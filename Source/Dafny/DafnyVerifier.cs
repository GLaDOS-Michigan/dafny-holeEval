//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.IO;
using System.Collections.Generic;
using System.Collections.Concurrent;
using System.Diagnostics.Contracts;
using System.Diagnostics;
using System.Reflection;
using System.Linq;
using Microsoft.Boogie;
using System.Threading;
using System.Threading.Tasks;
using System.Threading.Tasks.Dataflow;
using Grpc.Core;
using Google.Protobuf;

namespace Microsoft.Dafny {

  public class DafnyVerifierClient {
    private const int MaxDepth = 100;
    private int ConcurrentConsumerCount;

    private List<Channel> channelsList = new List<Channel>();
    private int sentRequests;
    private List<string> ServerIpPortList = new List<string>();
    private List<DafnyVerifierService.DafnyVerifierServiceClient> serversList =
      new List<DafnyVerifierService.DafnyVerifierServiceClient>();
    private List<TmpFolder> baseFoldersPath = new List<TmpFolder>();
    private List<List<TmpFolder>> temporaryFoldersList = new List<List<TmpFolder>>();
    private List<AsyncUnaryCall<Empty>> outstandingCleanupTasks = new List<AsyncUnaryCall<Empty>>();
    private List<Queue<IMessage>> tasksQueuePerDepth = new List<Queue<IMessage>>();
    // private ConcurrentQueue<CloneAndVerifyRequest> workerThreadTaskQueue = new ConcurrentQueue<CloneAndVerifyRequest>();
    private BufferBlock<IMessage> tasksBuffer;
    private bool freshTasksBuffer = false;
    private List<Task<int>> consumerTasks = new List<Task<int>>();
    private List<int> taskFinishedPerConsumer = new List<int>();
    private string OutputPrefix;
    public Func<int, bool> OutputProcessorFunc;
    private Random rand = new Random();

    public class Change
    {
      public IToken StartTok;
      public IToken EndTok;
      public string Replacement;
      public string StartString;
      public string FileName
      {
        get { return StartTok.filename; }
      }
      public Change(IToken startTok, IToken endTok, string replacement, string startString)
      {
        this.StartTok = startTok;
        this.EndTok = endTok;
        this.Replacement = replacement;
        this.StartString = startString;
      }
      public string ToJsonString() {
        var str = $"{{\"StartTok\":{{\"line\":{StartTok.line},\"col\":{StartTok.col}}}";
        str += $",\"EndTok\":{{\"line\":{EndTok.line},\"col\":{EndTok.col}}}";
        str += $",\"Replacement\":\"{Replacement}\"}}";
        return str;
      }
    }

    public static bool AddFileToChangeList(ref Dictionary<string, List<Change>> changeList, Change change) {
      if (!changeList.ContainsKey(change.FileName)) {
        changeList[change.FileName] = new List<Change>();
      }
      for (int i = 0; i < changeList[change.FileName].Count; i++) {
        if (changeList[change.FileName][i].StartTok.line <= change.StartTok.line && 
            change.EndTok.line <= changeList[change.FileName][i].EndTok.line) {
              return false;
            }
      }
      int index;
      for (index = 0; index < changeList[change.FileName].Count; index++) {
        if (change.StartTok.line > changeList[change.FileName][index].EndTok.line) {
          break;
        }
      }
      // TODO(armin): check if the changes are exclusive
      changeList[change.FileName].Insert(index, change);
      return true;
    }

    public DafnyVerifierClient(string serverIpPortFileName, string outputPrefix, Func<int, bool> outputProcessorFunc = null) {
      sentRequests = 0;
      OutputPrefix = outputPrefix;
      OutputProcessorFunc = outputProcessorFunc;
      sw = Stopwatch.StartNew();

      foreach (string line in System.IO.File.ReadLines(serverIpPortFileName)) {
        ServerIpPortList.Add(line);
        channelsList.Add(new Channel(line, ChannelCredentials.Insecure));
        serversList.Add(new DafnyVerifierService.DafnyVerifierServiceClient(
          channelsList[channelsList.Count - 1]));
        baseFoldersPath.Add(new TmpFolder());
        temporaryFoldersList.Add(new List<TmpFolder>());
      }
      Parallel.For(0, serversList.Count,
        index => {
          CreateDir createDir = new CreateDir();
          createDir.Owner = "arminvak";
          baseFoldersPath[index] = serversList[index].CreateTmpFolder(createDir);
        }
      );
      for (int i = 0; i < serversList.Count; i++) {
        temporaryFoldersList[i].Add(baseFoldersPath[i]);
      }
      for (int i = 0; i < MaxDepth; i++) {
        tasksQueuePerDepth.Add(new Queue<IMessage>());
      }
      
      // assuming each server has 40 cores. making double of that consumers
      ConcurrentConsumerCount = serversList.Count * 2 * 40;
      RestartConsumers();
    }
    public void RestartConsumers() {
      tasksBuffer = new BufferBlock<IMessage>();
      freshTasksBuffer = true;
      consumerTasks.Clear();
      // setting up consumers
      for (int i = 0; i < ConcurrentConsumerCount; i++) {
        consumerTasks.Add(ProcessRequestAsync(tasksBuffer));
      }
    }
    public Stopwatch sw;
    public ConcurrentDictionary<IMessage, IMessage> dafnyOutput = new ConcurrentDictionary<IMessage, IMessage>();
    public Dictionary<int, IMessage> requestsList = new Dictionary<int, IMessage>();
    public Dictionary<IMessage, Expression> requestToExpr = new Dictionary<IMessage, Expression>();
    public Dictionary<IMessage, List<ProofEvaluator.ExprStmtUnion>> requestToStmtExprList = new Dictionary<IMessage, List<ProofEvaluator.ExprStmtUnion>>();
    public Dictionary<IMessage, List<Expression>> requestToExprList = new Dictionary<IMessage, List<Expression>>();
    // requestToCall for clone and verify requests
    public ConcurrentDictionary<IMessage, AsyncUnaryCall<VerificationResponseList>> CAVRequestToCall =
      new ConcurrentDictionary<IMessage, AsyncUnaryCall<VerificationResponseList>>();
    // requestToCall for verification requests
    public ConcurrentDictionary<IMessage, AsyncUnaryCall<VerificationResponse>> VRequestToCall =
      new ConcurrentDictionary<IMessage, AsyncUnaryCall<VerificationResponse>>();
    // requestToCall for two stage verification requests
    public ConcurrentDictionary<IMessage, AsyncUnaryCall<VerificationResponseList>> TSRequestToCall =
      new ConcurrentDictionary<IMessage, AsyncUnaryCall<VerificationResponseList>>();
    public Dictionary<IMessage, int> requestToCnt = new Dictionary<IMessage, int>();
    public Dictionary<IMessage, int> requestToAvailableExprAIndex = new Dictionary<IMessage, int>();
    public Dictionary<IMessage, int> requestToAvailableExprBIndex = new Dictionary<IMessage, int>();
    public Dictionary<IMessage, int> requestToPostConditionPosition = new Dictionary<IMessage, int>();
    public Dictionary<IMessage, int> requestToLemmaStartPosition = new Dictionary<IMessage, int>();

    public List<List<VerificationRequest>> EnvironmentSetupTasks = new List<List<VerificationRequest>>();
    public List<List<VerificationRequest>> EnvironmentVerificationTasks = new List<List<VerificationRequest>>();

    public void InitializeBaseFoldersInRemoteServers(Program program, string commonPrefix) {
      Parallel.For(0, serversList.Count, new ParallelOptions { MaxDegreeOfParallelism = -1 },
        index => {
          var ipPort = ServerIpPortList[index];
          var ip = ipPort.Split(':')[0];

          string arguments = $"-az --rsh=\" ssh -o StrictHostKeyChecking=no\" --include '*/' --include '*\\.dfy' --exclude '*' {commonPrefix}/ arminvak@{ip}:{baseFoldersPath[index].Path}/";
          ProcessStartInfo startInfo = new ProcessStartInfo() { FileName = "/usr/bin/rsync", Arguments = arguments, };
          Process proc = new Process() { StartInfo = startInfo, };
          proc.Start();
          proc.WaitForExit();
          if (proc.ExitCode != 0) {
            Console.WriteLine($"Unsuccessful rsync for node{index} with ip:{ip}: Confirm connection between nodes");
            System.Environment.Exit(-1);
          }
        }
      );
      // var filesList = new List<string>();
      // foreach (var file in program.DefaultModuleDef.Includes) {
      //   filesList.Add(file.CanonicalPath);
      // }
    }

    public int CreateEnvironment(IncludeParser includeParser, Dictionary<string, List<Change>> changeList) {
      var env = new List<VerificationRequest>();
      foreach (var fileChangesTuple in changeList) {
        var code = File.ReadAllLines(fileChangesTuple.Key);
        foreach (var change in fileChangesTuple.Value) {
          var startTokLine = change.StartTok.line;
          var startTokCol = change.StartTok.col;
          startTokLine--;
          startTokCol--;
          var endTokLine = change.EndTok.line;
          var endTokCol = change.EndTok.col;
          endTokLine--;
          endTokCol--;
          if (change.StartString != "") {
            while (startTokLine >= 0) {
              var index = code[startTokLine].LastIndexOf(change.StartString, startTokCol);
              if (index != -1) {
                startTokCol = index;
                break;
              }
              startTokLine--;
              startTokCol = code[startTokLine].Length;
            }
            Contract.Assert(startTokLine >= 0);
          }
          code[startTokLine] = code[startTokLine].Substring(0, startTokCol) + change.Replacement.Replace("\n", " ");
          for (int i = startTokLine + 1; i < endTokLine; i++) {
            code[i] = "";
          }
          if (startTokLine != endTokLine && code[endTokLine].Length != 0) {
            code[endTokLine] = code[endTokLine].Substring(endTokCol + 1);
          }
        }
        VerificationRequest request = new VerificationRequest();
        request.Code = String.Join('\n', code);
        request.Path = includeParser.Normalized(fileChangesTuple.Key);
        request.Timeout = "10s";
        env.Add(request);
      }
      EnvironmentSetupTasks.Add(env);
      EnvironmentVerificationTasks.Add(new List<VerificationRequest>());
      return EnvironmentSetupTasks.Count - 1;
    }

    public void AddVerificationRequestToEnvironment(int envId, string code, string filename, List<string> args, string timeout = "1h") {
      Contract.Assert(envId >= 0);
      Contract.Assert(envId < EnvironmentVerificationTasks.Count);
      VerificationRequest request = new VerificationRequest();
      request.Code = code;
      request.Path = filename;
      request.Timeout = timeout;
      foreach (var arg in args) {
        request.Arguments.Add(arg);
      }
      EnvironmentVerificationTasks[envId].Add(request);
    }

    public void ResetVerificationTasksInEnvironment(int envId) {
      Contract.Assert(envId >= 0);
      Contract.Assert(envId < EnvironmentVerificationTasks.Count);
      EnvironmentVerificationTasks[envId].Clear();
    }

    public async Task<bool> RunVerificationRequestsStartingFromEnvironment(int envId, bool runExclusive) {
      for(int cnt = envId; cnt < EnvironmentSetupTasks.Count; cnt++) {
        TwoStageRequest request = new TwoStageRequest();
        var serverId = cnt % serversList.Count;
        request.DirectoryPath = baseFoldersPath[serverId].Path;
        request.RunExclusive = runExclusive;
        foreach (var req in EnvironmentSetupTasks[cnt]) {
          request.FirstStageRequestsList.Add(req);
        }
        foreach (var req in EnvironmentVerificationTasks[cnt]) {
          request.SecondStageRequestsList.Add(req);
        }
        Contract.Assert(!requestsList.ContainsKey(cnt));
        requestsList.Add(cnt, request);
        tasksQueuePerDepth[0].Enqueue(request);
        requestToCnt[request] = cnt;
        dafnyOutput[request] = new VerificationResponseList();
      }
      if (!freshTasksBuffer) {
        RestartConsumers();
      }
      var result = await startProofTasksAccordingToPriority();
      return result;
    }

    public TmpFolder DuplicateAllFiles(int cnt, string changingFilePath) {
      var serverId = cnt % serversList.Count;
      TmpFolder duplicateFileRequest = new TmpFolder();
      duplicateFileRequest.Path = baseFoldersPath[serverId].Path;
      duplicateFileRequest.ModifyingFile = changingFilePath;
      duplicateFileRequest.Owner = "arminvak";
      TmpFolder targetFolder = serversList[serverId].DuplicateFolder(duplicateFileRequest);
      temporaryFoldersList[serverId].Add(targetFolder);
      return targetFolder;
    }

    public static Result IsCorrectOutputForValidityCheck(string output, string expectedOutput, string expectedInconclusiveOutputStart) {
      if (output.EndsWith("1 error\n")) {
        var outputList = output.Split('\n');
        for (int i = 1; i <= 7; i++) {
          if ((outputList.Length >= i) && (outputList[outputList.Length - i] == expectedOutput)) {
            return Result.CorrectProof;
          }
        }
        return Result.IncorrectProof;
      } else if (output.EndsWith("1 inconclusive\n")) {
        var outputList = output.Split('\n');
        return ((outputList.Length >= 4) && outputList[outputList.Length - 4].StartsWith(expectedInconclusiveOutputStart)) ? Result.CorrectProofByTimeout : Result.IncorrectProof;
      } else {
        return Result.IncorrectProof;
      }
    }

    public static Result IsCorrectOutputForNoErrors(string output) {
      if (output.EndsWith(" 0 errors\n")) {
        return Result.CorrectProof;
      } else {
        return Result.IncorrectProof;
      }
    }

    public enum ImportType {
      NoImport = 0,
      CompleteImport = 1,
      SpecifiedImport = 2
    }

    public static Tuple<ImportType, AliasModuleDecl> GetImportType(string name, ModuleDefinition moduleDef) {
      if (moduleDef.FullDafnyName == name) {
        return new Tuple<ImportType, AliasModuleDecl>(ImportType.CompleteImport, null);
      }
      foreach (var topLevelDecl in moduleDef.TopLevelDecls) {
        if (topLevelDecl is AliasModuleDecl) {
          var aliasModuleDecl = topLevelDecl as AliasModuleDecl;
          if (aliasModuleDecl.Name == name) {
            if (aliasModuleDecl.Exports.Count == 0) {
              return new Tuple<ImportType, AliasModuleDecl>(ImportType.CompleteImport, null);
            }
            else {
              return new Tuple<ImportType, AliasModuleDecl>(ImportType.SpecifiedImport, aliasModuleDecl);
            }
          }
        }
      }
      return new Tuple<ImportType, AliasModuleDecl>(ImportType.NoImport, null);
    }

    public static IToken GetFirstToken(Expression expr) {
      if (expr is ApplySuffix) {
        return GetFirstToken((expr as ApplySuffix).Lhs);
      }
      else if (expr is ComprehensionExpr) {
        return (expr as ComprehensionExpr).BodyStartTok;
      } else if (expr is StmtExpr) {
        return (expr as StmtExpr).S.Tok;
      } else if (expr is ITEExpr) {
        return expr.tok;
      } else if (expr is MatchExpr) {
        // cannot find the last bracelet. not included in the AST
        return null;
      } else if (expr is IdentifierExpr) {
        return expr.tok;
      } else if (expr is UnaryOpExpr) {
        return (expr as UnaryExpr).tok;
      } else if (expr is BinaryExpr) {
        return GetFirstToken((expr as BinaryExpr).E0);
      } else if (expr is LiteralExpr) {
        return expr.tok;
      } else if (expr is ChainingExpression) {
        var chainExpr = expr as ChainingExpression;
        return GetFirstToken(chainExpr.Operands[0]);
      } else if (expr is NameSegment) {
        return expr.tok;
      } else if (expr is ExprDotName) {
        return GetFirstToken((expr as ExprDotName).Lhs);
      } else if (expr is LetExpr) {
        return expr.tok;
      } else if (expr is ParensExpression) {
        return expr.tok;
      } else {
        Console.WriteLine($"do not support GetFirstToken for {Printer.ExprToString(expr)} of type {expr.GetType()}");
        return null;
        // throw new NotImplementedException($"do not support GetFirstToken for {Printer.ExprToString(expr)} of type {expr.GetType()}");
      }
    }

    public static IToken GetLastToken(Expression expr) {
      if (expr is ApplySuffix) {
        return (expr as ApplySuffix).CloseParanthesisToken;
      } else if (expr is ComprehensionExpr) {
        return (expr as ComprehensionExpr).BodyEndTok;
      } else if (expr is StmtExpr) {
        return GetLastToken((expr as StmtExpr).E);
      } else if (expr is ITEExpr) {
        return GetLastToken((expr as ITEExpr).Els);
      } else if (expr is MatchExpr) {
        // cannot find the last bracelet. not included in the AST
        return null;
      } else if (expr is IdentifierExpr) {
        return expr.tok;
      } else if (expr is UnaryExpr) {
        // cannot find the last bracelet. not included in the AST
        return null;
      } else if (expr is BinaryExpr) {
        return GetLastToken((expr as BinaryExpr).E1);
      } else if (expr is LiteralExpr) {
        return expr.tok;
      } else if (expr is ChainingExpression) {
        var chainExpr = expr as ChainingExpression;
        return GetLastToken(chainExpr.Operands[chainExpr.Operands.Count - 1]);
      } else if (expr is NameSegment) {
        return expr.tok;
      } else if (expr is ExprDotName) {
        return expr.tok;
      } else if (expr is LetExpr) {
        return GetLastToken((expr as LetExpr).Body);
      } else if (expr is ParensExpression) {
        return (expr as ParensExpression).CloseParenthesisTok;
      } else {
        Console.WriteLine($"do not support GetLastToken for {Printer.ExprToString(expr)} of type {expr.GetType()}");
        return null;
      }
    }

    public class ProofFailResult {
      public string FuncBoogieName;
      public int Line;
      public int Column;

      public ProofFailResult(string funcBoogieName, int line, int column) {
        this.FuncBoogieName = funcBoogieName;
        this.Line = line;
        this.Column = column;
      }
    }

    public static List<ProofFailResult> GetFailingFunctionResults(string filename, string output) {
      List<ProofFailResult> res = new List<ProofFailResult>();
      if (!output.EndsWith(" 0 errors\n")) {
        var outputList = output.Split("\nVerifying ").ToList();
        if (outputList[outputList.Count - 1].LastIndexOf("\nDafny program verifier") != -1) {
          // Console.WriteLine($"do not support parsing: {outputList[outputList.Count - 1]}");
          // Console.WriteLine("will skip this function");
          // return null;
          outputList.Add(outputList[outputList.Count - 1].Substring(outputList[outputList.Count - 1].LastIndexOf("\nDafny program verifier")));
          outputList[outputList.Count - 2] = outputList[outputList.Count - 2].Substring(0, outputList[outputList.Count - 2].LastIndexOf("\nDafny program verifier"));
        }
        for (int i = 1; i < outputList.Count; i++) {
          if (outputList[i].EndsWith("verified\n")) {
            continue;
          }
          else {
            var funcBoogieName = outputList[i].Substring(0, outputList[i].IndexOf(' '));
            var errorsList = outputList[i].Split(filename);
            for (int j = 1; j < errorsList.Length; j++) {
              var error = errorsList[j];
              if (error.Substring(error.IndexOf(')')).StartsWith("): Error") ||
                  error.Substring(error.IndexOf(')')).StartsWith("): Verification out of resource") ||
                  error.Substring(error.IndexOf(')')).StartsWith("): Verification inconclusive"))
              {
                var lineColStrList = error.Substring(1, error.IndexOf(')') - 1).Split(',');
                var line = Int32.Parse(lineColStrList[0]);
                var col = Int32.Parse(lineColStrList[1]);
                res.Add(new ProofFailResult(funcBoogieName, line, col));
              }
            }
          }
        }
      }
      return res;
    }

    public void Cleanup() {
      for (int serverId = 0; serverId < temporaryFoldersList.Count; serverId++) {
        for (int i = 0; i < temporaryFoldersList[serverId].Count; i++) {
          AsyncUnaryCall<Empty> task = serversList[serverId].RemoveFolderAsync(
            temporaryFoldersList[serverId][i],
            deadline: DateTime.UtcNow.AddMinutes(30));
          outstandingCleanupTasks.Add(task);
        }
      }
      temporaryFoldersList.Clear();
    }

    public async Task<bool> FinalizeCleanup() {
      for (int i = 0; i < outstandingCleanupTasks.Count; i++) {
        Empty response = await outstandingCleanupTasks[i];
      }
      return true;
    }

    public async Task<bool> startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs() {
      // await Parallel.ForEachAsync(requestsList.Values.SelectMany(x => x).ToList(),
      await Parallel.ForEachAsync(requestsList.Values,
        async (request, tmp) => {
        start:
          try {
            if (request is VerificationRequest) {
              VerificationResponse response = await VRequestToCall[request];
              dafnyOutput[request] = response;  
            }
            else {
              VerificationResponseList response = await CAVRequestToCall[request];
              dafnyOutput[request] = response;
            }
          } catch (RpcException ex) {
            Console.WriteLine($"{sw.ElapsedMilliseconds / 1000}:: Restarting task #{requestToCnt[request]} {ex.Message}");
            RestartTask(request);
            goto start;
          }
        });
      return true;
    }

    // public void CheckIfCorrectAnswer(IMessage request, IMessage response) {
    //   // var output = response.Response.ToStringUtf8();
    //   if (request is CloneAndVerifyRequest) {
    //     var responseList = response as VerificationResponseList;
    //     for (int i = 0; i < responseList.ResponseList.Count; i++) {
    //       var output = responseList.ResponseList[i].Response.ToStringUtf8();
    //       if (output.EndsWith("0 errors\n")) {
    //         if (output.EndsWith(" 0 verified, 0 errors\n")) {
    //           throw new NotSupportedException("grpc server didn't prove anything. check /proc:");
    //         }
    //         if (requestToCnt[request] == 0) {
    //           Console.WriteLine($"{sw.ElapsedMilliseconds / 1000}:: proof pass without any change, not executing other verification requests");
    //           IList<IMessage> items = new List<IMessage>();
    //           tasksBuffer.TryReceiveAll(out items);
    //         }
    //         var str = $"{sw.ElapsedMilliseconds / 1000}:: correct answer #{requestToCnt[request]}: ";
    //         var sep = "";
    //         foreach (var stmtExpr in requestToStmtExprList[request]) {
    //           if (stmtExpr.Expr != null) {
    //             str += ($"{sep}{Printer.ExprToString(stmtExpr.Expr)}");
    //           } else {
    //             str += ($"{sep}{Printer.StatementToString(stmtExpr.Stmt)}");
    //           }
    //           sep = ", ";
    //         }
    //         Console.WriteLine(str);
    //       }
    //     }
    //   }
    //   else if (request is VerificationRequest) {
    //     // In this case, all verification requests should be considered to determine
    //     // the correntness of an expression. So, we do nothing here.
    //   }
    // }

    public async Task<int> ProcessRequestAsync(IReceivableSourceBlock<IMessage> source) {
      int tasksProcessed = 0;
      int retries = 0;
      while (await source.OutputAvailableAsync()) {
        if (source.TryReceive(out IMessage request)) {
          start:
          try {
            string output = "";
            if (request is VerificationRequest) {
              if (!VRequestToCall.ContainsKey(request)) {
                RestartTask(request);
              }
              if (requestToCnt[request] % 100 == 0) {
                Console.WriteLine($"calling await for #{requestToCnt[request]}");
              }
              VerificationResponse response = await VRequestToCall[request];
              if (requestToCnt[request] % 100 == 0) {
                Console.WriteLine($"finished await for #{requestToCnt[request]}");
              }
              if (DafnyOptions.O.HoleEvaluatorDumpOutput) {
                output = response.ToString();
                await File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{requestToCnt[request]}_0.txt",
                  request.ToString());
                await File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{OutputPrefix}_{requestToCnt[request]}_0.txt",
                  (requestToExpr.ContainsKey(request) ? "// " + Printer.ExprToString(requestToExpr[request]) + "\n" : "") +
                  (requestToCnt.ContainsKey(request) ? "// " + requestToCnt[request] + "\n" : "") + output + "\n");
              }
              dafnyOutput[request] = response;
              if (OutputProcessorFunc != null) {
                OutputProcessorFunc(requestToCnt[request]);
              }
            }
            else if (request is CloneAndVerifyRequest) {
              if (!CAVRequestToCall.ContainsKey(request)) {
                RestartTask(request);
              }
              // Console.WriteLine($"calling await for #{requestToCnt[request]}");
              VerificationResponseList response = await CAVRequestToCall[request];
              // Console.WriteLine($"finished await for #{requestToCnt[request]}");
              if (DafnyOptions.O.HoleEvaluatorDumpOutput) {
                output = $"{response.ExecutionTimeInMs.ToString()}\n";
                for (int i = 0; i < response.ResponseList.Count; i++) {
                  output = output + $"{i}:\t{response.ResponseList[i].Response.ToStringUtf8()}\n";
                }
                await File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{requestToCnt[request]}_0.txt",
                request.ToString());
                await File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{OutputPrefix}_{requestToCnt[request]}_0.txt",
                  (requestToExpr.ContainsKey(request) ? "// " + Printer.ExprToString(requestToExpr[request]) + "\n" : "") +
                  (requestToCnt.ContainsKey(request) ? "// " + requestToCnt[request] + "\n" : "") + output + "\n");
              }
              dafnyOutput[request] = response;
              if (OutputProcessorFunc != null) {
                OutputProcessorFunc(requestToCnt[request]);
              }
            }
            else if (request is TwoStageRequest) {
              if (!TSRequestToCall.ContainsKey(request)) {
                RestartTask(request);
              }
              // Console.WriteLine($"calling await for #{requestToCnt[request]}");
              VerificationResponseList response = await TSRequestToCall[request];
              // Console.WriteLine($"finished await for #{requestToCnt[request]}");
              if (DafnyOptions.O.HoleEvaluatorDumpOutput) {
                output = $"{response.ExecutionTimeInMs.ToString()}\n";
                for (int i = 0; i < response.ResponseList.Count; i++) {
                  output = output + $"{i}:\t{response.ResponseList[i].Response.ToStringUtf8()}\n";
                }
                await File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{requestToCnt[request]}_0.txt",
                request.ToString());
                await File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{OutputPrefix}_{requestToCnt[request]}_0.txt",
                  (requestToExpr.ContainsKey(request) ? "// " + Printer.ExprToString(requestToExpr[request]) + "\n" : "") +
                  (requestToCnt.ContainsKey(request) ? "// " + requestToCnt[request] + "\n" : "") + output + "\n");
              }
              dafnyOutput[request] = response;
              if (OutputProcessorFunc != null) {
                OutputProcessorFunc(requestToCnt[request]);
              }
            }
            else {
              throw new NotImplementedException();
            }

            // Console.WriteLine($"finish executing {requestToCnt[request]}");
          } catch (RpcException ex) {
            Console.WriteLine($"{sw.ElapsedMilliseconds / 1000}:: Restarting task #{requestToCnt[request]} {ex.Message}");
            if (retries < 5) {
              RestartTask(request);
              retries++;
              goto start;
            }
          }
          tasksProcessed++;
        }
      }
      return tasksProcessed;
    }

    public async Task<bool> startProofTasksAccordingToPriority() {
      for (int i = 0; i < MaxDepth; i++) {
        // Console.WriteLine($"depth size = {tasksQueuePerDepth[i].Count}");
        foreach (var request in tasksQueuePerDepth[i]) {
          tasksBuffer.Post(request);
        }
        tasksQueuePerDepth[i].Clear();
      }
      tasksBuffer.Complete();

      // waiting on consumers
      for (int i = 0; i < ConcurrentConsumerCount; i++) {
        taskFinishedPerConsumer.Add(await consumerTasks[i]);
      }
      freshTasksBuffer = false;
      // for (int i = 0; i < ConcurrentConsumerCount; i++) {
      //   Console.WriteLine($"Consumer #{i} finished {taskFinishedPerConsumer[i]} tasks");
      // }
      return true;
    }


    private void RestartTask(IMessage request) {
      // var prevTask = requestToCall[request];
      var serverId = requestToCnt[request] % serversList.Count;
      if (request is CloneAndVerifyRequest) {
        AsyncUnaryCall<VerificationResponseList> task = serversList[serverId].CloneAndVerifyAsync(
          request as CloneAndVerifyRequest,
          deadline: DateTime.UtcNow.AddMinutes(30000));
        CAVRequestToCall[request] = task;
      }
      else if (request is VerificationRequest) {
        AsyncUnaryCall<VerificationResponse> task = serversList[serverId].VerifyAsync(
          request as VerificationRequest,
          deadline: DateTime.UtcNow.AddMinutes(30000));
        VRequestToCall[request] = task;
      }
      else if (request is TwoStageRequest) {
        AsyncUnaryCall<VerificationResponseList> task = serversList[serverId].TwoStageVerifyAsync(
          request as TwoStageRequest,
          deadline: DateTime.UtcNow.AddMinutes(30000));
        TSRequestToCall[request] = task;
      }
      else {
        throw new NotSupportedException($"invalid request type : {request.ToString()}");
      }
    }

    public VerificationRequest GetFileRewriteRequest(string code, ExpressionFinder.ExpressionDepth exprDepth,
        int cnt, string remoteFilePath, string timeout = "1h") {
      VerificationRequest request = new VerificationRequest();
      request.Code = code;
      request.Path = remoteFilePath;
      request.Timeout = timeout;
      requestToExpr[request] = exprDepth.expr;
      requestToCnt[request] = cnt;
      return request;
    }

    public VerificationRequest GetVerificationRequest(string code, List<string> args, ExpressionFinder.ExpressionDepth exprDepth,
        int cnt, int postConditionPos, int lemmaStartPos, string remoteFilePath, string timeout = "1h") {
      VerificationRequest request = new VerificationRequest();
      request.Code = code;
      request.Path = remoteFilePath;
      request.Timeout = timeout;
      foreach (var arg in args) {
        request.Arguments.Add(arg);
      }
      requestToExpr[request] = exprDepth.expr;
      requestToCnt[request] = cnt;
      requestToPostConditionPosition[request] = postConditionPos;
      requestToLemmaStartPosition[request] = lemmaStartPos;
      return request;
    }

    public VerificationRequest GetVerificationRequestForProof(string code, List<string> args, List<ProofEvaluator.ExprStmtUnion> exprStmtList,
        int cnt, string filePath, string lemmaName, string timeout = "1h") {
      VerificationRequest request = new VerificationRequest();
      request.Code = code;
      request.Path = filePath;
      request.Timeout = timeout;
      foreach (var arg in args) {
        request.Arguments.Add(arg);
      }
      request.Arguments.Add($"/proc:*{lemmaName}*");
      requestToStmtExprList[request] = exprStmtList;
      requestToCnt[request] = cnt;
      return request;
    }

    public void runDafny(List<VerificationRequest> requests, ExpressionFinder.ExpressionDepth exprDepth,
        int cnt) {
      sentRequests++;
      // if (sentRequests == 500) {
      //   sentRequests = 0;
      //   ResetChannel();
      // }
      CloneAndVerifyRequest request = new CloneAndVerifyRequest();
      var serverId = cnt % serversList.Count;
      request.DirectoryPath = baseFoldersPath[serverId].Path;
      foreach (var req in requests) {
        request.RequestsList.Add(req);
      }
      Contract.Assert(!requestsList.ContainsKey(cnt));
      requestsList.Add(cnt, request);
      tasksQueuePerDepth[exprDepth.depth].Enqueue(request);
      requestToExpr[request] = exprDepth.expr;
      requestToCnt[request] = cnt;
      dafnyOutput[request] = new VerificationResponseList();
    }

    public void runDafny(List<VerificationRequest> requests, List<ProofEvaluator.ExprStmtUnion> exprStmtList,
        int cnt) {
      sentRequests++;
      // if (sentRequests == 500) {
      //   sentRequests = 0;
      //   ResetChannel();
      // }
      CloneAndVerifyRequest request = new CloneAndVerifyRequest();
      foreach (var req in requests) {
        request.RequestsList.Add(req);
      }
      Contract.Assert(!requestsList.ContainsKey(cnt));
      requestsList.Add(cnt, request);
      int maxDepth = 0;
      foreach (var stmtExpr in exprStmtList) {
        maxDepth = Math.Max(maxDepth, stmtExpr.Depth);
      }
      tasksQueuePerDepth[maxDepth].Enqueue(request);
      requestToStmtExprList[request] = exprStmtList;
      requestToCnt[request] = cnt;
      dafnyOutput[request] = new VerificationResponseList();
    }

    public void runDafny(string code, string args,
        int availableExprAIndex, int availableExprBIndex,
        int lemmaStartPos, int postConditionPos) {
      throw new NotImplementedException("Check compatibility with tasksQueuePerDepth");
      // CloneAndVerifyRequest request = new CloneAndVerifyRequest();
      // request.Code = code;
      // request.Arguments.Add(args);
      // var serverId = (availableExprAIndex * availableExprBIndex) % serversList.Count;
      // AsyncUnaryCall<VerificationResponseList> task = serversList[serverId].CloneAndVerifyAsync(request);
      // requestToCall[request] = task;
      // // if (!requestsList.ContainsKey(requestsList.Count)) {
      //   // requestsList.Add(requestsList.Count, new List<IMessage>());
      // // }
      // requestsList.Add(requestsList.Count, request);
      // requestToAvailableExprAIndex[request] = availableExprAIndex;
      // requestToAvailableExprBIndex[request] = availableExprBIndex;
      // requestToPostConditionPosition[request] = postConditionPos;
      // requestToLemmaStartPosition[request] = lemmaStartPos;
      // dafnyOutput[request] = new VerificationResponseList();
    }

  //   public void runDafnyProofCheck(string code, List<string> args, List<ProofEvaluator.ExprStmtUnion> exprStmtList, int cnt, string timeout = "1h") {
  //     sentRequests++;
  //     // if (sentRequests == 500) {
  //     //   sentRequests = 0;
  //     //   ResetChannel();
  //     // }
  //     CloneAndVerifyRequest request = new CloneAndVerifyRequest();
  //     request.Code = code;
  //     foreach (var arg in args) {
  //       request.Arguments.Add(arg);
  //     }
  //     request.Timeout = timeout;
  //     // if (!requestsList.ContainsKey(cnt)) {
  //     //   requestsList.Add(cnt, new List<IMessage>());
  //     // }
  //     requestsList.Add(cnt, request);
  //     requestToStmtExprList[request] = exprStmtList;
  //     requestToCnt[request] = cnt;
  //     dafnyOutput[request] = new VerificationResponse();
  //     if (cnt < consumerTasks.Count || (tasksBuffer.Count < consumerTasks.Count / 4)) {
  //       tasksBuffer.Post(request);
  //     }
  //     else {
  //       int maxDepth = 0;
  //       foreach (var stmtExpr in exprStmtList) {
  //         maxDepth = Math.Max(maxDepth, stmtExpr.Depth);
  //       }
  //       tasksQueuePerDepth[maxDepth].Enqueue(request);
  //     }
  //   }

  }
}
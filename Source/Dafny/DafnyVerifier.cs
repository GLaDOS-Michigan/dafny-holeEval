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
    private List<Task<int>> consumerTasks = new List<Task<int>>();
    private List<int> taskFinishedPerConsumer = new List<int>();
    private string OutputPrefix;
    private Random rand = new Random();
    public DafnyVerifierClient(string serverIpPortFileName, string outputPrefix) {
      sentRequests = 0;
      OutputPrefix = outputPrefix;

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
    public Dictionary<IMessage, int> requestToCnt = new Dictionary<IMessage, int>();
    public Dictionary<IMessage, int> requestToAvailableExprAIndex = new Dictionary<IMessage, int>();
    public Dictionary<IMessage, int> requestToAvailableExprBIndex = new Dictionary<IMessage, int>();
    public Dictionary<IMessage, int> requestToPostConditionPosition = new Dictionary<IMessage, int>();
    public Dictionary<IMessage, int> requestToLemmaStartPosition = new Dictionary<IMessage, int>();

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
      if (output.EndsWith("0 errors\n")) {
        return Result.CorrectProof;
      } else {
        return Result.IncorrectProof;
      }
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
              // CheckIfCorrectAnswer(request, response);
              dafnyOutput[request] = response;
            }
            else {
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
              // CheckIfCorrectAnswer(request, response);
              dafnyOutput[request] = response;
            }
            
            // Console.WriteLine($"finish executing {requestToCnt[request]}");
          } catch (RpcException ex) {
            Console.WriteLine($"{sw.ElapsedMilliseconds / 1000}:: Restarting task #{requestToCnt[request]} {ex.Message}");
            RestartTask(request);
            goto start;
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
        // Console.WriteLine($"sending request {(request as VerificationRequest).Path}");
        AsyncUnaryCall<VerificationResponse> task = serversList[serverId].VerifyAsync(
          request as VerificationRequest,
          deadline: DateTime.UtcNow.AddMinutes(30000));
        VRequestToCall[request] = task;
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
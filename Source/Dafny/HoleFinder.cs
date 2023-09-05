//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.Text;
using System.IO;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Diagnostics;
using System.Reflection;
using System.Linq;
using Microsoft.Boogie;
using System.Threading.Tasks;

namespace Microsoft.Dafny {

  public class HoleFinder {
    private string UnderscoreStr = "";
    private static Random random = new Random();
    public static string RandomString(int length) {
      const string chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
      return new string(Enumerable.Repeat(chars, length)
          .Select(s => s[random.Next(s.Length)]).ToArray());
    }
    private ExpressionFinder.ExpressionDepth constraintExpr = null;

    public DafnyVerifierClient dafnyVerifier;
    public DirectedCallGraph<Function, FunctionCallExpr, Expression> CG;
    private TasksList tasksList = null;
    private Dictionary<string, VerificationTaskArgs> tasksListDictionary = new Dictionary<string, VerificationTaskArgs>();
    private IncludeParser includeParser = null;
    private List<string> affectedFiles = new List<string>();
    public static int validityLemmaNameStartCol = 0;
    public static string lemmaForExprValidityString = "";
    private static int lemmaForExprValidityLineCount = 0;

    public HoleFinder() { }

    public void PrintWithFuncFalse(Program program, Function rootFunc, Function func, Expression constraintExpr) {
      string funcName;
      if (func.Name == "nullFunc")
        funcName = "NULL";
      else
        funcName = func.FullDafnyName;
      var backupFunc = new Function(func.tok, func.Name, func.HasStaticKeyword,
            func.IsGhost, func.TypeArgs, func.Formals,
            func.Result, func.ResultType, func.Req,
            func.Reads, func.Ens, func.Decreases,
            func.Body, func.ByMethodTok, func.ByMethodBody,
            func.Attributes, func.SignatureEllipsis);

      // List<List<Tuple<Function, FunctionCallExpr, Expression>>> AllPaths =
      //   new List<List<Tuple<Function, FunctionCallExpr, Expression>>>();
      // List<Tuple<Function, FunctionCallExpr, Expression>> CurrentPath =
      //   new List<Tuple<Function, FunctionCallExpr, Expression>>();
      // CurrentPath.Add(new Tuple<Function, FunctionCallExpr, Expression>(rootFunc, null, null));
      // HoleEvaluator.GetAllPaths(CG, rootFunc, func, AllPaths, CurrentPath);
      
      List<Tuple<Function, FunctionCallExpr, Expression>> p = new List<Tuple<Function, FunctionCallExpr, Expression>>();
      p.Add(new Tuple<Function, FunctionCallExpr, Expression>(rootFunc, null, null));
      string lemmaForExprValidityString = HoleEvaluator.GetValidityLemma(p, null, constraintExpr, -1);
      int lemmaForExprValidityPosition = 0;
      int lemmaForExprValidityStartPosition = 0;

      // var requestList = new List<VerificationRequest>();
      // var workingDir = $"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}/{funcName}_{cnt}";
      // if (tasksList == null) {
      //   throw new NotImplementedException();
      // }
      // else {
        
      // }

      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr, DafnyOptions.PrintModes.DllEmbed);
        pr.UniqueStringBeforeUnderscore = UnderscoreStr;
        if (funcName != "NULL") {
          func.Body = Expression.CreateBoolLiteral(func.Body.tok, false);
        }
        pr.PrintProgram(program, true);
        var code = $"// {funcName} set to false\n" + Printer.ToStringWithoutNewline(wr) + "\n\n";
        lemmaForExprValidityStartPosition = code.Count(f => f == '\n') + 1;
        code += lemmaForExprValidityString + "\n";
        lemmaForExprValidityPosition = code.Count(f => f == '\n');
        File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}holeFinder_{funcName}.dfy", code);
      }
      if (funcName != "NULL") {
        func.Body = backupFunc.Body;
      }
      string dafnyBinaryPath = System.Reflection.Assembly.GetEntryAssembly().Location;
      dafnyBinaryPath = dafnyBinaryPath.Substring(0, dafnyBinaryPath.Length - 4);
      string env = DafnyOptions.O.Environment.Remove(0, 22);
      var argList = env.Split(' ');
      string args = "";
      foreach (var arg in argList) {
        if (!arg.EndsWith(".dfy") && !arg.StartsWith("/hole") && arg.StartsWith("/")) {
          args += arg + " ";
        }
      }
      // holeFinderExecutor.createProcessWithOutput(dafnyBinaryPath,
      //     $"{args} {DafnyOptions.O.HoleEvaluatorWorkingDirectory}holeFinder_{funcName}.dfy /exitAfterFirstError",
      //     func, lemmaForExprValidityPosition, lemmaForExprValidityStartPosition, $"holeFinder_{funcName}");
    }

    public async Task<Function> FindHoleAfterRemoveFileLine(Program program, string removeFileLine, string baseFuncName) {
      var funcName = CodeModifier.Erase(program, removeFileLine);
      return await FindHole(program, funcName, baseFuncName);
    }
    public async Task<Function> FindHole(Program program, string funcName, string baseFuncName) {
      int timeLimitMultiplier = 2;
      int timeLimitMultiplierLength = 0;
      while (timeLimitMultiplier >= 1) {
        timeLimitMultiplierLength++;
        timeLimitMultiplier /= 10;
      }
      if (DafnyOptions.O.HoleEvaluatorServerIpPortList == null) {
        Console.WriteLine("ip port list is not given. Please specify with /holeEvalServerIpPortList");
        return null;
      }
      if (DafnyOptions.O.HoleEvaluatorCommands != null) {
        var input = File.ReadAllText(DafnyOptions.O.HoleEvaluatorCommands);
        tasksList = Google.Protobuf.JsonParser.Default.Parse<TasksList>(input);
        foreach (var task in tasksList.Tasks) {
          tasksListDictionary.Add(task.Path, task);
        }
      }
      validityLemmaNameStartCol = 30 + timeLimitMultiplierLength;
      dafnyVerifier = new DafnyVerifierClient(DafnyOptions.O.HoleEvaluatorServerIpPortList, $"output_{funcName}");
      UnderscoreStr = RandomString(8);
      dafnyVerifier.sw = Stopwatch.StartNew();
      Function baseFunc = HoleEvaluator.GetMember(program, baseFuncName) as Function;
      if (baseFunc == null) {
        Console.WriteLine($"couldn't find function {baseFuncName}. List of all functions:");
        foreach (var kvp in program.ModuleSigs) {
          foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
            Console.WriteLine(topLevelDecl.FullDafnyName);
          }
        }
        return null;
      }
      CG = HoleEvaluator.GetCallGraph(baseFunc);
      Function func = HoleEvaluator.GetMember(program, funcName) as Function;
      if (func == null) {
        Console.WriteLine($"couldn't find function {funcName}. List of all functions:");
        foreach (var kvp in program.ModuleSigs) {
          foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
            Console.WriteLine(topLevelDecl.FullDafnyName);
          }
        }
        return null;
      }
      List<List<Tuple<Function, FunctionCallExpr, Expression>>> Paths =
        new List<List<Tuple<Function, FunctionCallExpr, Expression>>>();
      List<Tuple<Function, FunctionCallExpr, Expression>> CurrentPath =
        new List<Tuple<Function, FunctionCallExpr, Expression>>();
      CurrentPath.Add(new Tuple<Function, FunctionCallExpr, Expression>(baseFunc, null, null));
      HoleEvaluator.GetAllPaths(CG, baseFunc, func, Paths, CurrentPath);
      if (Paths.Count == 0)
        Paths.Add(new List<Tuple<Function, FunctionCallExpr, Expression>>(CurrentPath));

      // calculate holeEvaluatorConstraint Invocation
      Function constraintFunc = null;
      if (DafnyOptions.O.HoleEvaluatorConstraint != null) {
        constraintFunc = HoleEvaluator.GetMember(program, DafnyOptions.O.HoleEvaluatorConstraint) as Function;
        if (constraintFunc == null) {
          Console.WriteLine($"constraint function {DafnyOptions.O.HoleEvaluatorConstraint} not found!");
          return null;
        }
      }
      constraintExpr = HoleEvaluator.GetConstraintExpr(program, baseFunc, constraintFunc);

      Function nullFunc = new Function(
        func.tok, "nullFunc", func.HasStaticKeyword, func.IsGhost,
        func.TypeArgs, func.Formals, func.Result, func.ResultType,
        func.Req, func.Reads, func.Ens, func.Decreases,
        func.Body, func.ByMethodTok, func.ByMethodBody,
        func.Attributes, func.SignatureEllipsis);
      PrintWithFuncFalse(program, func, nullFunc, constraintExpr.expr);
      foreach (var kvp in program.ModuleSigs) {
        foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
          if (topLevelDecl.Body != null && CG.AdjacencyWeightList.ContainsKey(topLevelDecl)) {
            Console.WriteLine(topLevelDecl.FullDafnyName);
            PrintWithFuncFalse(program, func, topLevelDecl, constraintExpr.expr);
          }
        }
      }
      // holeFinderExecutor.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs();

      // check if proof already goes through
      // var p = holeFinderExecutor.funcToProcess[nullFunc];
      // var output = holeFinderExecutor.dafnyOutput[p];
      // var fileName = holeFinderExecutor.inputFileName[p];
      // var position = holeFinderExecutor.processToPostConditionPosition[p];
      // var lemmaStartPosition = holeFinderExecutor.processToLemmaStartPosition[p];
      // var expectedOutput =
      //   $"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{fileName}.dfy({position},0): Error: A postcondition might not hold on this return path.";
      // var expectedInconclusiveOutputStart = 
      //   $"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{fileName}.dfy({lemmaStartPosition},{HoleEvaluator.validityLemmaNameStartCol}): Verification inconclusive";
      // Console.WriteLine(expectedInconclusiveOutputStart);
      // var nullChangeResult = DafnyExecutor.IsCorrectOutput(output, expectedOutput, expectedInconclusiveOutputStart);
      // if (nullChangeResult != Result.IncorrectProof) {
      //   Console.WriteLine($"{holeFinderExecutor.sw.ElapsedMilliseconds / 1000}:: proof already goes through! {nullChangeResult.ToString()}");
      //   return null;
      // }
      // if (dotGraphOutputPath == "")
      //   dotGraphOutputPath = $"./callGraph_{func.Name}.dot";
      // PrintCallGraphWithPotentialBugInfo(CG, dotGraphOutputPath);
      // Console.WriteLine($"{holeFinderExecutor.sw.ElapsedMilliseconds / 1000}:: finish");
      return null;
    }
  }
}
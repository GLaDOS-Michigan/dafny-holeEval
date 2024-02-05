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
    private DafnyVerifierClient dafnyVerifier = null;
    private IncludeParser includeParser = null;
    private List<string> affectedFiles = new List<string>();
    private TasksList tasksList = null;
    private Dictionary<string, VerificationTaskArgs> tasksListDictionary = new Dictionary<string, VerificationTaskArgs>();
    public Dictionary<string, ModuleDefinition> FileNameToModuleDict = new Dictionary<string, ModuleDefinition>();

    public DirectedCallGraph<Function, FunctionCallExpr, Expression> CG;
    public Dictionary<int, Dictionary<string, List<Change>>> EnvIdToChangeList = new Dictionary<int, Dictionary<string, List<Change>>>();
    private Change baseChange = null;

    Dictionary<int, List<DafnyVerifierClient.ProofFailResult>> FailingLemmas = null;

    public HoleFinder() { }

    public Dictionary<string, List<Change>> GetBaseChangeList() {
      Dictionary<string, List<Change>> res = new Dictionary<string, List<Change>>();
      if (baseChange != null) {
        res[baseChange.FileName] = new List<Change>();
        res[baseChange.FileName].Add(baseChange);
      }
      return res;
    }

    public static string CallGraphToGraphViz(DirectedCallGraph<Function, FunctionCallExpr, Expression> CG) {
      var str = "";
      string graphVizOutput = $"digraph \"call_graph\" {{\n";
      graphVizOutput += "  // The list of nodes\n";
      Dictionary<string, int> NameToIDDict = new Dictionary<string, int>();
      var cnt = 0;
      foreach (var func in CG.AdjacencyWeightList.Keys) {
        NameToIDDict[func.FullDafnyName] = cnt;
        cnt++;
      }
      foreach (var func in CG.AdjacencyWeightList.Keys) {
        graphVizOutput += $"  {NameToIDDict[func.FullDafnyName]} [label=\"{func.FullDafnyName}\"];\n";
      }
      graphVizOutput += "\n  // The list of edges:\n";
      foreach (var funcEdgesKV in CG.AdjacencyWeightList) {
        var func = funcEdgesKV.Key;
        foreach (var edge in funcEdgesKV.Value) {
          graphVizOutput += $"  {NameToIDDict[func.FullDafnyName]} -> {NameToIDDict[edge.Item1.FullDafnyName]};\n";
        }
      }
      graphVizOutput += "}\n";
      return graphVizOutput;
    }

    public IEnumerable<Expression> GetDifferentExprsPathConjuncts(Expression expr) {
      expr = Expression.StripParens(expr);
      if (expr is BinaryExpr binaryExpr) {
        switch (binaryExpr.Op) {
          case BinaryExpr.Opcode.And:
            foreach (var e in GetDifferentExprsPathConjuncts(binaryExpr.E0)) {
              yield return e;
            }
            foreach (var e in GetDifferentExprsPathConjuncts(binaryExpr.E1)) {
              yield return e;
            }
            yield break;
        }
      } else if (expr is UnaryOpExpr unaryExpr) {
        if (unaryExpr.Op == UnaryOpExpr.Opcode.Not) {
          foreach (var e in GetDifferentExprsPathDisjuncts(unaryExpr.E)) {
            yield return Expression.CreateNot(e.tok, e);
          }
          yield break;
        }
      }
      yield return expr;
    }

    public IEnumerable<Expression> GetDifferentExprsPathDisjuncts(Expression expr) {
      expr = Expression.StripParens(expr);
      if (expr is BinaryExpr binaryExpr) {
        switch(binaryExpr.Op) {
          case BinaryExpr.Opcode.And:
            foreach (var e0 in GetDifferentExprsPathDisjuncts(binaryExpr.E0)) {
              foreach (var e1 in GetDifferentExprsPathDisjuncts(binaryExpr.E1)) {
                yield return Expression.CreateAnd(e0, e1);
              }
            }
            yield break;
          case BinaryExpr.Opcode.Or:
            foreach (var e0 in GetDifferentExprsPathDisjuncts(binaryExpr.E0)) {
              yield return e0;
            }
            foreach (var e1 in GetDifferentExprsPathDisjuncts(binaryExpr.E1)) {
              yield return e1;
            }
            yield break;
          case BinaryExpr.Opcode.Imp:
            foreach (var e0 in GetDifferentExprsPathConjuncts(binaryExpr.E0)) {
              yield return Expression.CreateNot(e0.tok, e0);
            }
            foreach (var e1 in GetDifferentExprsPathDisjuncts(binaryExpr.E1)) {
              yield return e1;
            }
            yield break;
        }
      } else if (expr is UnaryOpExpr unaryExpr) {
        if (unaryExpr.Op == UnaryOpExpr.Opcode.Not) {
          foreach (var e in GetDifferentExprsPathConjuncts(unaryExpr.E)) {
            yield return Expression.CreateNot(e.tok, e);
          }
          yield break;
        }
      } else if (expr is ITEExpr iteExpr) {
        if (iteExpr.Els != null) {
          yield return Expression.CreateAnd(iteExpr.Test, iteExpr.Thn);
          yield return Expression.CreateAnd(Expression.CreateNot(iteExpr.Test.tok, iteExpr.Test), iteExpr.Thn);
          yield break;
        }
      } else if (expr is MatchExpr matchExpr) {
        Console.WriteLine($"matchExpr not handled in GetDifferentExprsPathDisjuncts: {Printer.ExprToString(matchExpr)}");
        yield return expr;
      } else if (expr is NestedMatchExpr nestedMatchExpr) {
        if (nestedMatchExpr.Source.Type.IsDatatype && nestedMatchExpr.Cases.Count > 1) {
          foreach (var c in nestedMatchExpr.Cases) {
            var e = new ExprDotName(nestedMatchExpr.Source.tok, nestedMatchExpr.Source, c.Pat.Tok.val + "?", null);
            yield return Expression.CreateAnd(e, c.Body);
          }
          yield break;
        }
      }
      yield return expr;
    }

    public static DirectedCallGraph<Function, FunctionCallExpr, Expression> GetCallGraph(Function baseFunc) {
      Contract.Requires(baseFunc != null);
      DirectedCallGraph<Function, FunctionCallExpr, Expression> G = new DirectedCallGraph<Function, FunctionCallExpr, Expression>();
      // Tuple of SubExpression that is going to be parsed, pre-condition to reach this SubExpression, containing Function
      Queue<Tuple<Expression, Expression, Function>> queue = new Queue<Tuple<Expression, Expression, Function>>();
      queue.Enqueue(new Tuple<Expression, Expression, Function>(baseFunc.Body, null, baseFunc));
      G.AddVertex(baseFunc);
      HashSet<string> seenFunctionCalls = new HashSet<string>();
      while (queue.Count > 0) {
        Tuple<Expression, Expression, Function> currExprCondParentTuple = queue.Dequeue();
        if (currExprCondParentTuple.Item1 == null) continue;
        // var l = GetConjunctsExprList(currExprCondParentTuple.Item1);
        // foreach (var e in l) {
        //   Console.WriteLine(Printer.ExprToString(e));
        // }
        if (currExprCondParentTuple.Item1 is FunctionCallExpr) {
          var funcCallCondAsString = $"{currExprCondParentTuple.Item3.Name} -> " +
                                     $"{(currExprCondParentTuple.Item1 as FunctionCallExpr).Function.Name} -> ";
          if (currExprCondParentTuple.Item2 != null) {
            funcCallCondAsString += $"{Printer.ExprToString(currExprCondParentTuple.Item2)}";
          } else {
            funcCallCondAsString += "NULL";
          }
          if (!seenFunctionCalls.Contains(funcCallCondAsString)) {
            seenFunctionCalls.Add(funcCallCondAsString);
            if (currExprCondParentTuple.Item3 != (currExprCondParentTuple.Item1 as FunctionCallExpr).Function) {
              queue.Enqueue(new Tuple<Expression, Expression, Function>(
                (currExprCondParentTuple.Item1 as FunctionCallExpr).Function.Body,
                null,
                (currExprCondParentTuple.Item1 as FunctionCallExpr).Function));
              G.AddVertex((currExprCondParentTuple.Item1 as FunctionCallExpr).Function);
              G.AddEdge(
                currExprCondParentTuple.Item3,
                (currExprCondParentTuple.Item1 as FunctionCallExpr).Function,
                currExprCondParentTuple.Item1 as FunctionCallExpr,
                currExprCondParentTuple.Item2);
              // Console.WriteLine("-------------------------------------");
              // keys.Add(Printer.ExprToString((currExprParentTuple.Item1 as FunctionCallExpr).Function.Body) + ":" + (currExprParentTuple.Item1 as FunctionCallExpr).Function.Body);
            }
          }
        }
        if (currExprCondParentTuple.Item1 is ITEExpr) {
          // Console.WriteLine($"ite expr here: {Printer.ExprToString(currExprCondParentTuple.Item1)}");
          var iteExpr = currExprCondParentTuple.Item1 as ITEExpr;

          // add Condition
          queue.Enqueue(new Tuple<Expression, Expression, Function>(
            iteExpr.Test, currExprCondParentTuple.Item2, currExprCondParentTuple.Item3));

          // add then path
          Expression thenCond;
          if (currExprCondParentTuple.Item2 != null && currExprCondParentTuple.Item2 is LetExpr) {
            var prevLet = currExprCondParentTuple.Item2 as LetExpr;
            thenCond = Expression.CreateLet(prevLet.tok, prevLet.LHSs, prevLet.RHSs, 
              Expression.CreateAnd(prevLet.Body, iteExpr.Test), prevLet.Exact);
          }
          else {
            thenCond = currExprCondParentTuple.Item2 != null ?
              Expression.CreateAnd(currExprCondParentTuple.Item2, iteExpr.Test) :
              iteExpr.Test;
          }
          queue.Enqueue(new Tuple<Expression, Expression, Function>(
            iteExpr.Thn, thenCond, currExprCondParentTuple.Item3));

          // add else path
          Expression elseCond;
          if (currExprCondParentTuple.Item2 != null && currExprCondParentTuple.Item2 is LetExpr) {
            var prevLet = currExprCondParentTuple.Item2 as LetExpr;
            elseCond = Expression.CreateLet(prevLet.tok, prevLet.LHSs, prevLet.RHSs, 
              Expression.CreateAnd(prevLet.Body, 
                Expression.CreateNot(iteExpr.Test.tok, iteExpr.Test)
              ), prevLet.Exact);
          }
          else {
            elseCond = currExprCondParentTuple.Item2 != null ?
              Expression.CreateAnd(currExprCondParentTuple.Item2,
                                   Expression.CreateNot(iteExpr.Test.tok, iteExpr.Test)) :
              Expression.CreateNot(iteExpr.Test.tok, iteExpr.Test);
          }
          queue.Enqueue(new Tuple<Expression, Expression, Function>(
            iteExpr.Els, elseCond, currExprCondParentTuple.Item3));

          G.AddVertex(currExprCondParentTuple.Item3);
        } else if (currExprCondParentTuple.Item1 is MatchExpr) {
          var matchExpr = currExprCondParentTuple.Item1 as MatchExpr;
          // add source
          queue.Enqueue(new Tuple<Expression, Expression, Function>(
            matchExpr.Source, currExprCondParentTuple.Item2, currExprCondParentTuple.Item3));

          // add cases
          // Console.WriteLine(Printer.ExprToString(matchExpr));
          foreach (var c in matchExpr.Cases) {
            // Console.WriteLine($"{c.Ctor} -> {c.Ctor.Name}");
            Expression cond;
            if (currExprCondParentTuple.Item2 != null && currExprCondParentTuple.Item2 is LetExpr) {
              var prevLet = currExprCondParentTuple.Item2 as LetExpr;
              cond = new LetExpr(prevLet.tok, prevLet.LHSs, prevLet.RHSs, 
                Expression.CreateAnd(prevLet.Body, new MemberSelectExpr(c.Ctor.tok, matchExpr.Source, c.Ctor.Name)), prevLet.Exact);
            }
            else {
              cond = currExprCondParentTuple.Item2 != null ?
                Expression.CreateAnd(currExprCondParentTuple.Item2, new MemberSelectExpr(c.Ctor.tok, matchExpr.Source, c.Ctor.Name)) :
                new MemberSelectExpr(c.Ctor.tok, matchExpr.Source, c.Ctor.Name + "?");
            }
            queue.Enqueue(new Tuple<Expression, Expression, Function>(
              c.Body, cond, currExprCondParentTuple.Item3));
          }
          G.AddVertex(currExprCondParentTuple.Item3);
          // Console.WriteLine("----------------------------------------------------------------");
        } else if (currExprCondParentTuple.Item1 is ExistsExpr) {
          var existsExpr = currExprCondParentTuple.Item1 as ExistsExpr;
          var lhss = new List<CasePattern<BoundVar>>();
          var rhss = new List<Expression>();
          foreach (var bv in existsExpr.BoundVars) {
            // lhss.Add(new CasePattern<BoundVar>(bv.Tok,
            //   new BoundVar(bv.Tok, currExprCondParentTuple.Item3.Name + "_" + bv.Name, bv.Type)));
            lhss.Add(new CasePattern<BoundVar>(bv.Tok,
              new BoundVar(bv.Tok, bv.Name, bv.Type)));
          }
          rhss.Add(existsExpr.Term);
          Expression prevCond;
          if (currExprCondParentTuple.Item2 != null && currExprCondParentTuple.Item2 is LetExpr) {
            var prevLet = currExprCondParentTuple.Item2 as LetExpr;
            prevCond = Expression.CreateLet(prevLet.tok, prevLet.LHSs, prevLet.RHSs, 
              Expression.CreateAnd(prevLet.Body, existsExpr), prevLet.Exact);
          }
          else {
            prevCond = currExprCondParentTuple.Item2 != null ?
              Expression.CreateAnd(currExprCondParentTuple.Item2, existsExpr) :
              existsExpr;
          }
          var cond = Expression.CreateAnd(prevCond, Expression.CreateLet(existsExpr.BodyStartTok, lhss, rhss,
            Expression.CreateBoolLiteral(existsExpr.BodyStartTok, true), false));

          queue.Enqueue(new Tuple<Expression, Expression, Function>(existsExpr.Term, cond, currExprCondParentTuple.Item3));
          G.AddVertex(currExprCondParentTuple.Item3);
        } else if (currExprCondParentTuple.Item1 is LetExpr) {
          var letExpr = currExprCondParentTuple.Item1 as LetExpr;
          var currLetExpr = letExpr;
          var lhss = new List<CasePattern<BoundVar>>();
          var rhss = new List<Expression>();
          while (true) {
            for (int i = 0; i < currLetExpr.LHSs.Count; i++) {
              var lhs = currLetExpr.LHSs[i];
              var rhs = currLetExpr.RHSs[i];
              // lhss.Add(new CasePattern<BoundVar>(bv.Tok,
              //   new BoundVar(bv.Tok, currExprCondParentTuple.Item3.Name + "_" + bv.Name, bv.Type)));
              lhss.Add(new CasePattern<BoundVar>(lhs.tok,
                new BoundVar(lhs.tok, lhs.Id, lhs.Expr.Type)));
              rhss.Add(rhs);
            }
            if (currLetExpr.Body is LetExpr) {
              currLetExpr = currLetExpr.Body as LetExpr;
            }
            else {
              break;
            }
          }
          // var cond = currExprCondParentTuple.Item2 != null ?
          //   Expression.CreateAnd(currExprCondParentTuple.Item2, letExpr) :
          //   letExpr;

          var cond = Expression.CreateLet(letExpr.Body.tok, lhss, rhss,
            Expression.CreateBoolLiteral(letExpr.BodyStartTok, true), letExpr.Exact);

          queue.Enqueue(new Tuple<Expression, Expression, Function>(letExpr.Body, cond, currExprCondParentTuple.Item3));
          G.AddVertex(currExprCondParentTuple.Item3);
        } else {
          foreach (var e in currExprCondParentTuple.Item1.SubExpressions) {
            // if (!keys.Contains(Printer.ExprToString(e) + ":" + e)) {
            // Console.WriteLine("Adding " + e + ": " + Printer.ExprToString(e));
            // if (e is MatchExpr) {
            //   // Console.WriteLine($"MatchExpr : {Printer.ExprToString(e)}");
            //   queue.Enqueue(new Tuple<Expression, Expression, Function>(e, e, currExprCondParentTuple.Item3));
            //   G.AddVertex(currExprCondParentTuple.Item3);
            // } else if (e is ITEExpr) {
            //   // Console.WriteLine($"ITEExpr : {Printer.ExprToString(e)}");
            //   queue.Enqueue(new Tuple<Expression, Expression, Function>(e, e, currExprCondParentTuple.Item3));
            //   G.AddVertex(currExprCondParentTuple.Item3);
            // } else {
            // Console.WriteLine($"else : {e} -> {Printer.ExprToString(e)}");
            queue.Enqueue(new Tuple<Expression, Expression, Function>(e, currExprCondParentTuple.Item2, currExprCondParentTuple.Item3));
            G.AddVertex(currExprCondParentTuple.Item3);
            // }
          }
        }
      }
      return G;
    }

    private string GetChangeListString(int index)
    {
      ChangeList cList = new ChangeList();
      foreach (var fileChangeKV in EnvIdToChangeList[index]) {
        foreach (var c in fileChangeKV.Value) {
          cList.Changes.Add(c);
        }
      }
      return Google.Protobuf.JsonFormatter.Default.Format(cList);
    }

    private string GetRequestString(int index)
    {
      var TSRequest = dafnyVerifier.requestsList[index] as TwoStageRequest;
      return TSRequest.ToString() + "\n";
    }

    private string GetResponseString(int index)
    {
      var TSRequest = dafnyVerifier.requestsList[index] as TwoStageRequest;
      var TSOutput = dafnyVerifier.dafnyOutput[TSRequest] as VerificationResponseList;
      var res = "";
      for (int i = 0; i < TSRequest.SecondStageRequestsList.Count; i++)
      {
        var request = TSRequest.SecondStageRequestsList[i];
        if (request.Arguments.Count == 0)
        {
          continue;
        }
        var output = TSOutput.ResponseList[i];
        var response = output.Response.ToStringUtf8();
        var filePath = output.FileName;
        res += $"{filePath} response:\n{response}\n\n";
      }
      return res;
    }

    private Dictionary<int, List<DafnyVerifierClient.ProofFailResult>> GetFailingProofs(int index)
    {
      Dictionary<int, List<DafnyVerifierClient.ProofFailResult>> result =
          new Dictionary<int, List<DafnyVerifierClient.ProofFailResult>>();
      var TSRequest = dafnyVerifier.requestsList[index] as TwoStageRequest;
      var TSOutput = dafnyVerifier.dafnyOutput[TSRequest] as VerificationResponseList;
      var execTime = TSOutput.ExecutionTimeInMs;
      for (int i = 0; i < TSRequest.SecondStageRequestsList.Count; i++)
      {
        var request = TSRequest.SecondStageRequestsList[i];
        if (request.Arguments.Count == 0)
        {
          continue;
        }
        var output = TSOutput.ResponseList[i];
        var response = output.Response.ToStringUtf8();
        var filePath = output.FileName;
        // if (DafnyOptions.O.HoleEvaluatorVerboseMode)
        // {
        //   Console.WriteLine($"{index} output for maintain lemma:\n{response}");
        // }
        Result res = DafnyVerifierClient.IsCorrectOutputForNoErrors(response);
        if (res != Result.CorrectProof)
        {
          result[i] = DafnyVerifierClient.GetFailingFunctionResults("", filePath, response);
        }
      }
      return result;
    }

    public async Task<Function> FindHoleAfterRemoveFileLine(Program program, Program unresolvedProgram, string removeFileLine, string baseFuncName) {
      var funcNameChangeTuple = CodeModifier.Erase(program, removeFileLine);
      baseChange = funcNameChangeTuple.Item2;
      return await FindHole(program, unresolvedProgram, funcNameChangeTuple.Item1, baseFuncName);
    }
    public async Task<Function> FindHole(Program program, Program unresolvedProgram, string funcName, string baseFuncName) {
      if (DafnyOptions.O.HoleEvaluatorCommands != null) {
        var input = File.ReadAllText(DafnyOptions.O.HoleEvaluatorCommands);
        tasksList = Google.Protobuf.JsonParser.Default.Parse<TasksList>(input);
        foreach (var task in tasksList.Tasks) {
          tasksListDictionary.Add(task.Path, task);
          }
      }
      dafnyVerifier = new DafnyVerifierClient(DafnyOptions.O.HoleEvaluatorServerIpPortList, "output_changeListEval", null);
      includeParser = new IncludeParser(program);
      dafnyVerifier.InitializeBaseFoldersInRemoteServers(program, includeParser.commonPrefix);

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

      foreach (var kvp in program.ModuleSigs)
      {
        if (kvp.Value.ModuleDef.tok.filename != null)
        {
          var filename = includeParser.Normalized(kvp.Value.ModuleDef.tok.filename);
          FileNameToModuleDict[filename] = kvp.Value.ModuleDef;
        }
      }

      if (DafnyOptions.O.HoleEvaluatorLogOutputs != "")
      {
        var outputDir = DafnyOptions.O.HoleEvaluatorLogOutputs;
        if (!Directory.Exists(outputDir))
        {
          Directory.CreateDirectory(outputDir);
        }
      }
      CG = GetCallGraph(baseFunc);
      var callGraphStr = CallGraphToGraphViz(CG);
      if (DafnyOptions.O.HoleEvaluatorLogOutputs != "")
      {
        File.WriteAllText($"{DafnyOptions.O.HoleEvaluatorLogOutputs}/callGraph.dot", callGraphStr);
      }
      // var currFunc = baseFunc;
      var startEnvId = 0;
      var endEnvId = -1;
      var baseFuncEnvId = 0;
      {
        // no change environment
        var changeList = GetBaseChangeList();
        baseFuncEnvId = dafnyVerifier.CreateEnvironment(includeParser, changeList);
        foreach (var task in tasksListDictionary)
        {
          OpaqueEvaluator.AddVerificationRequestPerCallable(baseFuncEnvId, task.Key, task.Value.Arguments.ToList(), dafnyVerifier, FileNameToModuleDict);
          // dafnyVerifier.AddVerificationRequestToEnvironment(envId, "", task.Key, task.Value.Arguments.ToList());
        }
        EnvIdToChangeList[baseFuncEnvId] = changeList;
        endEnvId = baseFuncEnvId;
        await dafnyVerifier.RunVerificationRequestsStartingFromEnvironment(startEnvId, false);
        if (DafnyOptions.O.HoleEvaluatorLogOutputs != "")
        {
          var outputDir = DafnyOptions.O.HoleEvaluatorLogOutputs;
          File.WriteAllText($"{outputDir}/change_{baseFuncEnvId}.txt", GetChangeListString(baseFuncEnvId));
          File.WriteAllText($"{outputDir}/request_{baseFuncEnvId}.txt", GetRequestString(baseFuncEnvId));
          File.WriteAllText($"{outputDir}/response_{baseFuncEnvId}.txt", GetResponseString(baseFuncEnvId));
        }
        FailingLemmas = GetFailingProofs(baseFuncEnvId);
        // Console.WriteLine(res.Count);
        startEnvId = endEnvId + 1;
      }
      HashSet<string> exploredFunctions = new HashSet<string>();
      Queue<Function> exploringFunctions = new Queue<Function>();
      exploringFunctions.Enqueue(baseFunc);
      exploredFunctions.Add(baseFunc.FullDafnyName);
      while (exploringFunctions.Count != 0) {
        var currFunc = exploringFunctions.Peek();
        exploringFunctions.Dequeue();
        foreach (var edge in CG.AdjacencyWeightList[currFunc]) {
          if (!exploredFunctions.Contains(edge.Item1.FullDafnyName)) {
            exploredFunctions.Add(edge.Item1.FullDafnyName);
            exploringFunctions.Enqueue(edge.Item1);
          }
        }
        if (currFunc.Body == null) {
          continue;
        }
        var pathsList = GetDifferentExprsPathDisjuncts(currFunc.Body).ToList();
        // if (pathsList.Count <= 1) {
        Console.WriteLine($"Number of paths when exploring {currFunc.FullDafnyName} = {pathsList.Count}");
          // continue;
        // }
        pathsList.Insert(0, Expression.CreateBoolLiteral(currFunc.tok, false));
        for (int i = 0; i < pathsList.Count; i++) {
          var newBodyExpr = pathsList[i];
          var changeList = GetBaseChangeList();
          var startTok = currFunc.BodyStartTok;
          var endTok = currFunc.BodyEndTok;
          var startBracelet = "{ ";
          var endBracelet = " }";
          if (startTok == null)
          {
            startTok = DafnyVerifierClient.GetFirstToken(currFunc.Body);
            startBracelet = "";
          }
          if (endTok == null)
          {
            endTok = DafnyVerifierClient.GetLastToken(currFunc.Body);
            endBracelet = "";
          }
          var newBodyStr = startBracelet + Printer.ExprToString(newBodyExpr) + endBracelet;
          Change funcChange = DafnyVerifierClient.CreateChange(ChangeTypeEnum.ChangeFunctionBody, startTok, endTok, newBodyStr, "", newBodyStr);
          DafnyVerifierClient.AddFileToChangeList(ref changeList, funcChange);
          var envId = dafnyVerifier.CreateEnvironment(includeParser, changeList);
          foreach (var indexFailingKV in FailingLemmas)
          {
            var verificationReq = dafnyVerifier.EnvironmentVerificationTasks[baseFuncEnvId][indexFailingKV.Key];
            dafnyVerifier.AddVerificationRequestToEnvironment(envId, verificationReq);
          }
          EnvIdToChangeList[envId] = changeList;
          endEnvId = envId;
        }
        await dafnyVerifier.RunVerificationRequestsStartingFromEnvironment(startEnvId, false);
        var failingProofs = new List<Dictionary<int, List<DafnyVerifierClient.ProofFailResult>>>();
        for (int i = startEnvId; i <= endEnvId; i++)
        {
          if (DafnyOptions.O.HoleEvaluatorLogOutputs != "")
          {
            var outputDir = DafnyOptions.O.HoleEvaluatorLogOutputs;
            File.WriteAllText($"{outputDir}/change_{i}.txt", GetChangeListString(i));
            File.WriteAllText($"{outputDir}/request_{i}.txt", GetRequestString(i));
            File.WriteAllText($"{outputDir}/response_{i}.txt", GetResponseString(i));
          }
          var res = GetFailingProofs(i);
          Console.WriteLine($"{i} {res.Count} {Printer.ExprToString(pathsList[i - startEnvId])}");
          failingProofs.Add(res);
          // if (res.Count != 0) {
          // currFunc = 
          // }
        }
        // for (int i = 1; i < failingProofs.Count; i++) {
        //   // same number of failures as false means this predicate has not been the problem
        //   if (failingProofs[i].Count == failingProofs[0].Count) {
        //     foreach (var edge in CG.AdjacencyWeightList[])
        //   }
        // }
        break;
        startEnvId = endEnvId + 1;
      }
      // Function func = HoleEvaluator.GetMember(program, funcName) as Function;
      // if (func == null) {
      //   Console.WriteLine($"couldn't find function {funcName}. List of all functions:");
      //   foreach (var kvp in program.ModuleSigs) {
      //     foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
      //       Console.WriteLine(topLevelDecl.FullDafnyName);
      //     }
      //   }
      //   return null;
      // }
      // List<List<Tuple<Function, FunctionCallExpr, Expression>>> Paths =
        // new List<List<Tuple<Function, FunctionCallExpr, Expression>>>();
      // List<Tuple<Function, FunctionCallExpr, Expression>> CurrentPath =
        // new List<Tuple<Function, FunctionCallExpr, Expression>>();
      // CurrentPath.Add(new Tuple<Function, FunctionCallExpr, Expression>(baseFunc, null, null));
      // HoleEvaluator.GetAllPaths(CG, baseFunc, func, Paths, CurrentPath);
      // if (Paths.Count == 0)
      //   Paths.Add(new List<Tuple<Function, FunctionCallExpr, Expression>>(CurrentPath));

      // calculate holeEvaluatorConstraint Invocation
      // Function constraintFunc = null;
      // if (DafnyOptions.O.HoleEvaluatorConstraint != null) {
      //   constraintFunc = HoleEvaluator.GetMember(program, DafnyOptions.O.HoleEvaluatorConstraint) as Function;
      //   if (constraintFunc == null) {
      //     Console.WriteLine($"constraint function {DafnyOptions.O.HoleEvaluatorConstraint} not found!");
      //     return null;
      //   }
      // }
      // constraintExpr = HoleEvaluator.GetConstraintExpr(program, baseFunc, constraintFunc);

      // Function nullFunc = new Function(
      //   func.tok, "nullFunc", func.HasStaticKeyword, func.IsGhost,
      //   func.TypeArgs, func.Formals, func.Result, func.ResultType,
      //   func.Req, func.Reads, func.Ens, func.Decreases,
      //   func.Body, func.ByMethodTok, func.ByMethodBody,
      //   func.Attributes, func.SignatureEllipsis);
      // {
      //   var changeList = new Dictionary<string, List<Change>>();
      //   var startTok = func.BodyStartTok;
      //   var endTok = func.BodyEndTok;
      //   var startBracelet = "{ ";
      //   var endBracelet = " }";
      //   if (startTok == null)
      //   {
      //     startTok = DafnyVerifierClient.GetFirstToken(func.Body);
      //     startBracelet = "";
      //   }
      //   if (endTok == null)
      //   {
      //     endTok = DafnyVerifierClient.GetLastToken(func.Body);
      //     endBracelet = "";
      //   }
      //   var newBody = startBracelet + "false" + endBracelet;
      //   Change falseFuncChange = DafnyVerifierClient.CreateChange(ChangeTypeEnum.MakeFalseFunction, startTok, endTok, newBody, "", newBody);
      //   DafnyVerifierClient.AddFileToChangeList(ref changeList, falseFuncChange);
      //   var falseEnvId = dafnyVerifier.CreateEnvironment(includeParser, changeList);
      //   foreach (var task in tasksListDictionary)
      //   {
      //     dafnyVerifier.AddVerificationRequestToEnvironment(falseEnvId, "", task.Key, task.Value.Arguments.ToList());
      //   }
      //   EnvIdToChangeList[falseEnvId] = changeList;
      // }

      // // PrintWithFuncFalse(program, func, nullFunc, constraintExpr.expr);
      // foreach (var kvp in program.ModuleSigs) {
      //   foreach (var topLevelDecl in ModuleDefinition.AllCallables(kvp.Value.ModuleDef.TopLevelDecls)) {
      //     if (topLevelDecl.WhatKind == "predicate")
      //     {
      //       var pred = topLevelDecl as Function;
      //       if (pred.Body != null && CG.AdjacencyWeightList.ContainsKey(pred))
      //       {
      //         var cList = new Dictionary<string, List<Change>>();
      //         var startTok = pred.BodyStartTok;
      //         var endTok = pred.BodyEndTok;
      //         var startBracelet = "{ ";
      //         var endBracelet = " }";
      //         if (startTok == null)
      //         {
      //           startTok = DafnyVerifierClient.GetFirstToken(pred.Body);
      //           startBracelet = "";
      //         }
      //         if (endTok == null)
      //         {
      //           endTok = DafnyVerifierClient.GetLastToken(pred.Body);
      //           endBracelet = "";
      //         }
      //         var newBody = startBracelet + "false" + endBracelet;
      //         if (startTok.filename == null)
      //         {
      //           // this only happens in case of refinement
      //           // skip this function
      //           continue;
      //         }
      //         Change falseFuncChange = DafnyVerifierClient.CreateChange(ChangeTypeEnum.MakeFalseFunction, startTok, endTok, newBody, "", newBody);
      //         DafnyVerifierClient.AddFileToChangeList(ref cList, falseFuncChange);
      //         var envId = dafnyVerifier.CreateEnvironment(includeParser, cList);
      //         Console.WriteLine($"{envId} {pred.FullDafnyName}");
      //         foreach (var task in tasksListDictionary)
      //         {
      //           dafnyVerifier.AddVerificationRequestToEnvironment(envId, "", task.Key, task.Value.Arguments.ToList());
      //         }
      //         EnvIdToChangeList[envId] = cList;
      //         // PrintWithFuncFalse(program, func, topLevelDecl, constraintExpr.expr);
      //       }
      //     }
      //   }
      // }
      // await dafnyVerifier.RunVerificationRequestsStartingFromEnvironment(0, false);
      // if (DafnyOptions.O.HoleEvaluatorLogOutputs != "")
      // {
      //   var outputDir = DafnyOptions.O.HoleEvaluatorLogOutputs;
      //   if (!Directory.Exists(outputDir))
      //   {
      //     Directory.CreateDirectory(outputDir);
      //   }
      // }
      // for (int i = 0; i < dafnyVerifier.EnvironmentSetupTasks.Count; i++)
      // {
      //   // if (!correctEnvironments.Contains(i))
      //   // {
      //   if (DafnyOptions.O.HoleEvaluatorLogOutputs != "")
      //   {
      //     var outputDir = DafnyOptions.O.HoleEvaluatorLogOutputs;
      //     File.WriteAllText($"{outputDir}/change_{i}.txt", GetChangeListString(i));
      //     File.WriteAllText($"{outputDir}/request_{i}.txt", GetRequestString(i));
      //     File.WriteAllText($"{outputDir}/response_{i}.txt", GetResponseString(i));
      //   }
      //   var res = GetFailingProofs(i);
      //   Console.WriteLine(res.Count);
      //     // if (res.Count == 0)
      //     // {
      //     //   correctEnvironments.Add(i);
      //     // }
      //   // }
      // }
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
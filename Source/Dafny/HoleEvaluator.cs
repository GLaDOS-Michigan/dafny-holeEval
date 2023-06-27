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
  public enum Result {
    Unknown = 0,
    CorrectProof = 1,
    CorrectProofByTimeout = 2,
    IncorrectProof = 3,
    FalsePredicate = 4,
    InvalidExpr = 5,
    NoMatchingTrigger = 6,
    NotRunningDueToAlreadyCorrectCode = 7,
    CorrectProofWithoutMaintainGuarantee = 8
  }
  public class HoleEvaluator {
    private string UnderscoreStr = "";
    private static Random random = new Random();
    private Cloner cloner = new Cloner();
    public static string RandomString(int length) {
      const string chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
      return new string(Enumerable.Repeat(chars, length)
          .Select(s => s[random.Next(s.Length)]).ToArray());
    }
    public ExpressionFinder expressionFinder = null;
    private List<BitArray> bitArrayList = new List<BitArray>();
    private List<UInt64> executionTimes = new List<UInt64>();
    private ExpressionFinder.ExpressionDepth constraintExpr = null;

    public static bool IsGoodResult(Result result) {
      return (result == Result.CorrectProof ||
              result == Result.CorrectProofByTimeout ||
              result == Result.IncorrectProof ||
              result == Result.Unknown);
    }
    private Dictionary<int, Result> combinationResults = new Dictionary<int, Result>();
    private Dictionary<int, int> negateOfExpressionIndex = new Dictionary<int, int>();
    // private DafnyExecutor dafnyMainExecutor = new DafnyExecutor();
    private DafnyExecutor dafnyImpliesExecutor = new DafnyExecutor();
    public DafnyVerifierClient dafnyVerifier;

    private TasksList tasksList = null;
    private Dictionary<string, VerificationTaskArgs> tasksListDictionary = new Dictionary<string, VerificationTaskArgs>();
    private IncludeParser includeParser = null;
    private List<string> affectedFiles = new List<string>();

    public static int validityLemmaNameStartCol = 0;
    public static string lemmaForExprValidityString = "";
    private static int lemmaForExprValidityLineCount = 0;
    public static string lemmaForMaintainabilityString = "";
    private static int lemmaForMaintainabilityLineCount = 0;

    private void UpdateCombinationResultForMaintainStateLemma(int originalExprIndex, int index) {
      var CAVRequest = dafnyVerifier.requestsList[index] as CloneAndVerifyRequest;
      var CAVOutput = dafnyVerifier.dafnyOutput[CAVRequest] as VerificationResponseList;
      var execTime = CAVOutput.ExecutionTimeInMs;
      executionTimes.Add(execTime);
      for (int i = 0; i < CAVRequest.RequestsList.Count; i++) {
        var request = CAVRequest.RequestsList[i];
        if (request.Arguments.Count == 0) {
          continue;
        }
        var position = dafnyVerifier.requestToPostConditionPosition[request];
        var lemmaStartPosition = dafnyVerifier.requestToLemmaStartPosition[request];
        var output = CAVOutput.ResponseList[i];
        var response = output.Response.ToStringUtf8();
        var filePath = output.FileName;
        if (DafnyOptions.O.HoleEvaluatorVerboseMode) {
          Console.WriteLine($"{originalExprIndex} output for maintain lemma:\n{response}");
        }
        Result res = DafnyVerifierClient.IsCorrectOutputForNoErrors(response);
        if (res == Result.CorrectProof) {
          combinationResults[originalExprIndex] = res;
        }
        else {
          combinationResults[originalExprIndex] = Result.CorrectProofWithoutMaintainGuarantee;
        }
        break;
      }
      expressionFinder.combinationResults[originalExprIndex] = combinationResults[originalExprIndex];
    }

    private void UpdateCombinationResult(int index) {
      var CAVRequest = dafnyVerifier.requestsList[index] as CloneAndVerifyRequest;
      var CAVOutput = dafnyVerifier.dafnyOutput[CAVRequest] as VerificationResponseList;
      var execTime = CAVOutput.ExecutionTimeInMs;
      executionTimes.Add(execTime);
      for (int i = 0; i < CAVRequest.RequestsList.Count; i++) {
        var request = CAVRequest.RequestsList[i];
        if (request.Arguments.Count == 0) {
          continue;
        }
        var position = dafnyVerifier.requestToPostConditionPosition[request];
        var lemmaStartPosition = dafnyVerifier.requestToLemmaStartPosition[request];
        var output = CAVOutput.ResponseList[i];
        var response = output.Response.ToStringUtf8();
        var filePath = output.FileName;
        Result res;
        if (position != -1) {
          var expectedOutput =
            $"{filePath}({position},0): Error: A postcondition might not hold on this return path.";
          var expectedInconclusiveOutputStart =
            $"{filePath}({lemmaStartPosition},{validityLemmaNameStartCol}): Verification inconclusive";
          // Console.WriteLine($"{index} => {output}");
          // Console.WriteLine($"{output.EndsWith("0 errors\n")} {output.EndsWith($"resolution/type errors detected in {fileName}.dfy\n")}");
          // Console.WriteLine($"----------------------------------------------------------------");
          res = DafnyVerifierClient.IsCorrectOutputForValidityCheck(response, expectedOutput, expectedInconclusiveOutputStart);
        } else {
          res = DafnyVerifierClient.IsCorrectOutputForNoErrors(response);
        }
        if (res != Result.IncorrectProof) {
          // correctExpressions.Add(dafnyMainExecutor.processToExpr[p]);
          // Console.WriteLine(output);
          combinationResults[index] = res;
          // Console.WriteLine(p.StartInfo.Arguments);
          // Console.WriteLine(Printer.ExprToString(dafnyVerifier.requestToExpr[request]));
        } else if (position != -1 && response.EndsWith("0 errors\n")) {
          combinationResults[index] = Result.FalsePredicate;
          break;
        } else if (response.EndsWith($"resolution/type errors detected in {Path.GetFileName(filePath)}\n")) {
          combinationResults[index] = Result.InvalidExpr;
          break;
        } else {
          combinationResults[index] = Result.IncorrectProof;
          break;
        }
      }
      expressionFinder.combinationResults[index] = combinationResults[index];
    }

    public Dictionary<string, List<string>> GetEqualExpressionList(Expression expr) {
      // The first element of each value's list in the result is the type of list
      Dictionary<string, List<string>> result = new Dictionary<string, List<string>>();
      HoleEvalGraph<string> G = new HoleEvalGraph<string>();
      foreach (var e in Expression.Conjuncts(expr)) {
        if (e is BinaryExpr && (e as BinaryExpr).ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon) {
          var be = e as BinaryExpr;
          var e0 = Printer.ExprToString(be.E0);
          var e1 = Printer.ExprToString(be.E1);
          if (e0 == e1) {
            continue;
          }
          if (!G.AdjacencyList.ContainsKey(e0)) {
            G.AddVertex(e0);
          }
          if (!G.AdjacencyList.ContainsKey(e1)) {
            G.AddVertex(e1);
          }
          G.AddEdge(new Tuple<string, string>(e0, e1));
        }
      }
      HashSet<string> visited = new HashSet<string>();
      foreach (var e in Expression.Conjuncts(expr)) {
        if (e is BinaryExpr && (e as BinaryExpr).ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon) {
          var be = e as BinaryExpr;
          var e0 = Printer.ExprToString(be.E0);
          var e1 = Printer.ExprToString(be.E1);
          if (e0 == e1) {
            continue;
          }
          if (visited.Contains(e0) || visited.Contains(e1)) {
            Debug.Assert(visited.Contains(e0));
            Debug.Assert(visited.Contains(e1));
            continue;
          }
          HashSet<string> newVisits = G.DFS(e0);
          visited.UnionWith(newVisits);
          result[e0] = new List<string>();
          // The first element of each value's list in the result is the type of list
          result[e0].Add(be.E0.Type.ToString());
          newVisits.Remove(e0);
          foreach (string s in newVisits) {
            result[e0].Add(s);
          }
        }
      }
      return result;
    }

    public static DirectedCallGraph<Function, FunctionCallExpr, Expression> GetCallGraph(Function baseFunc) {
      Contract.Requires(baseFunc != null);
      DirectedCallGraph<Function, FunctionCallExpr, Expression> G = new DirectedCallGraph<Function, FunctionCallExpr, Expression>();
      // Tuple of SubExpression that is going to be parsed, pre-condition to reach this SubExpression, containing Function
      Queue<Tuple<Expression, Expression, Function>> queue = new Queue<Tuple<Expression, Expression, Function>>();
      queue.Enqueue(new Tuple<Expression, Expression, Function>(baseFunc.Body, null, baseFunc));
      G.AddVertex(baseFunc);
      HashSet<string> seenFunctionCalls = new HashSet<string>();
      // keys.Add(Printer.ExprToString(baseF.Body) + ":" + baseF.Body);
      // TODO: Check an example in which a function is called in another function with two different pre-conditions
      while (queue.Count > 0) {
        Tuple<Expression, Expression, Function> currExprCondParentTuple = queue.Dequeue();
        if (currExprCondParentTuple.Item1 == null) continue;
        // Console.WriteLine("Processing " + currExprParentTuple.Item1 + ": " + Printer.ExprToString(currExprParentTuple.Item1));
        if (currExprCondParentTuple.Item1 is FunctionCallExpr /*&& (currExpr as FunctionCallExpr).Function.Body != null*/) {
          // if (!keys.Contains(Printer.ExprToString((currExprParentTuple.Item1 as FunctionCallExpr).Function.Body) + ":" + (currExprParentTuple.Item1 as FunctionCallExpr).Function.Body)) {
          // Console.WriteLine("Adding " + (currExprParentTuple.Item1 as FunctionCallExpr).Function.Body + ": " + Printer.ExprToString((currExprParentTuple.Item1 as FunctionCallExpr).Function.Body));
          var funcCallCondAsString = $"{currExprCondParentTuple.Item3.Name} -> " +
                                     $"{(currExprCondParentTuple.Item1 as FunctionCallExpr).Function.Name} -> ";
          if (currExprCondParentTuple.Item2 != null) {
            funcCallCondAsString += $"{Printer.ExprToString(currExprCondParentTuple.Item2)}";
          } else {
            funcCallCondAsString += "NULL";
          }
          if (!seenFunctionCalls.Contains(funcCallCondAsString)) {
            seenFunctionCalls.Add(funcCallCondAsString);
            // if (currExprCondParentTuple.Item2 != null) {
            //   Console.WriteLine($"condition : {Printer.ExprToString(currExprCondParentTuple.Item2)}");
            // } else {
            //   Console.WriteLine($"condition : null");
            // }
            // if ((currExprCondParentTuple.Item1 as FunctionCallExpr).Function.ToString() == ) {

            // }
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
          var thenCond = currExprCondParentTuple.Item2 != null ?
            Expression.CreateAnd(currExprCondParentTuple.Item2, iteExpr.Test) :
            iteExpr.Test;
          queue.Enqueue(new Tuple<Expression, Expression, Function>(
            iteExpr.Thn, thenCond, currExprCondParentTuple.Item3));

          // add else path
          var elseCond = currExprCondParentTuple.Item2 != null ?
            Expression.CreateAnd(currExprCondParentTuple.Item2,
                                 Expression.CreateNot(iteExpr.Test.tok, iteExpr.Test)) :
            Expression.CreateNot(iteExpr.Test.tok, iteExpr.Test);
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
            var cond = currExprCondParentTuple.Item2 != null ?
              Expression.CreateAnd(currExprCondParentTuple.Item2, new MemberSelectExpr(c.Ctor.tok, matchExpr.Source, c.Ctor.Name)) :
              new MemberSelectExpr(c.Ctor.tok, matchExpr.Source, c.Ctor.Name + "?");
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
          var cond = Expression.CreateAnd(existsExpr, Expression.CreateLet(existsExpr.BodyStartTok, lhss, rhss,
            Expression.CreateBoolLiteral(existsExpr.BodyStartTok, true), false));

          queue.Enqueue(new Tuple<Expression, Expression, Function>(existsExpr.Term, cond, currExprCondParentTuple.Item3));
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

    DirectedCallGraph<Function, FunctionCallExpr, Expression> CG;
    List<List<Tuple<Function, FunctionCallExpr, Expression>>> Paths =
      new List<List<Tuple<Function, FunctionCallExpr, Expression>>>();
    List<Tuple<Function, FunctionCallExpr, Expression>> CurrentPath =
      new List<Tuple<Function, FunctionCallExpr, Expression>>();

    public void GetAllPaths(Function source, Function destination) {
      if (source.FullDafnyName == destination.FullDafnyName) {
        Paths.Add(new List<Tuple<Function, FunctionCallExpr, Expression>>(CurrentPath));
        return;
      }
      var neighbourWeightList = CG.AdjacencyWeightList[source];
      foreach (var nwPair in neighbourWeightList) {
        CurrentPath.Add(new Tuple<Function, FunctionCallExpr, Expression>(
          nwPair.Item1, nwPair.Item2, nwPair.Item3));
        GetAllPaths(nwPair.Item1, destination);
        CurrentPath.RemoveAt(CurrentPath.Count - 1);
      }
    }

    public static string GetPrefixedString(string prefix, Expression expr, ModuleDefinition currentModuleDef, Dictionary<string, string> changedPredicatesDict = null) {
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr);
        // pr.UniqueStringBeforeUnderscore = UnderscoreStr;
        pr.Prefix = prefix;
        pr.ChangedPredicatesDict = changedPredicatesDict;
        pr.ModuleForTypes = currentModuleDef;
        pr.PrintExpression(expr, false);
        return wr.ToString();
      }
    }

    public static string GetPrefixedString(string prefix, string name) {
      var strSplit = name.Split('.');
      strSplit[strSplit.Length - 1] = prefix + strSplit[strSplit.Length - 1];
      return strSplit.Concat(".");
    }

    public static Dictionary<string, string> ChangedPredicatesDictionary = new Dictionary<string, string>();

    public static string GetMaintainabilityLemma(List<Tuple<Function, FunctionCallExpr, Expression>> path, Expression constraintExpr, ModuleDefinition currentModuleDef)
    {
      Contract.Requires(constraintExpr != null);
      string res = "lemma {:timeLimitMultiplier 2} maintainCheck";
      foreach (var nwPair in path) {
        res += "_" + nwPair.Item1.Name;
      }
      res += "(";
      var sep = "";
      var newParamLists = new List<Tuple<List<string>, string>>();
      var oldParamLists = new List<Tuple<List<string>, string>>();
      // function params for new one
      foreach (var nwPair in path) {
        res += sep + "\n    ";
        var paramList = GetFunctionParamList(nwPair.Item1, nwPair.Item1.Name + "_");
        res += paramList.Item2;
        newParamLists.Add(paramList);
        sep = ", ";
      }
      // function params for old one
      foreach (var nwPair in path) {
        res += sep + "\n    ";
        var paramList = GetFunctionParamList(nwPair.Item1, "old_" + nwPair.Item1.Name + "_");
        res += paramList.Item2;
        oldParamLists.Add(paramList);
        sep = ", ";
      }
      res += ")\n";

      // // print equality between param lists
      res += "\n  // requires equality between new and old arguments\n";
      for (int i = 0; i < newParamLists.Count; i++) {
        for (int j = 0; j < newParamLists[i].Item1.Count; j++) {
          res += "  requires " + newParamLists[i].Item1[j] + " == " + oldParamLists[i].Item1[j] + "\n";
        }
      }

      for (int i = 0; i < path.Count; i++) {
        ChangedPredicatesDictionary.Add(path[i].Item1.FullDafnyName, GetPrefixedString("old_", path[i].Item1.FullDafnyName));
      }
      res += "\n  // requires Next(old_s, old_s')\n";
      // print path[0] for old one
      foreach (var req in path[0].Item1.Req) {
        res += "  requires " + GetPrefixedString("old_" + path[0].Item1.Name + "_", req.E, currentModuleDef) + "\n";
      }
      res += "  requires " + GetPrefixedString("old_", path[0].Item1.FullDafnyName) + "(";
      sep = "";
      foreach (var formal in path[0].Item1.Formals) {
        res += sep + "old_" + path[0].Item1.Name + "_" + formal.Name;
        sep = ", ";
      }
      res += ")\n";

      // print rest for old one
      for (int i = 0; i < path.Count - 1; i++) {
        var callExpr = path[i + 1].Item2;
        var condExpr = path[i + 1].Item3;
        var requiresOrAndSep = "requires";
        if (condExpr != null) {
          if (condExpr is BinaryExpr && (condExpr as BinaryExpr).E1 is LetExpr) {
            requiresOrAndSep = "  &&";
          }
          currentModuleDef = path[i].Item1.EnclosingClass.EnclosingModuleDefinition;
          res += $"  {requiresOrAndSep} " + GetPrefixedString("old_" + path[i].Item1.Name + "_", condExpr, currentModuleDef, ChangedPredicatesDictionary) + "\n";
        }
        for (int j = 0; j < callExpr.Args.Count; j++) {
          res += $"  {requiresOrAndSep} ";
          res += GetPrefixedString("old_" + path[i].Item1.Name + "_", callExpr.Args[j], currentModuleDef, ChangedPredicatesDictionary);
          res += " == ";
          res += "old_" + path[i + 1].Item1.Name + "_" + path[i + 1].Item1.Formals[j].Name + "\n";
        }
        foreach (var req in callExpr.Function.Req) {
          res += $"  {requiresOrAndSep} " + GetPrefixedString("old_" + path[i + 1].Item1.Name + "_", req.E, currentModuleDef) + "\n";
        }
        res += $"  {requiresOrAndSep} " + GetPrefixedString("old_", callExpr.Function.FullDafnyName) + "(";
        sep = "";
        foreach (var arg in callExpr.Args) {
          res += sep + GetPrefixedString("old_" + path[i].Item1.Name + "_", arg, currentModuleDef);
          sep = ", ";
        }
        res += ")\n";
      }

      res += "\n  // requires Inv(old_s) && Inv(old_s')\n";
      currentModuleDef = path[0].Item1.EnclosingClass.EnclosingModuleDefinition;
      res += "  requires " + GetPrefixedString("old_" + path[0].Item1.Name + "_", constraintExpr, currentModuleDef) + "\n";
      res += "\n  // requires Inv(s) && Inv(s')\n";
      res += "  requires " + GetPrefixedString(path[0].Item1.Name + "_", constraintExpr, currentModuleDef) + "\n";

      res += "\n  // ensures Next(s, s') in reverse order\n";
      // print rest for new one (in reverse order)
      for (int i = path.Count - 2; i >= 0; i--) {
        var callExpr = path[i + 1].Item2;
        var condExpr = path[i + 1].Item3;
        var requiresOrAndSep = "ensures";
        if (condExpr != null) {
          if (condExpr is BinaryExpr && (condExpr as BinaryExpr).E1 is LetExpr) {
            requiresOrAndSep = "  &&";
          }
          currentModuleDef = path[i].Item1.EnclosingClass.EnclosingModuleDefinition;
          res += $"  {requiresOrAndSep} " + GetPrefixedString(path[i].Item1.Name + "_", condExpr, currentModuleDef) + "\n";
        }
        for (int j = 0; j < callExpr.Args.Count; j++) {
          res += $"  {requiresOrAndSep} ";
          res += GetPrefixedString(path[i].Item1.Name + "_", callExpr.Args[j], currentModuleDef);
          res += " == ";
          res += path[i + 1].Item1.Name + "_" + path[i + 1].Item1.Formals[j].Name + "\n";
        }
        foreach (var req in callExpr.Function.Req) {
          res += $"  {requiresOrAndSep} " + GetPrefixedString(path[i + 1].Item1.Name + "_", req.E, currentModuleDef) + "\n";
        }
        res += $"  {requiresOrAndSep} " + callExpr.Function.FullDafnyName + "(";
        sep = "";
        foreach (var arg in callExpr.Args) {
          res += sep + GetPrefixedString(path[i].Item1.Name + "_", arg, currentModuleDef);
          sep = ", ";
        }
        res += ")\n";
      }
      // print path[0] for new one
      foreach (var req in path[0].Item1.Req) {
        res += "  ensures " + GetPrefixedString(path[0].Item1.Name + "_", req.E, currentModuleDef) + "\n";
      }
      res += "  ensures " + path[0].Item1.FullDafnyName + "(";
      sep = "";
      foreach (var formal in path[0].Item1.Formals) {
        res += sep + path[0].Item1.Name + "_" + formal.Name;
        sep = ", ";
      }
      res += ")\n";
      res += "{}\n";

      return res;
    }

    public static string GetValidityLemma(List<Tuple<Function, FunctionCallExpr, Expression>> path, ModuleDefinition currentModuleDef, Expression constraintExpr, int cnt) {
      string res = "lemma {:timeLimitMultiplier 2} validityCheck";
      if (cnt != -1) {
        res += "_" + cnt.ToString();
      }
      foreach (var nwPair in path) {
        res += "_" + nwPair.Item1.Name;
      }
      res += "(";
      var sep = "";
      foreach (var nwPair in path) {
        res += sep + "\n    ";
        sep = "";
        res += GetFunctionParamList(nwPair.Item1, nwPair.Item1.Name + "_").Item2;
        sep = ", ";
      }
      res += ")\n";
      foreach (var req in path[0].Item1.Req) {
        res += "  requires " + GetPrefixedString(path[0].Item1.Name + "_", req.E, currentModuleDef) + "\n";
      }
      res += "  requires " + path[0].Item1.FullDafnyName + "(";
      sep = "";
      foreach (var formal in path[0].Item1.Formals) {
        res += sep + path[0].Item1.Name + "_" + formal.Name;
        sep = ", ";
      }
      res += ")\n";
      for (int i = 0; i < path.Count - 1; i++) {
        var callExpr = path[i + 1].Item2;
        var condExpr = path[i + 1].Item3;
        var requiresOrAndSep = "requires";
        if (condExpr != null) {
          if (condExpr is BinaryExpr && (condExpr as BinaryExpr).E1 is LetExpr) {
            requiresOrAndSep = "  &&";
          }
          currentModuleDef = path[i].Item1.EnclosingClass.EnclosingModuleDefinition;
          res += $"  {requiresOrAndSep} " + GetPrefixedString(path[i].Item1.Name + "_", condExpr, currentModuleDef) + "\n";
        }
        for (int j = 0; j < callExpr.Args.Count; j++) {
          res += $"  {requiresOrAndSep} ";
          res += GetPrefixedString(path[i].Item1.Name + "_", callExpr.Args[j], currentModuleDef);
          res += " == ";
          res += path[i + 1].Item1.Name + "_" + path[i + 1].Item1.Formals[j].Name + "\n";
        }
        foreach (var req in callExpr.Function.Req) {
          res += $"  {requiresOrAndSep} " + GetPrefixedString(path[i + 1].Item1.Name + "_", req.E, currentModuleDef) + "\n";
        }
        res += $"  {requiresOrAndSep} " + callExpr.Function.FullDafnyName + "(";
        sep = "";
        foreach (var arg in callExpr.Args) {
          res += sep + GetPrefixedString(path[i].Item1.Name + "_", arg, currentModuleDef);
          sep = ", ";
        }
        res += ")\n";
      }
      if (constraintExpr != null) {
        currentModuleDef = path[0].Item1.EnclosingClass.EnclosingModuleDefinition;
        res += "  requires " + GetPrefixedString(path[0].Item1.Name + "_", constraintExpr, currentModuleDef) + "\n";
      }
      res += "  ensures false\n{}";
      return res;
    }

    public async Task<bool> EvaluateAfterRemoveFileLine(Program program, Program unresolvedProgram, string removeFileLine, string baseFuncName, int depth) {
      var funcName = CodeModifier.Erase(program, removeFileLine);
      return await Evaluate(program, unresolvedProgram, funcName, baseFuncName, depth);
    }

    public async Task<bool> Evaluate(Program program, Program unresolvedProgram, string funcName, string baseFuncName, int depth) {
      if (DafnyOptions.O.HoleEvaluatorServerIpPortList == null) {
        Console.WriteLine("ip port list is not given. Please specify with /holeEvalServerIpPortList");
        return false;
      }
      if (DafnyOptions.O.HoleEvaluatorCommands != null) {
        var input = File.ReadAllText(DafnyOptions.O.HoleEvaluatorCommands);
        tasksList = Google.Protobuf.JsonParser.Default.Parse<TasksList>(input);
        foreach (var task in tasksList.Tasks) {
          tasksListDictionary.Add(task.Path, task);
        }
      }
      dafnyVerifier = new DafnyVerifierClient(DafnyOptions.O.HoleEvaluatorServerIpPortList, $"output_{funcName}");
      expressionFinder = new ExpressionFinder(this);
      bool runOnce = DafnyOptions.O.HoleEvaluatorRunOnce;
      int timeLimitMultiplier = 2;
      int timeLimitMultiplierLength = 0;
      while (timeLimitMultiplier >= 1) {
        timeLimitMultiplierLength++;
        timeLimitMultiplier /= 10;
      }
      validityLemmaNameStartCol = 30 + timeLimitMultiplierLength;

      // Collect all paths from baseFunc to func
      Console.WriteLine($"{funcName} {baseFuncName} {depth}");
      if (baseFuncName == null) {
        baseFuncName = funcName;
      }
      Function baseFunc = GetFunction(program, baseFuncName);
      if (baseFunc == null) {
        Console.WriteLine($"couldn't find function {baseFuncName}. List of all functions:");
        foreach (var kvp in program.ModuleSigs) {
          foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
            Console.WriteLine(topLevelDecl.FullDafnyName);
          }
        }
        return false;
      }
      Function constraintFunc = null;
      if (DafnyOptions.O.HoleEvaluatorConstraint != null) {
        constraintFunc = GetFunction(program, DafnyOptions.O.HoleEvaluatorConstraint);
        if (constraintFunc == null) {
          Console.WriteLine($"constraint function {DafnyOptions.O.HoleEvaluatorConstraint} not found!");
          return false;
        }
      }
      CG = GetCallGraph(baseFunc);
      Function func = GetFunction(program, funcName);
      CurrentPath.Add(new Tuple<Function, FunctionCallExpr, Expression>(baseFunc, null, null));
      GetAllPaths(baseFunc, func);
      if (Paths.Count == 0)
        Paths.Add(new List<Tuple<Function, FunctionCallExpr, Expression>>(CurrentPath));
      // foreach (var p in Paths) {
      //   Console.WriteLine(GetValidityLemma(p));
      //   Console.WriteLine("\n----------------------------------------------------------------\n");
      // }
      // return true;

      UnderscoreStr = RandomString(8);
      dafnyVerifier.sw = Stopwatch.StartNew();
      Console.WriteLine($"hole evaluation begins for func {funcName}");
      Function desiredFunction = null;
      Function desiredFunctionUnresolved = null;
      Function topLevelDeclCopy = null;
      desiredFunction = GetFunction(program, funcName);
      if (desiredFunction != null) {
        includeParser = new IncludeParser(program);
        var filename = includeParser.Normalized(desiredFunction.BodyStartTok.filename);
        foreach (var file in includeParser.GetListOfAffectedFilesBy(filename)) {
          affectedFiles.Add(file);
        }
        dafnyVerifier.InitializeBaseFoldersInRemoteServers(program, includeParser.commonPrefix);
        affectedFiles.Add(filename);
        affectedFiles = affectedFiles.Distinct().ToList();
        // calculate holeEvaluatorConstraint Invocation
        if (constraintFunc != null) {
          Dictionary<string, HashSet<ExpressionFinder.ExpressionDepth>> typeToExpressionDictForInputs = new Dictionary<string, HashSet<ExpressionFinder.ExpressionDepth>>();
          foreach (var formal in baseFunc.Formals) {
            var identExpr = new ExpressionFinder.ExpressionDepth(Expression.CreateIdentExpr(formal), 1);
            var typeString = formal.Type.ToString();
            if (typeToExpressionDictForInputs.ContainsKey(typeString)) {
              typeToExpressionDictForInputs[typeString].Add(identExpr);
            } else {
              var lst = new HashSet<ExpressionFinder.ExpressionDepth>();
              lst.Add(identExpr);
              typeToExpressionDictForInputs.Add(typeString, lst);
            }
          }
          var funcCalls = ExpressionFinder.GetAllPossibleFunctionInvocations(program, constraintFunc, typeToExpressionDictForInputs);
          foreach (var funcCall in funcCalls) {
            if (constraintExpr == null) {
              constraintExpr = new ExpressionFinder.ExpressionDepth(funcCall.expr, 1);
            } else {
              constraintExpr.expr = Expression.CreateAnd(constraintExpr.expr, funcCall.expr);
            }
          }
          Console.WriteLine($"constraint expr to be added : {Printer.ExprToString(constraintExpr.expr)}");
        }
        expressionFinder.CalcDepthOneAvailableExpresssionsFromFunction(program, desiredFunction);
        desiredFunctionUnresolved = GetFunctionFromUnresolved(unresolvedProgram, funcName);
        if (DafnyOptions.O.HoleEvaluatorRemoveFileLine != null) {
          var fileLineList = DafnyOptions.O.HoleEvaluatorRemoveFileLine.Split(',');
          foreach (var fileLineString in fileLineList) {
            var fileLineArray = fileLineString.Split(':');
            var file = fileLineArray[0];
            var line = Int32.Parse(fileLineArray[1]);
            CodeModifier.EraseFromPredicate(desiredFunctionUnresolved as Predicate, line);
          }
        }
        Contract.Assert(desiredFunctionUnresolved != null);
        topLevelDeclCopy = new Function(
          desiredFunctionUnresolved.tok, desiredFunctionUnresolved.Name, desiredFunctionUnresolved.HasStaticKeyword,
          desiredFunctionUnresolved.IsGhost, desiredFunctionUnresolved.TypeArgs, desiredFunctionUnresolved.Formals,
          desiredFunctionUnresolved.Result, desiredFunctionUnresolved.ResultType, desiredFunctionUnresolved.Req,
          desiredFunctionUnresolved.Reads, desiredFunctionUnresolved.Ens, desiredFunctionUnresolved.Decreases,
          desiredFunctionUnresolved.Body, desiredFunctionUnresolved.ByMethodTok, desiredFunctionUnresolved.ByMethodBody,
          desiredFunctionUnresolved.Attributes, desiredFunctionUnresolved.SignatureEllipsis);
      } else {
        Console.WriteLine($"{funcName} was not found!");
        return false;
      }
      Console.WriteLine($"expressionFinder.availableExpressions.Count == {expressionFinder.availableExpressions.Count}");

      workingFunc = desiredFunctionUnresolved;
      workingConstraintFunc = constraintFunc;
      workingFuncCode = File.ReadAllLines(workingFunc.BodyStartTok.filename);
      mergedCode.Add(String.Join('\n', workingFuncCode.Take(workingFunc.tok.line - 1)));
      // placeholder for workingLemma
      mergedCode.Add("");
      mergedCode.Add(String.Join('\n', workingFuncCode.Skip(workingFunc.BodyEndTok.line)));

      if (constraintFunc != null && constraintFunc.BodyStartTok.filename != workingFunc.BodyStartTok.filename) {
        constraintFuncCode = File.ReadAllText(constraintFunc.BodyStartTok.filename);
        constraintFuncLineCount = constraintFuncCode.Count(f => (f == '\n'));
      }
      
      lemmaForExprValidityString = GetValidityLemma(Paths[0], null, constraintExpr == null ? null : constraintExpr.expr, -1);
      lemmaForExprValidityLineCount = lemmaForExprValidityString.Count(f => (f == '\n'));

      lemmaForMaintainabilityString = GetMaintainabilityLemma(Paths[0], constraintExpr == null ? null : constraintExpr.expr, null);
      lemmaForMaintainabilityLineCount = lemmaForMaintainabilityString.Count(f => (f == '\n'));

      for (int i = 0; i < expressionFinder.availableExpressions.Count; i++) {
      // for (int i = 0; i < 100; i++) {
        PrintExprAndCreateProcess(unresolvedProgram, expressionFinder.availableExpressions[i], i);
        desiredFunctionUnresolved.Body = topLevelDeclCopy.Body;
      }
      Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: finish generatinng expressions and lemmas");
      await dafnyVerifier.startProofTasksAccordingToPriority();
      Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: finish exploring");

      // bool foundCorrectExpr = false;
      
      for (int i = 0; i < expressionFinder.availableExpressions.Count; i++) {
      // for (int i = 0; i < 100; i++) {
        UpdateCombinationResult(i);
        // foundCorrectExpr |= combinationResults[i] == Result.CorrectProof;
      }

      // Until here, we only check depth 1 of expressions.
      // Now we try to check next depths
      int numberOfSingleExpr = expressionFinder.availableExpressions.Count;
      for (int dd = 2; dd <= depth; dd++) {
        var prevDepthExprStartIndex = expressionFinder.availableExpressions.Count;
        expressionFinder.CalcNextDepthAvailableExpressions();
        for (int i = prevDepthExprStartIndex; i < expressionFinder.availableExpressions.Count; i++) {
          var expr = expressionFinder.availableExpressions[i];
          PrintExprAndCreateProcess(program, expr, i);
          desiredFunction.Body = topLevelDeclCopy.Body;
        }
        await dafnyVerifier.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs();
        for (int i = prevDepthExprStartIndex; i < expressionFinder.availableExpressions.Count; i++) {
          UpdateCombinationResult(i);
        }
      }
      Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: finish exploring, try to check maintain state lemma");
      var passingProof = new List<int>();
      dafnyVerifier.RestartConsumers();
      for (int i = 0; i < expressionFinder.availableExpressions.Count; i++) {
        if (combinationResults[i] == Result.CorrectProof || combinationResults[i] == Result.CorrectProof) {
          var expr = expressionFinder.availableExpressions[i];
          CheckMaintainState(unresolvedProgram, expr, expressionFinder.availableExpressions.Count + passingProof.Count);
          passingProof.Add(i);
        }
      }
      await dafnyVerifier.startProofTasksAccordingToPriority();
      dafnyVerifier.Cleanup();
      for (int i = 0; i < passingProof.Count; i++) {
        UpdateCombinationResultForMaintainStateLemma(passingProof[i], i + expressionFinder.availableExpressions.Count);
      }
      int correctProofCount = 0;
      int correctProofByTimeoutCount = 0;
      int correctProofWithoutMaintainCount = 0;
      int incorrectProofCount = 0;
      int invalidExprCount = 0;
      int falsePredicateCount = 0;
      int noMatchingTriggerCount = 0;
      for (int i = 0; i < expressionFinder.availableExpressions.Count; i++) {
      // for (int i = 0; i < 100; i++) {
        switch (combinationResults[i]) {
          case Result.InvalidExpr: invalidExprCount++; break;
          case Result.FalsePredicate: falsePredicateCount++; break;
          case Result.CorrectProof:
            Console.WriteLine($"correct answer: {i} {Printer.ExprToString(expressionFinder.availableExpressions[i].expr)}");
            correctProofCount++; 
            break;
          case Result.CorrectProofWithoutMaintainGuarantee:
            Console.WriteLine($"correct answer but not passing maintain guarantee: {i} {Printer.ExprToString(expressionFinder.availableExpressions[i].expr)}");
            correctProofWithoutMaintainCount++; 
            break;
          case Result.CorrectProofByTimeout: 
            Console.WriteLine($"correct answer by timeout: {i}");
            correctProofByTimeoutCount++; 
            break;
          case Result.IncorrectProof: incorrectProofCount++; break;
          case Result.NoMatchingTrigger: noMatchingTriggerCount++; break;
          case Result.Unknown: throw new NotSupportedException();
        }
      }
      Console.WriteLine("{0,-15} {1,-15} {2,-15} {3,-15} {4, -25} {5, -15} {6, -15}",
        "InvalidExpr", "IncorrectProof", "TriviallyCorrect", "CorrectProof", "CorrectProofByTimeout", "CorrectProofWOMaintain", "NoMatchingTrigger", "Total");
      Console.WriteLine("{0,-15} {1,-15} {2,-15} {3,-15} {4, -25} {5, -25} {6, -15} {7, -15}",
        invalidExprCount, incorrectProofCount, falsePredicateCount, correctProofCount, correctProofByTimeoutCount,
        correctProofWithoutMaintainCount, noMatchingTriggerCount, expressionFinder.availableExpressions.Count);
      string executionTimesSummary = "";
      // executionTimes.Sort();
      for (int i = 0; i < executionTimes.Count; i++) {
        executionTimesSummary += $"{i}, {executionTimes[i]}\n";
      }
      await File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}/executionTimeSummary.txt",
            executionTimesSummary);

      // for (int i = 0; i < bitArrayList.Count; i++) {
      //   var ba = bitArrayList[i];
      //   Console.WriteLine("------------------------------");
      //   Console.WriteLine(i + " : " +
      //                     Printer.ExprToString(availableExpressions[i]) + " : " +
      //                     combinationResults[i].ToString());
      //   Console.WriteLine(ToBitString(ba));
      //   Console.WriteLine("------------------------------");
      // }
      // return true;

      // int correctExpressionCount = combinationResults.Count(elem => elem.Value == Result.CorrectProof);
      // if (correctExpressionCount == 0) {
      //   Console.WriteLine("Couldn't find any correct answer. Printing 0 error ones");
      //   for (int i = 0; i < availableExpressions.Count; i++) {
      //     if (combinationResults[i] == Result.InvalidExpr) {
      //       var p = dafnyMainExecutor.dafnyProcesses[i];
      //       Console.WriteLine(p.StartInfo.Arguments);
      //       Console.WriteLine(Printer.ExprToString(dafnyMainExecutor.processToExpr[p]));
      //     }
      //   }
      //   return false;
      // }
      // The 0th process represents no change to the predicate, and
      // if that is a correct predicate, it means the proof already 
      // goes through and no additional conjunction is needed.
      if (combinationResults[0] == Result.CorrectProof || combinationResults[0] == Result.CorrectProofByTimeout) {
        Console.WriteLine("proof already goes through and no additional conjunction is needed!");
        return true;
      }
      await dafnyVerifier.FinalizeCleanup();
      return true;
      List<int> correctExpressionsIndex = new List<int>();
      for (int i = 0; i < expressionFinder.availableExpressions.Count; i++) {
        if (combinationResults[i] == Result.CorrectProof || combinationResults[i] == Result.CorrectProofByTimeout)
          correctExpressionsIndex.Add(i);
      }
      // for (int i = 0; i < correctExpressionsIndex.Count; i++) {
      //   Console.WriteLine($"correct Expr #{correctExpressionsIndex[i],3}: {Printer.ExprToString(availableExpressions[correctExpressionsIndex[i]])}");
      // }
      for (int i = 0; i < correctExpressionsIndex.Count; i++) {
        for (int j = i + 1; j < correctExpressionsIndex.Count; j++) {
          {
            PrintImplies(program, desiredFunction, correctExpressionsIndex[i], correctExpressionsIndex[j]);
            PrintImplies(program, desiredFunction, correctExpressionsIndex[j], correctExpressionsIndex[i]);
          }
        }
      }
      dafnyImpliesExecutor.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs(true);
      Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: finish calculating implies, printing the dot graph");
      string graphVizOutput = $"digraph \"{funcName}_implies_graph\" {{\n";
      graphVizOutput += "  // The list of correct expressions\n";
      for (int i = 0; i < correctExpressionsIndex.Count; i++) {
        graphVizOutput += $"  {correctExpressionsIndex[i]} [label=\"{Printer.ExprToString(expressionFinder.availableExpressions[correctExpressionsIndex[i]].expr)}\"];\n";
      }
      graphVizOutput += "\n  // The list of edges:\n";
      foreach (var p in dafnyImpliesExecutor.dafnyProcesses) {
        var availableExprAIndex = dafnyImpliesExecutor.processToAvailableExprAIndex[p];
        var availableExprBIndex = dafnyImpliesExecutor.processToAvailableExprBIndex[p];
        // skip connecting all nodes to true
        if (Printer.ExprToString(expressionFinder.availableExpressions[availableExprAIndex].expr) == "true" ||
            Printer.ExprToString(expressionFinder.availableExpressions[availableExprBIndex].expr) == "true")
          continue;
        var output = dafnyImpliesExecutor.dafnyOutput[p];
        if (output.EndsWith("0 errors\n")) {
          Console.WriteLine($"edge from {availableExprAIndex} to {availableExprBIndex}");
          graphVizOutput += $"  {availableExprAIndex} -> {availableExprBIndex};\n";
        }
      }
      graphVizOutput += "}\n";
      await File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}graph_{funcName}_implies.dot", graphVizOutput);
      Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: end");
      return true;
    }

    public static string GetFullModuleName(ModuleDefinition moduleDef) {
      if (moduleDef.Name == "_module") {
        return "";
      } else if (moduleDef.EnclosingModule.Name == "_module") {
        return moduleDef.Name;
      } else {
        return GetFullModuleName(moduleDef.EnclosingModule) + "." + moduleDef.Name;
      }
    }

    public static string GetFullLemmaNameString(ModuleDefinition moduleDef, string name) {
      if (moduleDef is null) {
        return name;
      }
      foreach (var decl in ModuleDefinition.AllFunctions(moduleDef.TopLevelDecls)) {
        if (decl.ToString() == name) {
          var moduleName = GetFullModuleName(moduleDef);
          return (moduleName == "") ? name : (moduleName + "." + name);
        }
      }
      foreach (var imp in ModuleDefinition.AllDeclarationsAndNonNullTypeDecls(moduleDef.TopLevelDecls)) {
        if (imp is ModuleDecl) {
          var result = GetFullLemmaNameString((imp as ModuleDecl).Signature.ModuleDef, name);
          if (result != "") {
            return result;
          }
        }
      }
      // couldn't find the type definition here, so we should search the parent
      return "";
    }


    public static Tuple<List<string>, string> GetFunctionParamList(Function func, string namePrefix = "") {
      var funcName = func.FullDafnyName;
      string parameterNameTypes = "";
      List<string> paramNames = new List<string>();
      var sep = "";
      foreach (var param in func.Formals) {
        parameterNameTypes += sep + namePrefix + param.Name + ":" + Printer.GetFullTypeString(func.EnclosingClass.EnclosingModuleDefinition, param.Type, new HashSet<ModuleDefinition>());
        paramNames.Add(namePrefix + param.Name);
        sep = ", ";
      }
      return new Tuple<List<string>, string>(paramNames, parameterNameTypes);
    }

    public static Function GetFunction(Program program, string funcName) {
      foreach (var kvp in program.ModuleSigs) {
        foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
          if (topLevelDecl.FullDafnyName == funcName) {
            return topLevelDecl;
          }
        }
      }
      return null;
    }

    public static Function GetFunctionFromModuleDef(ModuleDefinition moduleDef, string funcName) {
      foreach (var topLevelDecl in moduleDef.TopLevelDecls) {
        if (topLevelDecl is ClassDecl) {
          var cd = topLevelDecl as ClassDecl;
          foreach (var member in cd.Members) {
            if ($"{cd.FullDafnyName}.{member.Name}" == funcName) {
              return member as Function;
            }
          }
        }
      }
      return null;
    }

    public static Function GetFunctionFromUnresolved(Program program, string funcName) {
      int index = funcName.LastIndexOf('.');
      string moduleName = funcName.Remove(index);
      foreach (var topLevelDecl in program.DefaultModuleDef.TopLevelDecls) {
        if (topLevelDecl.FullDafnyName == moduleName) {
          var lmd = topLevelDecl as LiteralModuleDecl;
          var func = GetFunctionFromModuleDef(lmd.ModuleDef, funcName);
          if (func != null) {
            return func;
          }
        }
      }
      return null;
    }

    public void DuplicateAllFiles(Program program, string workingDir, int cnt) {
      if (System.IO.Directory.Exists(workingDir)) {
        System.IO.Directory.Delete(workingDir, true);
      }
      System.IO.Directory.CreateDirectory(workingDir);
      var samples = new List<string>();
      samples.Add(includeParser.Normalized(program.FullName));
      System.IO.Directory.CreateDirectory(Path.GetDirectoryName($"{workingDir}/{samples[0]}"));
      File.Copy(program.FullName, $"{workingDir}/{samples[0]}", true);
      foreach (var file in program.DefaultModuleDef.Includes) {
        samples.Add(includeParser.Normalized(file.canonicalPath));
      }
      for (int i = 1; i < samples.Count; i++) {
        System.IO.Directory.CreateDirectory(Path.GetDirectoryName($"{workingDir}/{samples[i]}"));
        File.Copy(program.DefaultModuleDef.Includes[i - 1].canonicalPath, $"{workingDir}/{samples[i]}", true);
      }
    }

    private Function workingFunc = null;
    private Function workingConstraintFunc = null;
    private string[] workingFuncCode;
    private string constraintFuncCode = "";
    private int constraintFuncLineCount = 0;
    private List<string> mergedCode = new List<string>();

    public void CheckMaintainState(Program program, ExpressionFinder.ExpressionDepth exprDepth, int index) {
      var funcName = workingFunc.Name;
      int lemmaForMaintainStatePosition = -1;
      int lemmaForMaintainStateStartPosition = -1;

      var requestList = new List<VerificationRequest>();

      var workingDir = $"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}/{funcName}_{index}";
      if (tasksList == null) {
        throw new NotSupportedException();
      }
      else {
        var changedFilesList = new HashSet<string>();
        var changedPredicatesNamesDict = new Dictionary<string, string>();
        for(int i = 0; i < Paths[0].Count; i++) {
          changedFilesList.Add(includeParser.Normalized(Paths[0][i].Item1.BodyStartTok.filename));
          changedPredicatesNamesDict.Add(Paths[0][i].Item1.Name, "old_" + Paths[0][i].Item1.Name);
        }
        bool maintainLemmaAdded = false;
        foreach (var path in changedFilesList) {
          var code = File.ReadAllLines(includeParser.commonPrefix + "/" + path);
          if (workingConstraintFunc != null &&
              path == includeParser.Normalized(workingConstraintFunc.BodyStartTok.filename)) {
            maintainLemmaAdded = true;
            code[code.Length - 1] = code[code.Length - 1] + "\n" + lemmaForMaintainabilityString;
          }
          for(int i = 0; i < Paths[0].Count; i++) {
            // desiredFunctionUnresolved = GetFunctionFromUnresolved(unresolvedProgram, funcName);
            var func = GetFunctionFromUnresolved(program, Paths[0][i].Item1.FullDafnyName);
            Contract.Assert(func != null);
            if (includeParser.Normalized(func.tok.filename) == path) {
              for (int j = func.tok.line - 1; j < func.BodyEndTok.line; j++) {
                code[j] = "";
              }
              string newFunc = "";
              string oldFunc = "";
              if (func.Name == workingFunc.Name && 
                  func.tok.filename == workingFunc.tok.filename && 
                  func.tok.line == workingFunc.tok.line) {
                var clonedFunc = cloner.CloneFunction(func);
                if (exprDepth.expr.HasCardinality) {
                  clonedFunc.Body = Expression.CreateAnd(clonedFunc.Body, exprDepth.expr);
                } else {
                  clonedFunc.Body = Expression.CreateAnd(exprDepth.expr, clonedFunc.Body);
                }
                using (var wr = new System.IO.StringWriter()) {
                  var pr = new Printer(wr, DafnyOptions.PrintModes.DllEmbed);
                  pr.UniqueStringBeforeUnderscore = UnderscoreStr;
                  pr.PrintFunction(clonedFunc, 0, false);
                  newFunc = Printer.ToStringWithoutNewline(wr);
                }
              }
              else {
                using (var wr = new System.IO.StringWriter()) {
                  var pr = new Printer(wr, DafnyOptions.PrintModes.DllEmbed);
                  pr.UniqueStringBeforeUnderscore = UnderscoreStr;
                  pr.PrintFunction(func, 0, false);
                  newFunc = Printer.ToStringWithoutNewline(wr);
                }
              }
              using (var wr = new System.IO.StringWriter()) {
                var pr = new Printer(wr, DafnyOptions.PrintModes.DllEmbed);
                pr.UniqueStringBeforeUnderscore = UnderscoreStr;
                pr.ChangedPredicatesDict = changedPredicatesNamesDict;
                // pr.ModuleForTypes = currentModuleDef;
                pr.PrintFunction(func, 0, false);
                oldFunc = Printer.ToStringWithoutNewline(wr);
              }
              code[func.tok.line - 1] = newFunc + "\n" + oldFunc;
            }
          }
          var request = dafnyVerifier.GetFileRewriteRequest(String.Join('\n', code), exprDepth, index, path);
          requestList.Add(request);
        }
        var constraintFuncPath = includeParser.Normalized(workingConstraintFunc.BodyStartTok.filename);
        if (!maintainLemmaAdded) {
          for (int i = 0; i < requestList.Count; i++) {
            if (requestList[i].Path == constraintFuncPath) {
              lemmaForMaintainStateStartPosition = requestList[i].Code.Count(f => (f == '\n')) + 2;
              // requestList[i].Code = requestList[i].Code + "\n" + lemmaForMaintainabilityString;
              var lastBraceLocation = requestList[i].Code.Length - 1;
              while (lastBraceLocation > 0 && requestList[i].Code[lastBraceLocation] != '}') {
                lastBraceLocation--;
              }
              requestList[i].Code = requestList[i].Code.Remove(lastBraceLocation - 1) + "\n" + lemmaForMaintainabilityString + "\n}";
              lemmaForMaintainStatePosition = lemmaForMaintainStateStartPosition + lemmaForMaintainabilityLineCount;
              foreach (var arg in tasksListDictionary[constraintFuncPath].Arguments.ToList()) {
                requestList[i].Arguments.Add(arg);
              }
              requestList[i].Arguments.Add("/proc:*maintainCheck*");
              dafnyVerifier.requestToPostConditionPosition[requestList[i]] = lemmaForMaintainStatePosition;
              dafnyVerifier.requestToLemmaStartPosition[requestList[i]] = lemmaForMaintainStateStartPosition;
              maintainLemmaAdded = true;
              break;
            }
          }
          if (!maintainLemmaAdded && workingConstraintFunc != null) {
            maintainLemmaAdded = true;

            lemmaForMaintainStateStartPosition = constraintFuncLineCount + 2;
            var newBaseCode = constraintFuncCode + "\n" + lemmaForMaintainabilityString;
            lemmaForMaintainStatePosition = lemmaForMaintainStateStartPosition + lemmaForMaintainabilityLineCount;
            var argList = tasksListDictionary[constraintFuncPath].Arguments.ToList();
            argList.Add("/proc:*maintainCheck*");
            requestList.Add(dafnyVerifier.GetVerificationRequest(
              newBaseCode, argList,
              exprDepth, index, lemmaForMaintainStatePosition, lemmaForMaintainStateStartPosition,
              constraintFuncPath));
          }
        }
        dafnyVerifier.runDafny(requestList, exprDepth, index);
      }
    }

    public void PrintExprAndCreateProcess(Program program, ExpressionFinder.ExpressionDepth exprDepth, int cnt) {
      bool runOnce = DafnyOptions.O.HoleEvaluatorRunOnce;
      if (cnt % 1000 == 1) {
        Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: {cnt}");
      }
      if (DafnyOptions.O.HoleEvaluatorVerboseMode) {
        Console.WriteLine($"{cnt} {Printer.ExprToString(exprDepth.expr)}\t\t{exprDepth.depth}");
      }
      var funcName = workingFunc.Name;

      int lemmaForExprValidityPosition = -1;
      int lemmaForExprValidityStartPosition = -1;

      var requestList = new List<VerificationRequest>();

      var workingDir = $"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}/{funcName}_{cnt}";
      if (tasksList == null) {
        string code = "";
        using (var wr = new System.IO.StringWriter()) {
          var pr = new Printer(wr, DafnyOptions.PrintModes.DllEmbed);
          pr.UniqueStringBeforeUnderscore = UnderscoreStr;
          if (exprDepth.expr.HasCardinality) {
            workingFunc.Body = Expression.CreateAnd(exprDepth.expr, workingFunc.Body);
          } else {
            workingFunc.Body = Expression.CreateAnd(workingFunc.Body, exprDepth.expr);
          }
          pr.PrintProgram(program, true);
          code = $"// #{cnt}\n";
          code += $"// {Printer.ExprToString(exprDepth.expr)}\n" + Printer.ToStringWithoutNewline(wr) + "\n\n";
          lemmaForExprValidityStartPosition = code.Count(f => f == '\n') + 1;
          code += lemmaForExprValidityString + "\n";
          lemmaForExprValidityPosition = code.Count(f => f == '\n');
          if (DafnyOptions.O.HoleEvaluatorCreateAuxFiles)
            File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{funcName}_{cnt}.dfy", code);
        }
        string env = DafnyOptions.O.Environment.Remove(0, 22);
        var argList = env.Split(' ');
        List<string> args = new List<string>();
        foreach (var arg in argList) {
          if (!arg.EndsWith(".dfy") && !arg.StartsWith("/holeEval") && arg.StartsWith("/")) {
            args.Add(arg);
          }
        }
        args.Add("/exitAfterFirstError");
        requestList.Add(dafnyVerifier.GetVerificationRequest(code, args,
            exprDepth, cnt, lemmaForExprValidityPosition, lemmaForExprValidityStartPosition, ""));
      } else {
        var changingFilePath = includeParser.Normalized(workingFunc.BodyStartTok.filename);
        string constraintFuncChangingFilePath = "";
        // var remoteFolderPath = dafnyVerifier.DuplicateAllFiles(cnt, changingFilePath);

        var clonedWorkingFunc = cloner.CloneFunction(workingFunc);
        if (exprDepth.expr.HasCardinality) {
          clonedWorkingFunc.Body = Expression.CreateAnd(exprDepth.expr, clonedWorkingFunc.Body);
        } else {
          clonedWorkingFunc.Body = Expression.CreateAnd(clonedWorkingFunc.Body, exprDepth.expr);
        }
        using (var wr = new System.IO.StringWriter()) {
          var pr = new Printer(wr, DafnyOptions.PrintModes.DllEmbed);
          pr.UniqueStringBeforeUnderscore = UnderscoreStr;
          pr.PrintFunction(clonedWorkingFunc, 0, false);
          mergedCode[1] = Printer.ToStringWithoutNewline(wr);
        }
        var newCode = String.Join('\n', mergedCode);

        if (constraintFuncCode != "") {
          constraintFuncChangingFilePath = includeParser.Normalized(workingConstraintFunc.BodyStartTok.filename);
          lemmaForExprValidityStartPosition = constraintFuncLineCount + 2;
          var newBaseCode = constraintFuncCode + "\n" + lemmaForExprValidityString;
          lemmaForExprValidityPosition = lemmaForExprValidityStartPosition + lemmaForExprValidityLineCount;
          requestList.Add(dafnyVerifier.GetVerificationRequest(
            newBaseCode, tasksListDictionary[constraintFuncChangingFilePath].Arguments.ToList(),
            exprDepth, cnt, lemmaForExprValidityPosition, lemmaForExprValidityStartPosition,
            constraintFuncChangingFilePath));

          requestList.Add(dafnyVerifier.GetVerificationRequest(
            newCode, tasksListDictionary[changingFilePath].Arguments.ToList(),
            exprDepth, cnt, -1, -1, changingFilePath));
        } else {
          var newCodeLineCount = newCode.Count(f => (f == '\n'));
          lemmaForExprValidityStartPosition = newCodeLineCount + 2;
          newCode += "\n" + lemmaForExprValidityString;
          lemmaForExprValidityPosition = newCodeLineCount + lemmaForExprValidityLineCount;
          requestList.Add(dafnyVerifier.GetVerificationRequest(
            newCode, tasksListDictionary[changingFilePath].Arguments.ToList(),
            exprDepth, cnt, lemmaForExprValidityPosition, lemmaForExprValidityStartPosition,
            changingFilePath));
        }

        // File.WriteAllTextAsync($"{workingDir}/{changingFilePath}", newCode);
        foreach (var f in affectedFiles) {
          if (f != changingFilePath && f != constraintFuncChangingFilePath) {
            // var code = File.ReadAllLines($"{workingDir}/{f}");
            requestList.Add(dafnyVerifier.GetVerificationRequest(
              "", tasksListDictionary[f].Arguments.ToList(),
              exprDepth, cnt, -1, -1, f));
          // } else {
            // dafnyVerifier.runDafny(String.Join('\n', code), tasksListDictionary[f].Arguments.ToList(),
            //   expr, cnt, lemmaForExprValidityPosition, lemmaForExprValidityStartPosition);
          }
        }
      }
      dafnyVerifier.runDafny(requestList, exprDepth, cnt);
    }

    public void PrintImplies(Program program, Function func, int availableExprAIndex, int availableExprBIndex) {
      // Console.WriteLine($"print implies {availableExprAIndex} {availableExprBIndex}");
      var funcName = func.FullDafnyName;
      var paramList = GetFunctionParamList(func);
      var parameterNameTypes = paramList.Item2;
      string lemmaForCheckingImpliesString = "lemma checkIfExprAImpliesExprB(";
      lemmaForCheckingImpliesString += parameterNameTypes + ")\n";
      Expression A = expressionFinder.availableExpressions[availableExprAIndex].expr;
      Expression B = expressionFinder.availableExpressions[availableExprBIndex].expr;
      lemmaForCheckingImpliesString += "  requires " + Printer.ExprToString(A) + "\n";
      lemmaForCheckingImpliesString += "  ensures " + Printer.ExprToString(B) + "\n";
      lemmaForCheckingImpliesString += "{}";

      int lemmaForCheckingImpliesPosition = 0;

      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr, DafnyOptions.PrintModes.DllEmbed);
        pr.UniqueStringBeforeUnderscore = UnderscoreStr;
        pr.PrintProgram(program, true);
        var code = $"// Implies {Printer.ExprToString(A)} ==> {Printer.ExprToString(B)}\n" + Printer.ToStringWithoutNewline(wr) + "\n\n";
        code += lemmaForCheckingImpliesString + "\n";
        lemmaForCheckingImpliesPosition = code.Count(f => f == '\n');
        File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{funcName}_implies_{availableExprAIndex}_{availableExprBIndex}.dfy", code);
      }

      string dafnyBinaryPath = System.Reflection.Assembly.GetEntryAssembly().Location;
      dafnyBinaryPath = dafnyBinaryPath.Substring(0, dafnyBinaryPath.Length - 4);
      string env = DafnyOptions.O.Environment.Remove(0, 22);
      var argList = env.Split(' ');
      string args = "";
      foreach (var arg in argList) {
        if (!arg.EndsWith(".dfy") && !arg.StartsWith("/holeEval") && !arg.StartsWith("/proc:") && args.StartsWith("/")) {
          args += arg + " ";
        }
      }
      dafnyImpliesExecutor.createProcessWithOutput(dafnyBinaryPath,
        $"{args} {DafnyOptions.O.HoleEvaluatorWorkingDirectory}{funcName}_implies_{availableExprAIndex}_{availableExprBIndex}.dfy /proc:Impl*checkIfExprAImpliesExprB*",
        availableExprAIndex, availableExprBIndex, -1, lemmaForCheckingImpliesPosition,
        $"{funcName}_implies_{availableExprAIndex}_{availableExprBIndex}.dfy");
    }

  }
}

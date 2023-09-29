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
  public class ExpressionFinder {

    private int prevDepthExprStartIndex = 1;
    private int numberOfSingleExpr = 0;
    private HoleEvaluator holeEval = null;
    private ProofEvaluator proofEval = null;
    public List<ExpressionDepth> availableExpressions = new List<ExpressionDepth>();
    private List<BitArray> bitArrayList = new List<BitArray>();
    private HashSet<string> currCombinations = new HashSet<string>();
    private Dictionary<string, int> bitArrayStringToIndex = new Dictionary<string, int>();
    public Dictionary<int, Result> combinationResults = new Dictionary<int, Result>();
    private Dictionary<int, int> negateOfExpressionIndex = new Dictionary<int, int>();

    public class ExpressionDepth {
      public Expression expr;
      public int depth;
      public ExpressionDepth(Expression expr, int depth) 
      {
        this.expr = expr;
        this.depth = depth;
      }
    }

    public class StatementDepth {
      public Statement stmt;
      public int depth;
      public StatementDepth(Statement stmt, int depth) 
      {
        this.stmt = stmt;
        this.depth = depth;
      }
    }

    public ExpressionFinder(HoleEvaluator holeEval) {
      this.holeEval = holeEval;
    }
    public ExpressionFinder(ProofEvaluator proofEval) {
      this.proofEval = proofEval;
    }

    private string ToBitString(BitArray bits, bool skipZero) {
      var sb = new StringBuilder();

      for (int i = skipZero ? 1 : 0; i < bits.Count; i++) {
        char c = bits[i] ? '1' : '0';
        sb.Append(c);
      }

      return sb.ToString();
    }

    public void Increment(ref BitArray bArray) {
      for (int i = 0; i < bArray.Count; i++) {
        bool previous = bArray[i];
        bArray[i] = !previous;
        if (!previous) {
          // Found a clear bit - now that we've set it, we're done
          return;
        }
      }
    }

    public bool IsGoodExprCombinationToExecute(int indexI, int indexJ) {
      Contract.Requires(indexI >= 0 && indexI < availableExpressions.Count);
      Contract.Requires(indexJ >= 0 && indexJ < availableExpressions.Count);
      if ((!HoleEvaluator.IsGoodResult(combinationResults[indexI])) ||
          (!HoleEvaluator.IsGoodResult(combinationResults[indexJ]))) {
        return false;
      }
      BitArray combinedBitArray = new BitArray(bitArrayList[indexI]);
      combinedBitArray.Or(bitArrayList[indexJ]);

      // Check if the combination is same as input combinations or not
      if (combinedBitArray.Equals(bitArrayList[indexI]) || combinedBitArray.Equals(bitArrayList[indexJ])) {
        return false;
      }
      // Check if this combination has been already executed or not
      if (currCombinations.Contains(ToBitString(combinedBitArray, true))) {
        return false;
      }
      // Check if negate of an expression also exists in this expr combination or not.
      List<int> enabledExprIndexes = new List<int>();
      for (int i = 0; i < combinedBitArray.Count; i++) {
        if (combinedBitArray[i]) {
          enabledExprIndexes.Add(i);
          if (negateOfExpressionIndex.ContainsKey(i)) {
            var negateIndex = negateOfExpressionIndex[i];
            if (combinedBitArray[negateIndex])
              return false;
          }
        }
      }
      BitArray countBitArray = new BitArray(enabledExprIndexes.Count, false);
      countBitArray[0] = true;
      BitArray zeroBitArray = new BitArray(enabledExprIndexes.Count, false);
      while (ToBitString(countBitArray, false) != ToBitString(zeroBitArray, false)) {
        BitArray subsetBitArray = new BitArray(combinedBitArray.Count, false);
        for (int i = 0; i < enabledExprIndexes.Count; i++) {
          subsetBitArray[enabledExprIndexes[i]] = countBitArray[i];
        }
        string subsetString = ToBitString(subsetBitArray, true);
        // Console.WriteLine($"{indexI} {indexJ} {subsetString}");
        // Console.WriteLine($"{ToBitString(countBitArray)} {ToBitString(zeroBitArray)} {countBitArray.Equals(zeroBitArray)}");
        if (bitArrayStringToIndex.ContainsKey(subsetString)) {
          int index = bitArrayStringToIndex[subsetString];
          if (!HoleEvaluator.IsGoodResult(combinationResults[index]))
            return false;
        }
        Increment(ref countBitArray);
      }
      return true;
    }

    public string GetCollectionName(Expression expr) {
      if (expr is BinaryExpr) {
        return GetCollectionName((expr as BinaryExpr).E0);
      }
      else if (expr.Type.AsCollectionType == null) {
        return Printer.ExprToString(expr);
      } else {
        if (expr is SeqSelectExpr) {
          return GetCollectionName((expr as SeqSelectExpr).Seq);
        } else if (expr is MultiSelectExpr) {
          return GetCollectionName((expr as MultiSelectExpr).Array);
        }
        else {
          return Printer.ExprToString(expr);
        }
      }
    }

    public IEnumerable<ExpressionDepth> ExtendFunctionInvocationExpressions(Program program, IEnumerable<ExpressionDepth> expressionList) {
      foreach (var exprDepth in expressionList) {
        yield return exprDepth;
      }
      var typeToExpressionDict = GetTypeToExpressionDict(expressionList);
      foreach (var kvp in program.ModuleSigs) {
        foreach (var d in kvp.Value.ModuleDef.TopLevelDecls) {
          var cl = d as TopLevelDeclWithMembers;
          if (cl != null) {
            foreach (var member in cl.Members) {
              if (member is Function) {
                var functionInvocations = GetAllPossibleFunctionInvocations(program, member as Function, typeToExpressionDict);
                foreach (var invocation in functionInvocations) {
                  yield return invocation;
                }
              } else if (member is Predicate) {
                var predicateInvocations = GetAllPossiblePredicateInvocations(program, member as Predicate, typeToExpressionDict);
                foreach (var invocation in predicateInvocations) {
                  yield return invocation;
                }
              }
            }
          }
        }
      }
    }

    public IEnumerable<ExpressionDepth> ExtendInSeqExpressions(IEnumerable<ExpressionDepth> expressionList) {
      int maxEvalDepth = DafnyOptions.O.HoleEvaluatorExpressionDepth;
      foreach (var exprDepth in expressionList) {
        yield return exprDepth;
      }
      var typeToExpressionDict = GetTypeToExpressionDict(expressionList);
      foreach (var typeExprListTuple in typeToExpressionDict) {
        var typeStr = typeExprListTuple.Key;
        var exprHashSet = typeExprListTuple.Value;
        var exprHashSetAny = exprHashSet.Where(x => true).FirstOrDefault();
        if (exprHashSetAny.expr.Type.AsCollectionType != null) {
          var collectionElementType = exprHashSetAny.expr.Type.AsCollectionType.Arg;
          collectionElementType = LemmaFinder.SubstituteTypeWithSynonyms(collectionElementType);
          if (typeToExpressionDict.ContainsKey(collectionElementType.ToString())) {
            foreach (var elem in typeToExpressionDict[collectionElementType.ToString()]) {
              if (elem.depth + 1 > maxEvalDepth) {
                continue;
              }
              foreach (var collection in exprHashSet) {
                if (collection.depth + 1 > maxEvalDepth) {
                   continue;
                }
                if (!(collection.expr is FunctionCallExpr)) {
                  var InExpr = new BinaryExpr(elem.expr.tok, BinaryExpr.Opcode.In, elem.expr, collection.expr);
                    InExpr.Type = Type.Bool;
                  yield return new ExpressionDepth(InExpr, Math.Max(collection.depth, elem.depth) + 1);
                }
              }
            }
          }
        }
      }
    }

    public IEnumerable<ExpressionDepth> ExtendSeqSelectExpressions(IEnumerable<ExpressionDepth> expressionList) {
      // Console.WriteLine("here");
      int maxEvalDepth = DafnyOptions.O.HoleEvaluatorExpressionDepth;
      foreach (var exprDepth in expressionList) {
        yield return exprDepth;
      }
      var typeToExpressionDict = GetTypeToExpressionDict(expressionList);
      if (typeToExpressionDict.ContainsKey("int")) {
        var intVarHashSet = typeToExpressionDict["int"];
        foreach (var type in typeToExpressionDict.Keys) {
          var firstElem = typeToExpressionDict[type].Where(x => true).FirstOrDefault();
          if (firstElem.expr.Type is SeqType) {
            var seqVarHashSet = typeToExpressionDict[type];
            foreach (var seqVar in seqVarHashSet) {
              if (seqVar.depth + 1 > maxEvalDepth) {
                continue;
              }
            // for (int i = 0; i < seqVarList.Count; i++) {
              // var seqVar = seqVarList[i];
              foreach (var intVar in intVarHashSet) {
                if (intVar.depth + 1 > maxEvalDepth) {
                  continue;
                }
              // for (int j = 0; j < intVarList.Count; j++) {
                var seqSelectExpr = new SeqSelectExpr(seqVar.expr.tok, true, seqVar.expr, intVar.expr, null);
                seqSelectExpr.Type = (seqVar.expr.Type as SeqType).Arg;
                yield return new ExpressionDepth(seqSelectExpr, Math.Max(seqVar.depth, intVar.depth) + 1);
              }
            }
          }
        }
      }
      yield break;
    }

    public void CalcDepthOneAvailableExpresssionsFromFunction(Program program, Function desiredFunction) {
      Contract.Requires(desiredFunction != null);
      Contract.Requires(availableExpressions.Count == 0);
      var expressions = ListArguments(program, desiredFunction);
      var extendedSeqSelectExpressions = ExtendSeqSelectExpressions(expressions);
      if (DafnyOptions.O.HoleEvaluatorIncludeFunctionInvocations) {
        var extendedFunctionInvocationsExpressions = ExtendFunctionInvocationExpressions(program, extendedSeqSelectExpressions);
        var extendedExpressions = ExtendInSeqExpressions(extendedFunctionInvocationsExpressions);
        CalcDepthOneAvailableExpresssions(program, desiredFunction, extendedExpressions);
      }
      else {
        var extendedExpressions = ExtendInSeqExpressions(extendedSeqSelectExpressions);
        CalcDepthOneAvailableExpresssions(program, desiredFunction, extendedExpressions);
      }
    }

    public void CalcDepthOneAvailableExpresssionsFromLemma(Program program, Lemma desiredLemma) {
      Contract.Requires(desiredLemma != null);
      Contract.Requires(availableExpressions.Count == 0);
      var expressions = ListArguments(program, desiredLemma);
      var extendedExpressions = ExtendSeqSelectExpressions(expressions);
      CalcDepthOneAvailableExpresssions(program, desiredLemma, extendedExpressions);
    }

    public Dictionary<string, HashSet<ExpressionDepth>> GetTypeToExpressionDict(IEnumerable<ExpressionDepth> expressionList) {
      int maxEvalDepth = DafnyOptions.O.HoleEvaluatorExpressionDepth;
      Dictionary<string, HashSet<ExpressionDepth>> typeToExpressionDict = new Dictionary<string, HashSet<ExpressionDepth>>();
      foreach (var exprDepth in expressionList) {
        var expr = exprDepth.expr;
        var exprString = Printer.ExprToString(expr);
        var typeString = expr.Type.ToString();
        // Console.WriteLine($"{c,2} {exprString,-20} {typeString}");
        if (expr.Type == Type.Bool && exprString[exprString.Length - 1] == '?') {
          typeString = "_questionMark_";
        }
        if (typeToExpressionDict.ContainsKey(typeString)) {
          // bool containsItem = typeToExpressionDict[typeString].Any(
          //      item => Printer.ExprToString(item.expr) == Printer.ExprToString(expr));
          // if (!containsItem) {
          typeToExpressionDict[typeString].Add(exprDepth);
          // }
        } else {
          var lst = new HashSet<ExpressionDepth>();
          lst.Add(exprDepth);
          typeToExpressionDict.Add(typeString, lst);
        }
        // AddExpression(program, topLevelDecl, expr);
      }
      return typeToExpressionDict;
    }

    public Dictionary<string, HashSet<ExpressionDepth>> GetRawExpressions(Program program, MemberDecl decl,
        IEnumerable<ExpressionDepth> expressions, bool addToAvailableExpressions) {
      var typeToExpressionDict = GetTypeToExpressionDict(expressions);
      // foreach (var kvp in program.ModuleSigs) {
      //   foreach (var d in kvp.Value.ModuleDef.TopLevelDecls) {
      //     var cl = d as TopLevelDeclWithMembers;
      //     if (cl != null) {
      //       foreach (var member in cl.Members) {
      //         if (member is Predicate) {
      //           var predicateInvocations = GetAllPossiblePredicateInvocations(program, member as Predicate, typeToExpressionDict);
      //           if (!typeToExpressionDict.ContainsKey("bool")) {
      //             typeToExpressionDict.Add("bool", new HashSet<ExpressionDepth>());
      //           }
      //           typeToExpressionDict["bool"].UnionWith(predicateInvocations);
      //         }
      //       }
      //     }
      //   }
      // }
      if (decl is Function) {
        var desiredFunction = decl as Function;
        var equalExprToCheck = desiredFunction.Body;
        foreach (var e in desiredFunction.Req) {
          equalExprToCheck = Expression.CreateAnd(equalExprToCheck, e.E);
        }
        Dictionary<string, List<string>> equalExprList = GetEqualExpressionList(equalExprToCheck);
        foreach (var k in equalExprList.Keys) {
          var t = equalExprList[k][0];
          if (typeToExpressionDict.ContainsKey(t)) {
            for (int i = 1; i < equalExprList[k].Count; i++) {
              foreach (var e in typeToExpressionDict[t]) {
              // for (int j = 0; j < typeToExpressionDict[t].Count; j++) {
                if (Printer.ExprToString(e.expr) == equalExprList[k][i]) {
                  typeToExpressionDict[t].Remove(e);
                  break;
                }
              }
            }
          }
        }
      }
      if (addToAvailableExpressions) {
        foreach (var t in typeToExpressionDict) {
          foreach (var e in t.Value) {
            availableExpressions.Add(e);
          }
        }
      }
      return typeToExpressionDict;
    }

    public void CalcDepthOneAvailableExpresssions(Program program, MemberDecl decl, IEnumerable<ExpressionDepth> expressions) {
      Contract.Requires(availableExpressions.Count == 0);
      Dictionary<string, HashSet<ExpressionDepth>> typeToExpressionDict = GetRawExpressions(program, decl, expressions, false);

      var trueExpr = Expression.CreateBoolLiteral(decl.tok, true);
      availableExpressions.Add(new ExpressionDepth(trueExpr, 1));
      foreach (var k in typeToExpressionDict.Keys) {
        var values = typeToExpressionDict[k].ToList();
        if (k == "_questionMark_") {
          foreach (var expr in values) {
            // No change to the type, add as is
            availableExpressions.Add(expr);
          }
        } else {
          for (int i = 0; i < values.Count; i++) {
            if (k == "bool") {
              availableExpressions.Add(new ExpressionDepth(values[i].expr, values[i].depth));
              continue;
            }
            for (int j = i + 1; j < values.Count; j++) {
              if (values[i].expr is LiteralExpr && values[j].expr is LiteralExpr) {
                continue;
              }
              if (values[i].expr is ApplySuffix && values[j].expr is ApplySuffix) {
                continue;
              }
              // Equality
              {
                var equalityExpr = Expression.CreateEq(values[i].expr, values[j].expr, values[i].expr.Type);
                equalityExpr.HasCardinality = values[i].expr.HasCardinality | values[j].expr.HasCardinality;
                availableExpressions.Add(new ExpressionDepth(equalityExpr, Math.Max(values[i].depth, values[j].depth)));
              }
              if (values[i].expr is ApplySuffix || values[j].expr is ApplySuffix) {
                continue;
              }
              // Non-Equality
              {
                var neqExpr = Expression.CreateNot(values[i].expr.tok, Expression.CreateEq(values[i].expr, values[j].expr, values[i].expr.Type));
                neqExpr.HasCardinality = values[i].expr.HasCardinality | values[j].expr.HasCardinality;
                availableExpressions.Add(new ExpressionDepth(neqExpr, Math.Max(values[i].depth, values[j].depth)));
                negateOfExpressionIndex[availableExpressions.Count - 1] = availableExpressions.Count - 2;
                negateOfExpressionIndex[availableExpressions.Count - 2] = availableExpressions.Count - 1;
              }

              // only check < <= => > for int and nat types
              if (k != "int" && k != "nat") {
                continue;
              }
              // Lower than
              {
                if (k != "nat" || (Printer.ExprToString(values[j].expr) != "0" && Printer.ExprToString(values[j].expr) != "1")) {
                  var lowerThanExpr = Expression.CreateLess(values[i].expr, values[j].expr);
                  lowerThanExpr.HasCardinality = values[i].expr.HasCardinality | values[j].expr.HasCardinality;
                  availableExpressions.Add(new ExpressionDepth(lowerThanExpr, Math.Max(values[i].depth, values[j].  depth)));
                }
              }
              // Greater Equal = !(Lower than)
              {
                if (k != "nat" || (Printer.ExprToString(values[i].expr) != "0" && Printer.ExprToString(values[i].expr) != "1")) {
                  var geExpr = Expression.CreateNot(values[i].expr.tok, Expression.CreateLess(values[i].expr, values[j].expr));
                  geExpr.HasCardinality = values[i].expr.HasCardinality | values[j].expr.HasCardinality;
                  availableExpressions.Add(new ExpressionDepth(geExpr, Math.Max(values[i].depth, values[j].depth)));
                  negateOfExpressionIndex[availableExpressions.Count - 1] = availableExpressions.Count - 2;
                  negateOfExpressionIndex[availableExpressions.Count - 2] = availableExpressions.Count - 1;
                }
              }
              // Lower Equal
              {
                if (k != "nat" || (Printer.ExprToString(values[j].expr) != "0" && Printer.ExprToString(values[j].expr) != "1" && Printer.ExprToString(values[i].expr) != "0" && Printer.ExprToString(values[i].expr) != "1")) {
                  var leExpr = Expression.CreateAtMost(values[i].expr, values[j].expr);
                  leExpr.HasCardinality = values[i].expr.HasCardinality | values[j].expr.HasCardinality;
                  availableExpressions.Add(new ExpressionDepth(leExpr, Math.Max(values[i].depth, values[j].depth)));
                }
              }
              // Greater Than = !(Lower equal)
              {
                if (k != "nat" || (Printer.ExprToString(values[i].expr) != "0" && Printer.ExprToString(values[i].expr) != "1")) {
                  var gtExpr = Expression.CreateNot(values[i].expr.tok, Expression.CreateAtMost(values[i].expr, values[j].expr));
                  gtExpr.HasCardinality = values[i].expr.HasCardinality | values[j].expr.HasCardinality;
                  availableExpressions.Add(new ExpressionDepth(gtExpr, Math.Max(values[i].depth, values[j].depth)));
                  negateOfExpressionIndex[availableExpressions.Count - 1] = availableExpressions.Count - 2;
                  negateOfExpressionIndex[availableExpressions.Count - 2] = availableExpressions.Count - 1;
                }
              }
            }
          }
        }
      }
      numberOfSingleExpr = availableExpressions.Count;
      if (DafnyOptions.O.HoleEvaluatorDepth > 1) {
        for (int i = 0; i < numberOfSingleExpr; i++) {
          BitArray bitArray = new BitArray(availableExpressions.Count, false);
          bitArray[i] = true;
          bitArrayList.Add(bitArray);
          if (i == 0) {
            currCombinations.Add(ToBitString(bitArray, false));
            bitArrayStringToIndex[ToBitString(bitArray, false)] = i;
          } else {
            currCombinations.Add(ToBitString(bitArray, true));
            bitArrayStringToIndex[ToBitString(bitArray, true)] = i;
          }
        }
      }
    }

    public void CalcNextDepthAvailableExpressions() {
      // Until here, we only check depth 1 of expressions.
      // Now we try to check next depths
      var tmp = availableExpressions.Count;
      for (int i = prevDepthExprStartIndex; i < tmp; i++) {
        for (int j = 1; j < numberOfSingleExpr; j++) {
          if (IsGoodExprCombinationToExecute(i, j)) {
            var exprDepthA = availableExpressions[i];
            var exprDepthB = availableExpressions[j];
            var exprA = exprDepthA.expr;
            var exprB = exprDepthA.expr;
            var conjunctExpr = Expression.CreateAnd(exprA, exprB);
            conjunctExpr.HasCardinality = exprA.HasCardinality | exprB.HasCardinality;
            BitArray bitArray = new BitArray(bitArrayList[i]);
            bitArray.Or(bitArrayList[j]);
            bitArrayList.Add(bitArray);
            currCombinations.Add(ToBitString(bitArray, true));
            bitArrayStringToIndex[ToBitString(bitArray, true)] = bitArrayList.Count - 1;
            availableExpressions.Add(new ExpressionDepth(conjunctExpr, Math.Max(exprDepthA.depth, exprDepthB.depth)));
          }
        }
      }
      prevDepthExprStartIndex = tmp;
      return;
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

    public static IEnumerable<Expression> ListConstructors(
        Type ty,
        DatatypeCtor ctor,
        Dictionary<string, List<Expression>> typeToExpressionDict,
        List<Expression> arguments,
        int shouldFillIndex) {
      if (shouldFillIndex == ctor.Formals.Count) {
        List<ActualBinding> bindings = new List<ActualBinding>();
        foreach (var arg in arguments) {
          bindings.Add(new ActualBinding(null, arg));
        }
        var applySuffixExpr = new ApplySuffix(ctor.tok, null, new NameSegment(ctor.tok, ctor.Name, null), bindings, ctor.tok);
        applySuffixExpr.Type = ty;
        yield return applySuffixExpr;
        yield break;
      }
      var t = ctor.Formals[shouldFillIndex].Type;
      if (typeToExpressionDict.ContainsKey(t.ToString())) {
        foreach (var expr in typeToExpressionDict[t.ToString()]) {
          arguments.Add(expr);
          foreach (var ans in ListConstructors(ty, ctor, typeToExpressionDict, arguments, shouldFillIndex + 1)) {
            yield return ans;
          }
          arguments.RemoveAt(arguments.Count - 1);
        }
      }
    }

    public static List<Expression> GetAllPossibleConstructors(Program program,
      Type ty,
      DatatypeCtor ctor,
      Dictionary<string, List<Expression>> typeToExpressionDict) {
      List<Expression> result = new List<Expression>();
      List<Expression> workingList = new List<Expression>();
      foreach (var expr in ListConstructors(ty, ctor, typeToExpressionDict, workingList, 0)) {
        result.Add(expr);
      }
      return result;
    }

    public static IEnumerable<ExpressionDepth> ListFunctionInvocations(
        Function func,
        Dictionary<string, HashSet<ExpressionDepth>> typeToExpressionDict,
        List<ExpressionDepth> arguments,
        int shouldFillIndex) {
      if (shouldFillIndex == func.Formals.Count) {
        List<ActualBinding> bindings = new List<ActualBinding>();
        var depth = 0;
        foreach (var arg in arguments) {
          bindings.Add(new ActualBinding(null, arg.expr));
          depth = Math.Max(depth, arg.depth);
        }
        var funcCallExpr = new FunctionCallExpr(func.tok, func.FullDafnyName, new ImplicitThisExpr(func.tok), func.tok, bindings);
        funcCallExpr.Type = func.ResultType;
        yield return new ExpressionDepth(funcCallExpr, depth);
        yield break;
      }
      var t = func.Formals[shouldFillIndex].Type;
      if (typeToExpressionDict.ContainsKey(t.ToString())) {
        foreach (var expr in typeToExpressionDict[t.ToString()]) {
          arguments.Add(expr);
          foreach (var ans in ListFunctionInvocations(func, typeToExpressionDict, arguments, shouldFillIndex + 1)) {
            yield return ans;
          }
          arguments.RemoveAt(arguments.Count - 1);
        }
      }
    }

    public static List<ExpressionDepth> GetAllPossibleFunctionInvocations(Program program,
        Function func,
        Dictionary<string, HashSet<ExpressionDepth>> typeToExpressionDict) {
      List<ExpressionDepth> result = new List<ExpressionDepth>();
      List<ExpressionDepth> workingList = new List<ExpressionDepth>();
      foreach (var expr in ListFunctionInvocations(func, typeToExpressionDict, workingList, 0)) {
        result.Add(expr);
      }
      return result;
    }

    public static IEnumerable<ExpressionDepth> ListPredicateInvocations(
        Predicate func,
        Dictionary<string, HashSet<ExpressionDepth>> typeToExpressionDict,
        List<ExpressionDepth> arguments,
        int shouldFillIndex) {
      if (shouldFillIndex == func.Formals.Count) {
        List<ActualBinding> bindings = new List<ActualBinding>();
        var depth = 0;
        foreach (var arg in arguments) {
          bindings.Add(new ActualBinding(null, arg.expr));
          depth = Math.Max(depth, arg.depth);
        }
        var applySuffixExpr = new ApplySuffix(func.tok, null, new IdentifierExpr(func.tok, func.FullDafnyName), bindings, func.tok);
        applySuffixExpr.Type = func.ResultType;
        yield return new ExpressionDepth(applySuffixExpr, depth);
        yield break;
      }
      var t = func.Formals[shouldFillIndex].Type;
      if (typeToExpressionDict.ContainsKey(t.ToString())) {
        foreach (var expr in typeToExpressionDict[t.ToString()]) {
          arguments.Add(expr);
          foreach (var ans in ListPredicateInvocations(func, typeToExpressionDict, arguments, shouldFillIndex + 1)) {
            yield return ans;
          }
          arguments.RemoveAt(arguments.Count - 1);
        }
      }
    }

    public static HashSet<ExpressionDepth> GetAllPossiblePredicateInvocations(Program program,
        Predicate func,
        Dictionary<string, HashSet<ExpressionDepth>> typeToExpressionDict) {
      HashSet<ExpressionDepth> result = new HashSet<ExpressionDepth>();
      List<ExpressionDepth> workingList = new List<ExpressionDepth>();
      foreach (var expr in ListPredicateInvocations(func, typeToExpressionDict, workingList, 0)) {
        result.Add(expr);
      }
      return result;
    }

    public IEnumerable<ExpressionDepth> ListArguments(Program program, Function func) {
      foreach (var formal in func.Formals) {
        // Console.WriteLine($"\n{formal.Name}\t{formal.Type.ToString()}");
        // Console.WriteLine(formal.Type.NormalizeExpand().IsTopLevelTypeWithMembers);
        // var c = 0;
        var identExpr = Expression.CreateIdentExpr(formal);
        foreach (var expr in TraverseFormal(program, new ExpressionDepth(identExpr, 1))) {
          // Console.WriteLine($"{c} {variable.Name,-20}:\t{variable.Type}");
          // c++;
          yield return expr;
        }

      }
    }

    public IEnumerable<ExpressionDepth> ListArguments(Program program, Statement stmt) {
      if (stmt is null || stmt.Tok.line > DafnyOptions.O.ProofEvaluatorInsertionPoint) {
        yield break;
      }
      if (stmt is BlockStmt) {
        foreach (var s in (stmt as BlockStmt).Body) {
          foreach (var exprDepth in ListArguments(program, s)) {
            yield return exprDepth;
          }
        }
      }
      else if (stmt is IfStmt) {
        var ifStmt = stmt as IfStmt;
        foreach (var s in ifStmt.Thn.Body) {
          foreach (var exprDepth in ListArguments(program, s)) {
            yield return exprDepth;
          }
        }
        foreach (var exprDepth in ListArguments(program, ifStmt.Els)) {
          yield return exprDepth;
        }
      }
      else if (stmt is VarDeclStmt) {
        var varDecl = stmt as VarDeclStmt;
        var identExpr = Expression.CreateIdentExpr(varDecl.Locals[0]);
        foreach (var exprDepth in TraverseFormal(program, new ExpressionDepth(identExpr, 1))) {
          yield return exprDepth;
        }
      }
      else if (stmt is ForallStmt) {
        var forallStmt = stmt as ForallStmt;
        foreach (var exprDepth in ListArguments(program, forallStmt.Body)) {
          yield return exprDepth;
        }
        foreach (var boundVar in forallStmt.BoundVars) {
          var identExpr = Expression.CreateIdentExpr(boundVar);
          foreach (var exprDepth in TraverseFormal(program, new ExpressionDepth(identExpr, 1))) {
            yield return exprDepth;
          }
        }
      }
    }

    public IEnumerable<ExpressionDepth> ListArguments(Program program, Lemma lemma) {
      foreach (var formal in lemma.Ins) {
        var identExpr = Expression.CreateIdentExpr(formal);
        foreach (var expr in TraverseFormal(program, new ExpressionDepth(identExpr, 1))) {
          yield return expr;
        }
      }
      foreach (var formal in lemma.Outs) {
        var identExpr = Expression.CreateIdentExpr(formal);
        foreach (var expr in TraverseFormal(program, new ExpressionDepth(identExpr, 1))) {
          yield return expr;
        }
      }
      foreach (var exprDepth in ListArguments(program, lemma.Body)) {
        yield return exprDepth;
      }
    }

    public IEnumerable<ExpressionDepth> TraverseFormal(Program program, ExpressionDepth exprDepth) {
      Contract.Requires(exprDepth != null);
      var maxExpressionDepth = DafnyOptions.O.HoleEvaluatorExpressionDepth;
      if (exprDepth.depth > maxExpressionDepth)
        yield break;
      yield return exprDepth;
      var expr = exprDepth.expr;
      var t = expr.Type;
      if (t is BoolType || t is CharType || t is IntType || t is BigOrdinalType ||
          t is RealType || t is BitvectorType || t is CollectionType) {
        if (t is BoolType) {
          var trueLiteralExpr = Expression.CreateBoolLiteral(expr.tok, true);
          yield return new ExpressionDepth(trueLiteralExpr, 1);
          // NOTE: No need to add false literal since we also check for non-equality.
        } else if (t is IntType) {
          var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
          yield return new ExpressionDepth(zeroLiteralExpr, 1);
          var oneLiteralExpr = Expression.CreateIntLiteral(expr.tok, 1);
          yield return new ExpressionDepth(oneLiteralExpr, 1);
          
          var plusOneLiteralExpr = Expression.CreateIncrement(expr, 1);
          yield return new ExpressionDepth(plusOneLiteralExpr, exprDepth.depth);
          var minusOneLiteralExpr = Expression.CreateDecrement(expr, 1);
          yield return new ExpressionDepth(minusOneLiteralExpr, exprDepth.depth);
        } else if (t is CollectionType) {
          // create cardinality
          var cardinalityExpr = Expression.CreateCardinality(expr, program.BuiltIns);
          yield return new ExpressionDepth(cardinalityExpr, exprDepth.depth);
          {
            var zeroLiteralExpr = Expression.CreateNatLiteral(expr.tok, 0, Type.Nat());
            yield return new ExpressionDepth(zeroLiteralExpr, 1);
            var oneLiteralExpr = Expression.CreateNatLiteral(expr.tok, 1, Type.Nat());
            yield return new ExpressionDepth(oneLiteralExpr, 1);
          }
          if (exprDepth.depth + 1 <= maxExpressionDepth) {
            
            var cardinalityMinusOneExpr = Expression.CreateDecrement(cardinalityExpr, 1);
            yield return new ExpressionDepth(cardinalityMinusOneExpr, exprDepth.depth + 1);
            
            var cardinalityMinusTwoExpr = Expression.CreateDecrement(cardinalityExpr, 2);
            yield return new ExpressionDepth(cardinalityMinusTwoExpr, exprDepth.depth + 1);
          }
          if (t is SeqType) {
            {
              // create 0th element of a sequence
              var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
              var zerothElement = new SeqSelectExpr(expr.tok, true, expr, zeroLiteralExpr, null);
              var st = t as SeqType;
              zerothElement.Type = st.Arg;
              foreach (var e in TraverseFormal(program, new ExpressionDepth(zerothElement, exprDepth.depth + 1))) {
                yield return e;
              }
            }

            {
              // create last element of a sequence
              var lastElementExpr = Expression.CreateDecrement(cardinalityExpr, 1);
              var lastElement = new SeqSelectExpr(expr.tok, true, expr, lastElementExpr, null);
              lastElement.Type = (t as SeqType).Arg;
              foreach (var e in TraverseFormal(program, new ExpressionDepth(lastElement, exprDepth.depth + 1))) {
                yield return e;
              }
            }

            if (exprDepth.depth < maxExpressionDepth)
            {
              {
                // create DropFirst of a sequence
                var oneLiteralExpr = Expression.CreateIntLiteral(expr.tok, 1);
                var dropFirstElement = new SeqSelectExpr(expr.tok, false, expr, oneLiteralExpr, null);
                dropFirstElement.Type = t;
                yield return new ExpressionDepth(dropFirstElement, exprDepth.depth + 1);
              }

              {
                // create drop last element of a sequence
                var cardinalityMinusOneExpr = Expression.CreateDecrement(expr, 1);
                var dropLastElement = new SeqSelectExpr(expr.tok, false, expr, null, cardinalityMinusOneExpr);
                dropLastElement.Type = t;
                yield return new ExpressionDepth(dropLastElement, exprDepth.depth + 1);
              }
            }
          }
        }
        // Console.WriteLine("pre-defined variable type");
        yield break;
      }
      var udt = (UserDefinedType)t;
      var cl = udt.ResolvedClass;
      if (cl is OpaqueTypeDecl) {
        var otd = (OpaqueTypeDecl)cl;
        // Console.WriteLine($"{variable.Name} is OpaqueTypeDecl");
        // TODO traverse underlying definition as well.
        throw new NotImplementedException();
      } else if (cl is TypeParameter) {
        var tp = (TypeParameter)cl;
        // Console.WriteLine($"{variable.Name} is TypeParameter");
        // TODO traverse underlying definition as well.
        throw new NotImplementedException();
      } else if (cl is InternalTypeSynonymDecl) {
        var isyn = (InternalTypeSynonymDecl)cl;
        // Console.WriteLine($"{variable.Name} is InternalTypeSynonymDecl");
        // TODO traverse underlying definition as well.
        throw new NotImplementedException();
      } else if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        // Console.WriteLine($"{Printer.ExprToString(td.Constraint)} {td.Var.Name} {td.BaseType} {td.BaseType is IntType}");
        // TODO possibly figure out other expressions from td.Constraint
        if (td.BaseType is IntType) {
          var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
          zeroLiteralExpr.Type = t;
          // TODO Add the literal for maximum value of this newtype decl.
          yield return new ExpressionDepth(zeroLiteralExpr, 1);
          var oneLiteralExpr = Expression.CreateIntLiteral(expr.tok, 1);
          oneLiteralExpr.Type = t;
          yield return new ExpressionDepth(oneLiteralExpr, 1);

          var plusOneLiteralExpr = Expression.CreateIncrement(expr, 1);
          plusOneLiteralExpr.Type = t;
          yield return new ExpressionDepth(plusOneLiteralExpr, exprDepth.depth);
          var minusOneLiteralExpr = Expression.CreateDecrement(expr, 1);
          minusOneLiteralExpr.Type = t;
          yield return new ExpressionDepth(minusOneLiteralExpr, exprDepth.depth);
        } else {
          throw new NotImplementedException();
        }
        // foreach (var v in TraverseType(program, td.BaseType)) {
        //   // var ngv = (Formal)variable;
        //   // var dotVar = new Formal(ngv.tok, ngv.Name + "." + v.Name, v.Type, true, true, null);
        //   Console.WriteLine($"!!!! {v.val}");
        //   var e = new ExprDotName(v, expr, v.val, null);
        //   e.Type = expr.Type;
        //   // Console.WriteLine($"Constructing dot var:{dotVar.Name}");
        //   yield return e;
        // }
      } else if (cl is SubsetTypeDecl) {
        // Console.WriteLine($"{Printer.ExprToString(expr)}");
        var td = (SubsetTypeDecl)cl;
        // Console.WriteLine($"{Printer.ExprToString(td.Constraint)} {td.Var.Name} {td.Rhs}");
        if (td.Rhs is IntType) {
          var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
          zeroLiteralExpr.Type = t;
          yield return new ExpressionDepth(zeroLiteralExpr, 1);
          var oneLiteralExpr = Expression.CreateIntLiteral(expr.tok, 1);
          oneLiteralExpr.Type = t;
          yield return new ExpressionDepth(oneLiteralExpr, 1);
          var plusOneLiteralExpr = Expression.CreateIncrement(expr, 1);
          plusOneLiteralExpr.Type = t;
          yield return new ExpressionDepth(plusOneLiteralExpr, exprDepth.depth);
          var minusOneLiteralExpr = Expression.CreateDecrement(expr, 1);
          minusOneLiteralExpr.Type = t;
          yield return new ExpressionDepth(minusOneLiteralExpr, exprDepth.depth);
        }
        // Console.WriteLine($"{variable.Name} is SubsetTypeDecl");
      } else if (cl is ClassDecl) {
        // Console.WriteLine($"{variable.Name} is ClassDecl");
        // TODO traverse underlying definition as well.
        throw new NotImplementedException();
      } else if (cl is DatatypeDecl) {
        if (exprDepth.depth + 1 <= maxExpressionDepth) {
          var dt = (DatatypeDecl)cl;
          var subst = Resolver.TypeSubstitutionMap(dt.TypeArgs, udt.TypeArgs);
          // Console.WriteLine($"{variable.Name} is DatatypeDecl");
          foreach (var ctor in dt.Ctors) {
            if (dt.Ctors.Count > 1) {
              var exprDot = new ExprDotName(ctor.tok, expr, ctor.tok.val + "?", null);
              exprDot.Type = Type.Bool;
              yield return new ExpressionDepth(exprDot, exprDepth.depth + 1);
            }
            foreach (var formal in ctor.Formals) {
              // Console.WriteLine($"type={formal.Type} => {Resolver.SubstType(formal.Type, subst)}");
              // var convertedFormal = new Formal(formal.tok, formal.Name, 
              //     Resolver.SubstType(formal.Type, subst), formal.InParam, formal.IsGhost,
              //     formal.DefaultValue, formal.IsOld, formal.IsNameOnly, formal.NameForCompilation);
              // var identExpr = Expression.CreateIdentExpr(convertedFormal);
              var exprDot = new ExprDotName(formal.tok, expr, formal.tok.val, null);
              exprDot.Type = Resolver.SubstType(formal.Type, subst);
              if (exprDot.Type.AsTypeSynonym != null) {
                var ts = exprDot.Type.AsTypeSynonym;
                exprDot.Type = ts.Rhs;
              }
              foreach (var v in TraverseFormal(program, new ExpressionDepth(exprDot, exprDepth.depth + 1))) {
                // Console.WriteLine($"aaa {v.tok.val}");
                // // var ngv = (Formal)variable;
                // // var dotVar = new Formal(ngv.tok, ngv.Name + "." + v.Name, v.Type, true, true, null);
                // // Console.WriteLine($"Constructing dot var:{dotVar.Name}");
                // var e = new ExprDotName(v.tok, expr, v.tok.val, null);
                // e.Type = v.Type;
                yield return v;
              }
              // Console.WriteLine($"aaaa {formal.Name}");
            }
          }
        }
      } else if (cl is TypeSynonymDecl) {
        var ts = cl as TypeSynonymDecl;
        var substExpr = new Cloner().CloneExpr(expr);
        substExpr.Type = ts.Rhs;
        foreach (var v in TraverseFormal(program, new ExpressionDepth(substExpr, exprDepth.depth))) {
          yield return v;
        }
      }
      // var members = expr.Type.NormalizeExpand().AsTopLevelTypeWithMembers;
      // foreach(var mem in members.Members)
      // {
      //   Console.WriteLine(mem);
      // }
      // if (expr.SubExpressions != null)
      // {
      // foreach (var subexpr in expr.SubExpressions)
      // {
      //   TraverseFormal(subexpr);
      // }
      // }
    }

    public IEnumerable<IToken> TraverseType(Program program, Type t) {
      // Console.WriteLine(t.ToString());
      if (t is BoolType || t is CharType || t is IntType || t is BigOrdinalType ||
          t is RealType || t is BitvectorType || t is CollectionType) {
        // Console.WriteLine("pre-defined type");
        yield break;
      }
      var udt = (UserDefinedType)t;
      var cl = udt.ResolvedClass;
      if (cl is OpaqueTypeDecl) {
        var otd = (OpaqueTypeDecl)cl;
        // Console.WriteLine($"{t.ToString()} is OpaqueTypeDecl");
        // TODO traverse underlying definition as well.
      } else if (cl is TypeParameter) {
        var tp = (TypeParameter)cl;
        // Console.WriteLine($"{t.ToString()} is TypeParameter");
        // TODO traverse underlying definition as well.
      } else if (cl is InternalTypeSynonymDecl) {
        var isyn = (InternalTypeSynonymDecl)cl;
        // Console.WriteLine($"{t.ToString()} is InternalTypeSynonymDecl");
        // TODO traverse underlying definition as well.
      } else if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        // Console.WriteLine($"{t.ToString()} is NewtypeDecl");
        foreach (var v in TraverseType(program, td.BaseType)) {
          yield return v;
        }
      } else if (cl is SubsetTypeDecl) {
        var td = (SubsetTypeDecl)cl;
        // Console.WriteLine($"{t.ToString()} is SubsetTypeDecl");
        // TODO traverse underlying definition as well.
      } else if (cl is ClassDecl) {
        // Console.WriteLine($"{t.ToString()} is ClassDecl");
        // TODO traverse underlying definition as well.
      } else if (cl is DatatypeDecl) {
        var dt = (DatatypeDecl)cl;
        // Console.WriteLine($"{t.ToString()} is DatatypeDecl");
        // TODO traverse underlying definition as well.
      } else {
        // Console.WriteLine($"{t.ToString()} is unknown");
      }
      // var members = expr.Type.NormalizeExpand().AsTopLevelTypeWithMembers;
      // foreach(var mem in members.Members)
      // {
      //   Console.WriteLine(mem);
      // }
      // if (expr.SubExpressions != null)
      // {
      // foreach (var subexpr in expr.SubExpressions)
      // {
      //   TraverseFormal(subexpr);
      // }
      // }
    }
  }
}
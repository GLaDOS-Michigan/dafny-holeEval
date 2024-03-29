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
    public List<Expression> availableExpressions = new List<Expression>();
    private List<BitArray> bitArrayList = new List<BitArray>();
    private HashSet<string> currCombinations = new HashSet<string>();
    private Dictionary<string, int> bitArrayStringToIndex = new Dictionary<string, int>();
    public Dictionary<int, Result> combinationResults = new Dictionary<int, Result>();
    private Dictionary<int, int> negateOfExpressionIndex = new Dictionary<int, int>();

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

    public IEnumerable<Expression> ExtendSeqSelectExpressions(IEnumerable<Expression> expressionList) {
      Console.WriteLine("here");
      var typeToExpressionDict = GetTypeToExpressionDict(expressionList);
      foreach (var expr in expressionList) {
        if (expr is SeqSelectExpr) {
          Console.WriteLine($"ExtendSeqSelect: {Printer.ExprToString(expr)}");
        }
      }
      yield break;
    }

    public void CalcDepthOneAvailableExpresssionsFromFunction(Program program, Function desiredFunction) {
      Contract.Requires(desiredFunction != null);
      Contract.Requires(availableExpressions.Count == 0);
      var expressions = ListArguments(program, desiredFunction);
      CalcDepthOneAvailableExpresssions(program, desiredFunction, expressions);
    }

    public void CalcDepthOneAvailableExpresssionsFromLemma(Program program, Lemma desiredLemma) {
      Contract.Requires(desiredLemma != null);
      Contract.Requires(availableExpressions.Count == 0);
      var expressions = ListArguments(program, desiredLemma);
      var extendedExpressions = ExtendSeqSelectExpressions(expressions);
      CalcDepthOneAvailableExpresssions(program, desiredLemma, extendedExpressions);
    }

    public Dictionary<string, List<Expression>> GetTypeToExpressionDict(IEnumerable<Expression> expressionList) {
      Dictionary<string, List<Expression>> typeToExpressionDict = new Dictionary<string, List<Expression>>();
      foreach (var expr in expressionList) {
        var exprString = Printer.ExprToString(expr);
        var typeString = expr.Type.ToString();
        // Console.WriteLine($"{c,2} {exprString,-20} {typeString}");
        if (expr.Type == Type.Bool && exprString[exprString.Length - 1] == '?') {
          typeString = "_questionMark_";
        }
        if (typeToExpressionDict.ContainsKey(typeString)) {
          bool containsItem = typeToExpressionDict[typeString].Any(
               item => Printer.ExprToString(item) == Printer.ExprToString(expr));
          if (!containsItem) {
            typeToExpressionDict[typeString].Add(expr);
          }
        } else {
          var lst = new List<Expression>();
          lst.Add(expr);
          typeToExpressionDict.Add(typeString, lst);
        }
        // AddExpression(program, topLevelDecl, expr);
      }
      return typeToExpressionDict;
    }

    public Dictionary<string, List<Expression>> GetRawExpressions(Program program, MemberDecl decl,
        IEnumerable<Expression> expressions, bool addToAvailableExpressions) {
      var typeToExpressionDict = GetTypeToExpressionDict(expressions);
      foreach (var kvp in program.ModuleSigs) {
        foreach (var d in kvp.Value.ModuleDef.TopLevelDecls) {
          var cl = d as TopLevelDeclWithMembers;
          if (cl != null) {
            foreach (var member in cl.Members) {
              if (member is Predicate) {
                var predicateInvocations = GetAllPossiblePredicateInvocations(program, member as Predicate, typeToExpressionDict);
                if (!typeToExpressionDict.ContainsKey("bool")) {
                  typeToExpressionDict.Add("bool", new List<Expression>());
                }
                typeToExpressionDict["bool"].AddRange(predicateInvocations);
              }
            }
          }
        }
      }
      if (decl is Function) {
        var desiredFunction = decl as Function;
        var equalExprToCheck = desiredFunction.Body;
        foreach (var e in desiredFunction.Req) {
          equalExprToCheck = Expression.CreateAnd(equalExprToCheck, e.E);
        }
        Dictionary<string, List<string>> equalExprList = GetEqualExpressionList(equalExprToCheck);
        foreach (var k in equalExprList.Keys) {
          var t = equalExprList[k][0];
          for (int i = 1; i < equalExprList[k].Count; i++) {
            for (int j = 0; j < typeToExpressionDict[t].Count; j++) {
              if (Printer.ExprToString(typeToExpressionDict[t][j]) == equalExprList[k][i]) {
                typeToExpressionDict[t].RemoveAt(j);
                break;
              }
            }
          }
        }
      }
      if (addToAvailableExpressions) {
        foreach (var t in typeToExpressionDict) {
          for (int i = 0; i < t.Value.Count; i++) {
            availableExpressions.Add(t.Value[i]);
          }
        }
      }
      return typeToExpressionDict;
    }

    public void CalcDepthOneAvailableExpresssions(Program program, MemberDecl decl, IEnumerable<Expression> expressions) {
      Contract.Requires(availableExpressions.Count == 0);
      Dictionary<string, List<Expression>> typeToExpressionDict = GetRawExpressions(program, decl, expressions, false);

      var trueExpr = Expression.CreateBoolLiteral(decl.tok, true);
      availableExpressions.Add(trueExpr);
      foreach (var k in typeToExpressionDict.Keys) {
        var values = typeToExpressionDict[k];
        if (k == "_questionMark_") {
          for (int i = 0; i < values.Count; i++) {
            {
              // No change to the type, add as is
              var expr = values[i];
              availableExpressions.Add(expr);
            }
          }
        } else {
          for (int i = 0; i < values.Count; i++) {
            for (int j = i + 1; j < values.Count; j++) {
              if (values[i] is LiteralExpr && values[j] is LiteralExpr) {
                continue;
              }
              if (values[i] is ApplySuffix && values[j] is ApplySuffix) {
                continue;
              }
              // Equality
              {
                var equalityExpr = Expression.CreateEq(values[i], values[j], values[i].Type);
                equalityExpr.HasCardinality = values[i].HasCardinality | values[j].HasCardinality;
                availableExpressions.Add(equalityExpr);
              }
              if (values[i] is ApplySuffix || values[j] is ApplySuffix) {
                continue;
              }
              // Non-Equality
              {
                var neqExpr = Expression.CreateNot(values[i].tok, Expression.CreateEq(values[i], values[j], values[i].Type));
                neqExpr.HasCardinality = values[i].HasCardinality | values[j].HasCardinality;
                availableExpressions.Add(neqExpr);
                negateOfExpressionIndex[availableExpressions.Count - 1] = availableExpressions.Count - 2;
                negateOfExpressionIndex[availableExpressions.Count - 2] = availableExpressions.Count - 1;
              }
              if (k == "bool") {
                continue;
              }

              // Lower than
              {
                var lowerThanExpr = Expression.CreateLess(values[i], values[j]);
                lowerThanExpr.HasCardinality = values[i].HasCardinality | values[j].HasCardinality;
                availableExpressions.Add(lowerThanExpr);
              }
              // Greater Equal = !(Lower than)
              {
                var geExpr = Expression.CreateNot(values[i].tok, Expression.CreateLess(values[i], values[j]));
                geExpr.HasCardinality = values[i].HasCardinality | values[j].HasCardinality;
                availableExpressions.Add(geExpr);
                negateOfExpressionIndex[availableExpressions.Count - 1] = availableExpressions.Count - 2;
                negateOfExpressionIndex[availableExpressions.Count - 2] = availableExpressions.Count - 1;
              }
              // Lower Equal
              {
                var leExpr = Expression.CreateAtMost(values[i], values[j]);
                leExpr.HasCardinality = values[i].HasCardinality | values[j].HasCardinality;
                availableExpressions.Add(leExpr);
              }
              // Greater Than = !(Lower equal)
              {
                var gtExpr = Expression.CreateNot(values[i].tok, Expression.CreateAtMost(values[i], values[j]));
                gtExpr.HasCardinality = values[i].HasCardinality | values[j].HasCardinality;
                availableExpressions.Add(gtExpr);
                negateOfExpressionIndex[availableExpressions.Count - 1] = availableExpressions.Count - 2;
                negateOfExpressionIndex[availableExpressions.Count - 2] = availableExpressions.Count - 1;
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
            var exprA = availableExpressions[i];
            var exprB = availableExpressions[j];
            var conjunctExpr = Expression.CreateAnd(exprA, exprB);
            conjunctExpr.HasCardinality = exprA.HasCardinality | exprB.HasCardinality;
            BitArray bitArray = new BitArray(bitArrayList[i]);
            bitArray.Or(bitArrayList[j]);
            bitArrayList.Add(bitArray);
            currCombinations.Add(ToBitString(bitArray, true));
            bitArrayStringToIndex[ToBitString(bitArray, true)] = bitArrayList.Count - 1;
            availableExpressions.Add(conjunctExpr);
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
        var applySuffixExpr = new ApplySuffix(ctor.tok, null, new NameSegment(ctor.tok, ctor.Name, null), bindings);
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

    public static IEnumerable<Expression> ListInvocations(
        Function func,
        Dictionary<string, List<Expression>> typeToExpressionDict,
        List<Expression> arguments,
        int shouldFillIndex) {
      if (shouldFillIndex == func.Formals.Count) {
        List<ActualBinding> bindings = new List<ActualBinding>();
        foreach (var arg in arguments) {
          bindings.Add(new ActualBinding(null, arg));
        }
        var funcCallExpr = new FunctionCallExpr(func.tok, func.FullDafnyName, new ImplicitThisExpr(func.tok), func.tok, bindings);
        funcCallExpr.Type = func.ResultType;
        yield return funcCallExpr;
        yield break;
      }
      var t = func.Formals[shouldFillIndex].Type;
      if (typeToExpressionDict.ContainsKey(t.ToString())) {
        foreach (var expr in typeToExpressionDict[t.ToString()]) {
          arguments.Add(expr);
          foreach (var ans in ListInvocations(func, typeToExpressionDict, arguments, shouldFillIndex + 1)) {
            yield return ans;
          }
          arguments.RemoveAt(arguments.Count - 1);
        }
      }
    }

    public static List<Expression> GetAllPossibleFunctionInvocations(Program program,
        Function func,
        Dictionary<string, List<Expression>> typeToExpressionDict) {
      List<Expression> result = new List<Expression>();
      List<Expression> workingList = new List<Expression>();
      foreach (var expr in ListInvocations(func, typeToExpressionDict, workingList, 0)) {
        result.Add(expr);
      }
      return result;
    }

    public static IEnumerable<Expression> ListPredicateInvocations(
        Predicate func,
        Dictionary<string, List<Expression>> typeToExpressionDict,
        List<Expression> arguments,
        int shouldFillIndex) {
      if (shouldFillIndex == func.Formals.Count) {
        List<ActualBinding> bindings = new List<ActualBinding>();
        foreach (var arg in arguments) {
          bindings.Add(new ActualBinding(null, arg));
        }
        var applySuffixExpr = new ApplySuffix(func.tok, null, new IdentifierExpr(func.tok, func.FullDafnyName), bindings);
        applySuffixExpr.Type = func.ResultType;
        yield return applySuffixExpr;
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

    public static List<Expression> GetAllPossiblePredicateInvocations(Program program,
        Predicate func,
        Dictionary<string, List<Expression>> typeToExpressionDict) {
      List<Expression> result = new List<Expression>();
      List<Expression> workingList = new List<Expression>();
      foreach (var expr in ListPredicateInvocations(func, typeToExpressionDict, workingList, 0)) {
        result.Add(expr);
      }
      return result;
    }

    public IEnumerable<Expression> ListArguments(Program program, Function func) {
      foreach (var formal in func.Formals) {
        // Console.WriteLine($"\n{formal.Name}\t{formal.Type.ToString()}");
        // Console.WriteLine(formal.Type.NormalizeExpand().IsTopLevelTypeWithMembers);
        // var c = 0;
        var identExpr = Expression.CreateIdentExpr(formal);
        foreach (var expr in TraverseFormal(program, identExpr)) {
          // Console.WriteLine($"{c} {variable.Name,-20}:\t{variable.Type}");
          // c++;
          yield return expr;
        }

      }
    }

    public IEnumerable<Expression> ListArguments(Program program, Lemma lemma) {
      foreach (var formal in lemma.Ins) {
        var identExpr = Expression.CreateIdentExpr(formal);
        foreach (var expr in TraverseFormal(program, identExpr)) {
          yield return expr;
        }
      }
      foreach (var formal in lemma.Outs) {
        var identExpr = Expression.CreateIdentExpr(formal);
        foreach (var expr in TraverseFormal(program, identExpr)) {
          yield return expr;
        }
      }
    }

    public IEnumerable<Expression> TraverseFormal(Program program, Expression expr) {
      Contract.Requires(expr != null);
      yield return expr;
      var t = expr.Type;
      if (t is BoolType || t is CharType || t is IntType || t is BigOrdinalType ||
          t is RealType || t is BitvectorType || t is CollectionType) {
        if (t is BoolType) {
          var trueLiteralExpr = Expression.CreateBoolLiteral(expr.tok, true);
          yield return trueLiteralExpr;
          // NOTE: No need to add false literal since we also check for non-equality.
        } else if (t is IntType) {
          var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
          yield return zeroLiteralExpr;
          var oneLiteralExpr = Expression.CreateIntLiteral(expr.tok, 1);
          yield return oneLiteralExpr;
        } else if (t is CollectionType) {
          // create cardinality
          var cardinalityExpr = Expression.CreateCardinality(expr, program.BuiltIns);
          yield return cardinalityExpr;
          if (t is SeqType) {
            var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
            var zerothElement = new SeqSelectExpr(expr.tok, true, expr, zeroLiteralExpr, null);
            var st = t as SeqType;
            zerothElement.Type = st.Arg;
            foreach (var e in TraverseFormal(program, zerothElement)) {
              yield return e;
            }
            // create 0th element of the sequence
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
          yield return zeroLiteralExpr;
          var oneLiteralExpr = Expression.CreateIntLiteral(expr.tok, 1);
          oneLiteralExpr.Type = t;
          yield return oneLiteralExpr;
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
          yield return zeroLiteralExpr;
          var oneLiteralExpr = Expression.CreateIntLiteral(expr.tok, 1);
          oneLiteralExpr.Type = t;
          yield return oneLiteralExpr;

        }
        // Console.WriteLine($"{variable.Name} is SubsetTypeDecl");
      } else if (cl is ClassDecl) {
        // Console.WriteLine($"{variable.Name} is ClassDecl");
        // TODO traverse underlying definition as well.
        throw new NotImplementedException();
      } else if (cl is DatatypeDecl) {
        var dt = (DatatypeDecl)cl;
        var subst = Resolver.TypeSubstitutionMap(dt.TypeArgs, udt.TypeArgs);
        // Console.WriteLine($"{variable.Name} is DatatypeDecl");
        foreach (var ctor in dt.Ctors) {
          if (dt.Ctors.Count > 1) {
            var exprDot = new ExprDotName(ctor.tok, expr, ctor.tok.val + "?", null);
            exprDot.Type = Type.Bool;
            yield return exprDot;
          }
          foreach (var formal in ctor.Formals) {
            // Console.WriteLine($"type={formal.Type} => {Resolver.SubstType(formal.Type, subst)}");
            // var convertedFormal = new Formal(formal.tok, formal.Name, 
            //     Resolver.SubstType(formal.Type, subst), formal.InParam, formal.IsGhost,
            //     formal.DefaultValue, formal.IsOld, formal.IsNameOnly, formal.NameForCompilation);
            // var identExpr = Expression.CreateIdentExpr(convertedFormal);
            var exprDot = new ExprDotName(formal.tok, expr, formal.tok.val, null);
            exprDot.Type = Resolver.SubstType(formal.Type, subst);
            foreach (var v in TraverseFormal(program, exprDot)) {
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
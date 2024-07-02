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
  public class InvariantFinder {

    public InvariantFinder() {
    }

    public static IEnumerable<ExpressionFinder.ExpressionDepth> GetCandidateInvariants(Program program, Function func) {
      int maxEvalDepth = DafnyOptions.O.HoleEvaluatorExpressionDepth;
      var expressions = ExpressionFinder.ListArguments(program, func, true);
      Dictionary<string, HashSet<ExpressionFinder.ExpressionDepth>> typeToExpressionDict = ExpressionFinder.GetRawExpressions(program, func as MemberDecl, expressions);
      // if (typeToExpressionDict.ContainsKey("int")) {
      //   var intExpressions = typeToExpressionDict["int"].ToList();
      //   for (int i = 0; i < intExpressions.Count; i++) {
      //     var e0 = intExpressions[i];
      //     if (e0.depth >= maxEvalDepth) {
      //       continue;
      //     }
      //     for (int j = i + 1; j < intExpressions.Count; j++) {
      //       var e1 = intExpressions[j];
      //       if (e0.depth + e1.depth < maxEvalDepth) {
      //         var sumExpr = Expression.CreateAdd(e0.expr, e1.expr);
      //         typeToExpressionDict["int"].Add(new ExpressionFinder.ExpressionDepth(sumExpr, e0.depth + e1.depth + 1));

      //         // var subExpr = Expression.CreateSub(e0.expr, e1.expr);
      //         // typeToExpressionDict["int"].Add(new ExpressionFinder.ExpressionDepth(e0.depth + e1.depth + 1, sumExpr));
      //       }
      //     }
      //   }
      // }
      // foreach (var kvp in program.ModuleSigs) {
      //   foreach (var d in kvp.Value.ModuleDef.TopLevelDecls) {
      //     var cl = d as TopLevelDeclWithMembers;
      //     if (cl != null) {
      //       foreach (var member in cl.Members) {
      //         if (member is Predicate) {
      //           var predicateInvocations = GetAllPossiblePredicateInvocations(program, member as Predicate, typeToExpressionDict);
      //           foreach (var invocation in predicateInvocations) {
      //             yield return invocation;
      //           }
      //         }
      //       }
      //     }
      //   }
      // }
      foreach (var t in typeToExpressionDict.Keys) {
        Console.WriteLine($"type = {t}");
        var exprList = typeToExpressionDict[t].ToList();
        List<ExpressionFinder.ExpressionDepth> literals = null;
        if (t == "int") {
          var literalsHashset = new HashSet<string>();
          literals = new List<ExpressionFinder.ExpressionDepth>();
          for (int i = 0; i < exprList.Count; i++) {
            if (exprList[i].expr is LiteralExpr literalExpr) {
              var literalExprStr = Printer.ExprToString(literalExpr);
              if (literalExprStr != "0" && literalExprStr != "1" && !literalsHashset.Contains(literalExprStr)) {
                literals.Add(exprList[i]);
                literalsHashset.Add(literalExprStr);
              }
            }
          }
        }
        if (t == "_questionMark_" || t == "bool") {
          for (int i = 0; i < exprList.Count; i++) {
            var e0 = exprList[i];
            if (e0.depth >= maxEvalDepth) {
              continue;
            }
            yield return new ExpressionFinder.ExpressionDepth(e0.expr, e0.depth, false);
            var notE0 = Expression.CreateNot(e0.expr.tok, e0.expr);
            yield return new ExpressionFinder.ExpressionDepth(notE0, e0.depth, true);
          }
        }
        else if (t.StartsWith("seq")) {
          for (int i = 0; i < exprList.Count; i++) {
            var e0 = exprList[i];
            if (Printer.ExprToString(e0.expr).EndsWith(']'))
            {
              continue;
            }
            var newVars = new List<BoundVar> {
              new BoundVar(e0.expr.tok, "i", Type.Nat())
            };
            var iExpr = Expression.CreateIdentExpr(newVars[0]);
            var ithElement = new SeqSelectExpr(e0.expr.tok, true, e0.expr, iExpr, null, e0.expr.tok) {
              Type = e0.expr.Type.AsCollectionType.Arg
            };
            var rangeExprOperands = new List<Expression> {
              Expression.CreateIntLiteral(Token.NoToken, 0),
              iExpr,
              Expression.CreateCardinality(e0.expr, program.BuiltIns)
            };
            var rangeExprOpcodes = new List<BinaryExpr.Opcode> {
              BinaryExpr.Opcode.Le,
              BinaryExpr.Opcode.Lt
            };
            var rangeExprOpcodeLocs = new List<IToken> {
              Token.NoToken, Token.NoToken
            };
            var rangeExprPrefixLimits = new List<Expression> {
              null, null
            };
            var rangeExpr = new ChainingExpression(e0.expr.tok, rangeExprOperands, rangeExprOpcodes, rangeExprOpcodeLocs, rangeExprPrefixLimits) {
              Type = Type.Bool
            };
            foreach (var exprDepth in ExpressionFinder.TraverseFormal(program, new ExpressionFinder.ExpressionDepth(ithElement, e0.depth + 1, false))) {
              // Console.WriteLine(Printer.ExprToString(exprDepth.expr));
              if (exprDepth.expr.Type.ToString() != "bool") {
                foreach (var subExpr in typeToExpressionDict[exprDepth.expr.Type.ToString()])
                {
                  {
                    var eqBody = Expression.CreateEq(exprDepth.expr, subExpr.expr, exprDepth.expr.Type);
                    var forallExpr = new ForallExpr(e0.expr.tok, e0.expr.tok, newVars, rangeExpr, eqBody, null) {
                      Type = Type.Bool
                    };
                    yield return new ExpressionFinder.ExpressionDepth(forallExpr, e0.depth + subExpr.depth + 1, false);
                  }
                  {
                    var neqBody = Expression.CreateNot(exprDepth.expr.tok, Expression.CreateEq(exprDepth.expr, subExpr.expr, exprDepth.expr.Type));
                    var forallExpr = new ForallExpr(e0.expr.tok, e0.expr.tok, newVars, rangeExpr, neqBody, null) {
                      Type = Type.Bool
                    };
                    yield return new ExpressionFinder.ExpressionDepth(forallExpr, e0.depth + subExpr.depth + 1, false);
                  }
                }
              } else {
                {
                  var forallExpr = new ForallExpr(e0.expr.tok, e0.expr.tok, newVars, rangeExpr, exprDepth.expr, null) {
                      Type = Type.Bool
                    };
                  yield return new ExpressionFinder.ExpressionDepth(forallExpr, e0.depth + exprDepth.depth + 1, false);
                }
                {
                  var neqExpr = Expression.CreateNot(exprDepth.expr.tok, exprDepth.expr);
                  var forallExpr = new ForallExpr(e0.expr.tok, e0.expr.tok, newVars, rangeExpr, neqExpr, null) {
                      Type = Type.Bool
                    };
                  yield return new ExpressionFinder.ExpressionDepth(forallExpr, e0.depth + exprDepth.depth + 1, false);
                }
              }
              if (typeToExpressionDict.ContainsKey("_questionMark_"))
              {
                foreach (var subExpr in typeToExpressionDict["_questionMark_"])
                {
                }
              }
            }
          }
          yield break;
        }
        else {
          for (int i = 0; i < exprList.Count; i++) {
            var e0 = exprList[i];
            if (e0.depth >= maxEvalDepth) {
              continue;
            }
            for (int j = i + 1; j < exprList.Count; j++) {
              var e1 = exprList[j];
              if (e0.depth + e1.depth < maxEvalDepth) {
                var ltExpr = Expression.CreateLess(e0.expr, e1.expr);
                yield return new ExpressionFinder.ExpressionDepth(ltExpr, e0.depth + e1.depth + 1, false);
                
                var geExpr = Expression.CreateNot(e0.expr.tok, Expression.CreateLess(e0.expr, e1.expr));
                yield return new ExpressionFinder.ExpressionDepth(geExpr, e0.depth + e1.depth + 1, true);

                var gtExpr = Expression.CreateAtMost(e0.expr, e1.expr);
                yield return new ExpressionFinder.ExpressionDepth(gtExpr, e0.depth + e1.depth + 1, false);

                var leExpr = Expression.CreateNot(e0.expr.tok, Expression.CreateAtMost(e0.expr, e1.expr));
                yield return new ExpressionFinder.ExpressionDepth(leExpr, e0.depth + e1.depth + 1, true);

                var eqExpr = Expression.CreateEq(e0.expr, e1.expr, e0.expr.Type);
                yield return new ExpressionFinder.ExpressionDepth(eqExpr, e0.depth + e1.depth + 1, false);

                var neqExpr = Expression.CreateNot(e0.expr.tok, Expression.CreateEq(e0.expr, e1.expr, e0.expr.Type));
                yield return new ExpressionFinder.ExpressionDepth(neqExpr, e0.depth + e1.depth + 1, false);

                if (t == "int") {
                  if (!(e0.expr is LiteralExpr) && !(e1.expr is LiteralExpr) 
                      && !(e0.expr is BinaryExpr) && !(e1.expr is BinaryExpr)) {
                    for (int k = 0; k < literals.Count; k++) {
                      var lit = literals[k].expr;
                      {
                        var sumExpr = Expression.CreateAdd(e0.expr, e1.expr);
                        var sumLtExpr = Expression.CreateLess(sumExpr, lit);
                        yield return new ExpressionFinder.ExpressionDepth(sumLtExpr, e0.depth + e1.depth + 1, false);
                      }
                      {
                        var sumExpr = Expression.CreateAdd(e0.expr, e1.expr);
                        var sumGeExpr = Expression.CreateNot(e0.expr.tok, Expression.CreateLess(sumExpr, lit));
                        yield return new ExpressionFinder.ExpressionDepth(sumGeExpr, e0.depth + e1.depth + 1, true);
                      }
                      {
                        var sumExpr = Expression.CreateAdd(e0.expr, e1.expr);
                        var sumGtExpr = Expression.CreateAtMost(sumExpr, lit);
                        yield return new ExpressionFinder.ExpressionDepth(sumGtExpr, e0.depth + e1.depth + 1, false);
                      }
                      {
                        var sumExpr = Expression.CreateAdd(e0.expr, e1.expr);
                        var sumLeExpr = Expression.CreateNot(e0.expr.tok, Expression.CreateAtMost(sumExpr, lit));
                        yield return new ExpressionFinder.ExpressionDepth(sumLeExpr, e0.depth + e1.depth + 1, true);
                      }
                      {
                        var sumExpr = Expression.CreateAdd(e0.expr, e1.expr);
                        var sumEqExpr = Expression.CreateEq(sumExpr, lit, lit.Type);
                        yield return new ExpressionFinder.ExpressionDepth(sumEqExpr, e0.depth + e1.depth + 1, false);
                      }
                      {
                        var sumExpr = Expression.CreateAdd(e0.expr, e1.expr);
                        var sumNeExpr = Expression.CreateNot(e0.expr.tok, Expression.CreateEq(sumExpr, lit, lit.Type));
                        yield return new ExpressionFinder.ExpressionDepth(sumNeExpr, e0.depth + e1.depth + 1, true);
                      }
                    }
                  }
                }
              }
            }
          }
        }
        // foreach (var e in typeToExpressionDict[t]) {
        //   Console.WriteLine(Printer.ExprToString(e.expr));
        // }
        // Console.WriteLine("---------------------------------------------");
      }
      // foreach (var expr in expressions) {
      //   yield return expr;
      // }
      // yield break;
    }

  }
}
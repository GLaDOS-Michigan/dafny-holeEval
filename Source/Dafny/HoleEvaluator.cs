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
using System.Diagnostics.Contracts;
using System.Reflection;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny {

  public class HoleEvaluator {

    public static void Evaluate(Program program, string funcName) {
      // Console.WriteLine($"hole evaluation begins for func {funcName}");
      foreach (var kvp in program.ModuleSigs) {
        // iterate over all functions / predicates (this doesn't include lemmas)
        foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
          if (topLevelDecl.FullDafnyName == funcName) {
            Console.WriteLine("Found desired function.");
            var expressions = ListArguments(program, topLevelDecl);
            var c = 0;
            Dictionary<string, List<Expression>> typeToExpressionDict = new Dictionary<string, List<Expression>>();
            foreach (var expr in expressions) {
              c++;
              Console.WriteLine($"{c,2} {Printer.ExprToString(expr),-20} {expr.Type}");
              if (typeToExpressionDict.ContainsKey(expr.Type.ToString())) {
                bool containsItem = typeToExpressionDict[expr.Type.ToString()].Any(
                     item => Printer.ExprToString(item) == Printer.ExprToString(expr));
                if (!containsItem) {
                  typeToExpressionDict[expr.Type.ToString()].Add(expr);
                }
              } else {
                var lst = new List<Expression>();
                lst.Add(expr);
                typeToExpressionDict.Add(expr.Type.ToString(), lst);
              }
              // AddExpression(program, topLevelDecl, expr);
            }
            Console.WriteLine("");
            foreach (var k in typeToExpressionDict.Keys) {
              foreach (var v in typeToExpressionDict[k]) {
                Console.WriteLine($"{Printer.ExprToString(v),-20} {v.Type}");
              }
            }
            Function topLevelDeclCopy = new Function(
              topLevelDecl.tok, topLevelDecl.Name, topLevelDecl.HasStaticKeyword,
              topLevelDecl.IsGhost, topLevelDecl.TypeArgs, topLevelDecl.Formals,
              topLevelDecl.Result, topLevelDecl.ResultType, topLevelDecl.Req,
              topLevelDecl.Reads, topLevelDecl.Ens, topLevelDecl.Decreases,
              topLevelDecl.Body, topLevelDecl.ByMethodTok, topLevelDecl.ByMethodBody,
              topLevelDecl.Attributes, topLevelDecl.SignatureEllipsis);
            // check equality of each pair of same type expressions
            var cnt = 0;
            using (var wr = new System.IO.StringWriter()) {
              var pr = new Printer(wr);
              pr.PrintProgram(program, true);
              File.WriteAllTextAsync($"/tmp/{funcName}_base.dfy",
                Printer.ToStringWithoutNewline(wr));
            }
            foreach (var k in typeToExpressionDict.Keys) {
              var values = typeToExpressionDict[k];
              for (int i = 0; i < values.Count; i++) {
                for (int j = i + 1; j < values.Count; j++) {
                  if (values[i] is LiteralExpr && values[j] is LiteralExpr) {
                    continue;
                  }
                  // Equality
                  {
                    cnt = cnt + 1;
                    var equalityExpr = Expression.CreateEq(values[i], values[j], values[i].Type);
                    var expr = equalityExpr;
                    PrintExpr(program, topLevelDecl, expr, cnt);
                    topLevelDecl.Body = topLevelDeclCopy.Body;
                  }

                  // Non-Equality
                  {
                    cnt = cnt + 1;
                    var neqExpr = Expression.CreateNot(values[i].tok, Expression.CreateEq(values[i], values[j], values[i].Type));
                    var expr = neqExpr;
                    PrintExpr(program, topLevelDecl, expr, cnt);
                    topLevelDecl.Body = topLevelDeclCopy.Body;
                  }

                  if (k == "bool") {
                    continue;
                  }

                  // Lower than
                  {
                    cnt = cnt + 1;
                    var lowerThanExpr = Expression.CreateLess(values[i], values[j]);
                    var expr = lowerThanExpr;
                    PrintExpr(program, topLevelDecl, expr, cnt);
                    topLevelDecl.Body = topLevelDeclCopy.Body;
                  }

                  // Greater Equal = !(Lower than)
                  {
                    cnt = cnt + 1;
                    var geExpr = Expression.CreateNot(values[i].tok,Expression.CreateLess(values[i], values[j]));
                    var expr = geExpr;
                    PrintExpr(program, topLevelDecl, expr, cnt);
                    topLevelDecl.Body = topLevelDeclCopy.Body;
                  }

                  // Lower Equal
                  {
                    cnt = cnt + 1;
                    var leExpr = Expression.CreateAtMost(values[i], values[j]);
                    var expr = leExpr;
                    PrintExpr(program, topLevelDecl, expr, cnt);
                    topLevelDecl.Body = topLevelDeclCopy.Body;
                  }

                  // Greater Than = !(Lower equal)
                  {
                    cnt = cnt + 1;
                    var gtExpr = Expression.CreateNot(values[i].tok,Expression.CreateAtMost(values[i], values[j]));
                    var expr = gtExpr;
                    PrintExpr(program, topLevelDecl, expr, cnt);
                    topLevelDecl.Body = topLevelDeclCopy.Body;
                  }
                }
              }
            }
          }
        }
      }
    }

    public static void PrintExpr(Program program, Function func, Expression expr, int cnt) {
      Console.WriteLine($"{cnt} {Printer.ExprToString(expr)}");

      var funcName = func.FullDafnyName;
      string parameterNameTypes = "";
      string paramNames = "";
      foreach (var param in func.Formals) {
        parameterNameTypes += param.Name + ":" + param.Type.ToString() + ", ";
        paramNames += param.Name + ", ";
      }
      parameterNameTypes = parameterNameTypes.Remove(parameterNameTypes.Length - 2, 2);
      paramNames = paramNames.Remove(paramNames.Length - 2, 2);
      string lemmaForExprValidityString = "lemma checkReachableStatesNotBeFalse(";
      lemmaForExprValidityString += parameterNameTypes + ")\n";
      lemmaForExprValidityString += "  requires ";
      lemmaForExprValidityString += funcName + "(" + paramNames + ")\n";
      lemmaForExprValidityString += "  ensures false\n{}";

      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr);
        func.Body = Expression.CreateAnd(func.Body, expr);
        pr.PrintProgram(program, true);
        File.WriteAllTextAsync($"/tmp/{funcName}_{cnt}.dfy",
          $"// {Printer.ExprToString(expr)}\n" + Printer.ToStringWithoutNewline(wr) +
          "\n\n" + lemmaForExprValidityString + "\n");
        // Console.WriteLine(Printer.ToStringWithoutNewline(wr));
        // Console.WriteLine("");
      }
      // Printer.PrintFunction(transformedFunction, 0, false);
    }

    // public static Function AddExpression(Function func, Expression expr)
    // {
    //   Function result = new Function(func.tok, func.Name, func.HasStaticKeyword, func.IsGhost,
    //   func.TypeArgs, func.Formals, func.Result, func.ResultType,
    //   func.Req, func.Reads, func.Ens, func.Decreases,
    //   Expression.CreateAnd(func.Body, expr), func.ByMethodTok, func.ByMethodBody,
    //   func.Attributes, func.SignatureEllipsis);
    //   return result;
    // }

    public static IEnumerable<Expression> ListArguments(Program program, Function func) {
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

    public static IEnumerable<Expression> TraverseFormal(Program program, Expression expr) {
      Contract.Requires(expr != null);
      yield return expr;
      var t = expr.Type;
      if (t is BoolType || t is CharType || t is IntType || t is BigOrdinalType ||
          t is RealType || t is BitvectorType || t is CollectionType) {
        if (t is BoolType) {
          var trueLiteralExpr = Expression.CreateBoolLiteral(expr.tok, true);
          yield return trueLiteralExpr;
          // NOTE: No need to add false literal since we also check non-equality.
        } else if (t is IntType) {
          var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
          yield return zeroLiteralExpr;
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
      } else if (cl is TypeParameter) {
        var tp = (TypeParameter)cl;
        // Console.WriteLine($"{variable.Name} is TypeParameter");
        // TODO traverse underlying definition as well.
      } else if (cl is InternalTypeSynonymDecl) {
        var isyn = (InternalTypeSynonymDecl)cl;
        // Console.WriteLine($"{variable.Name} is InternalTypeSynonymDecl");
        // TODO traverse underlying definition as well.
      } else if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        Console.WriteLine($"{Printer.ExprToString(td.Constraint)} {td.Var.Name}");
        // TODO possibly figure out other expressions from td.Constraint
        if (td.BaseType is IntType) {
          var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
          zeroLiteralExpr.Type = t;
          // Add the literal for maximum value of this newtype decl.
          yield return zeroLiteralExpr;
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
        Console.WriteLine($"{Printer.ExprToString(expr)}");
        var td = (SubsetTypeDecl)cl;
        Console.WriteLine($"{Printer.ExprToString(td.Constraint)} {td.Var.Name} {td.Rhs}");
        if (td.Rhs is IntType) {
          var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
          zeroLiteralExpr.Type = t;
          yield return zeroLiteralExpr;
        }
        // Console.WriteLine($"{variable.Name} is SubsetTypeDecl");
        // TODO traverse underlying definition as well.
      } else if (cl is ClassDecl) {
        // Console.WriteLine($"{variable.Name} is ClassDecl");
        // TODO traverse underlying definition as well.
      } else if (cl is DatatypeDecl) {
        var dt = (DatatypeDecl)cl;
        var subst = Resolver.TypeSubstitutionMap(dt.TypeArgs, udt.TypeArgs);
        // Console.WriteLine($"{variable.Name} is DatatypeDecl");
        // Console.WriteLine($"Ctor.Count:{dt.Ctors.Count}");
        foreach (var ctor in dt.Ctors) {
          foreach (var formal in ctor.Formals) {
            // Console.WriteLine(formal.Name);
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

    public static IEnumerable<IToken> TraverseType(Program program, Type t) {
      Console.WriteLine(t.ToString());
      if (t is BoolType || t is CharType || t is IntType || t is BigOrdinalType ||
          t is RealType || t is BitvectorType || t is CollectionType) {
        Console.WriteLine("pre-defined type");
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
        Console.WriteLine($"{t.ToString()} is NewtypeDecl");
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
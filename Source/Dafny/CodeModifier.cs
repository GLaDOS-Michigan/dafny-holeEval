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
using System.Linq;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Diagnostics;
using System.Reflection;
using Microsoft.Boogie;
using System.Threading.Tasks;

namespace Microsoft.Dafny {
  public class CodeModifier {
    public CodeModifier() { }

    public static Expression EraseFromExpression(Expression expr, int line) {
      if (expr is ITEExpr iteExpr)
      {
        var thnLastTok = DafnyVerifierClient.GetLastToken(iteExpr.Thn);
        if (line <= thnLastTok.line)
        {
          var newThnExpr = EraseFromExpression(iteExpr.Thn, line);
          return new ITEExpr(iteExpr.tok, iteExpr.IsBindingGuard, iteExpr.Test, newThnExpr, iteExpr.Els);
        }
        else
        {
          var newElsExpr = EraseFromExpression(iteExpr.Els, line);
          return new ITEExpr(iteExpr.tok, iteExpr.IsBindingGuard, iteExpr.Test, iteExpr.Thn, newElsExpr);
        }
      } else if (expr is BinaryExpr binaryExpr) {
        var exprList = Expression.Conjuncts(binaryExpr).ToList();
        int idx = -1;
        for (idx = 0; idx < exprList.Count; idx++) {
          if (line < exprList[idx].tok.line) {
            break;
          }
        }
        exprList.RemoveAt(idx - 1);
        var newExpr = exprList[0];
        for (int j = 1; j < exprList.Count; j++) {
          newExpr = Expression.CreateAnd(newExpr, exprList[j]);
        }
        return newExpr;
      } else if (expr is LetExpr letExpr) {
        var newBodyExpr = EraseFromExpression(letExpr.Body, line);
        return new LetExpr(letExpr.tok, letExpr.LHSs, letExpr.RHSs, newBodyExpr, letExpr.Exact, letExpr.Attributes);
      } else {
        throw new NotSupportedException($"not supported removing from {Printer.ExprToString(expr)} with type {expr.GetType()}");
      }
    }

    public static Change EraseFromPredicate(Predicate predicate, int line) {
      var exprList = Expression.Conjuncts(predicate.Body).ToList();
      Change res = null;
      var i = -1;
      for (i = 0; i < exprList.Count; i++) {
        if (line < exprList[i].tok.line) {
          break;
        }
      }
      if (i != 0) {
        if (exprList[i - 1] is ITEExpr iteExpr) {
          exprList.RemoveAt(i - 1);
          exprList.Insert(i - 1, EraseFromExpression(iteExpr, line));
        } else {
          exprList.RemoveAt(i - 1);
        }
      }
      if (exprList.Count == 0) {
        res = DafnyVerifierClient.CreateChange(ChangeTypeEnum.ChangeFunctionBody,
          DafnyVerifierClient.GetFirstToken(predicate.Body),
          DafnyVerifierClient.GetLastToken(predicate.Body),
          "true",
          "",
          "true");
        predicate.Body = Expression.CreateBoolLiteral(predicate.tok, true);
      } else {
        var body = exprList[0];
        for (int j = 1; j < exprList.Count; j++) {
          body = Expression.CreateAnd(body, exprList[j]);
        }
        var bodyString = "";
        using (var wr = new System.IO.StringWriter()) {
          var pr = new Printer(wr);
          pr.UniqueStringBeforeUnderscore = HoleEvaluator.RandomString(8);
          pr.PrintExpression(body, false);
          bodyString = wr.ToString();
        }

        res = DafnyVerifierClient.CreateChange(ChangeTypeEnum.ChangeFunctionBody,
          DafnyVerifierClient.GetFirstToken(predicate.Body),
          DafnyVerifierClient.GetLastToken(predicate.Body),
          bodyString,
          "",
          bodyString);
        predicate.Body = body;
      }
      return res;
    }

    public static Tuple<string, Change> Erase(Program program, string removeFileLine) {
      Tuple<string, Change> res = new Tuple<string, Change>("", null);
      var resItem1 = "";
      Change resItem2 = null;
      var fileLineList = removeFileLine.Split(',');
      foreach (var fileLineString in fileLineList) {
        var fileLineArray = fileLineString.Split(':');
        var file = fileLineArray[0];
        var line = Int32.Parse(fileLineArray[1]);
        if (program.ModuleSigs.Count == 0) {
          // unresolved program
          return res;
        }
        foreach (var kvp in program.ModuleSigs) {
          foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
            if (Path.GetFullPath(topLevelDecl.tok.filename) == file) {
              if (topLevelDecl.BodyStartTok.line <= line && line <= topLevelDecl.BodyEndTok.line) {
                if (topLevelDecl is Predicate) {
                  if (res.Item1 != "" && res.Item1 != topLevelDecl.FullDafnyName) {
                    throw new NotSupportedException("do not support removing from two lemmas at the same time!");
                  }
                  resItem1 = topLevelDecl.FullDafnyName;
                  resItem2 = EraseFromPredicate(topLevelDecl as Predicate, line);
                  res = new Tuple<string, Change>(resItem1, resItem2); 
                }
              }
            }
          }
          foreach (var topLevelDecl in ModuleDefinition.AllLemmas(kvp.Value.ModuleDef.TopLevelDecls)) {
            if (Path.GetFullPath(topLevelDecl.tok.filename) == file) {
              if (topLevelDecl.BodyStartTok.line <= line && line <= topLevelDecl.BodyEndTok.line) {
                var stmtList = topLevelDecl.Body.Body;
                // Console.WriteLine($"topLevelDecl : {topLevelDecl.FullDafnyName}");
                if (res.Item1 != "" && res.Item1 != topLevelDecl.FullDafnyName) {
                  throw new NotSupportedException("do not support removing from two lemmas at the same time!");
                }
                resItem1 = topLevelDecl.FullDafnyName;
                var i = -1;
                for (i = 0; i < stmtList.Count; i++) {
                  if (line < stmtList[i].Tok.line) {
                    break;
                  }
                }
                i--;
                var eraseRes = EraseFromStatement(topLevelDecl.Body.Body[i], line);
                resItem2 = eraseRes.Item2;
                if (i != -1 && eraseRes.Item1) {
                  var stmtToRemove = topLevelDecl.Body.Body[i];
                  resItem2 = DafnyVerifierClient.CreateChange(
                    ChangeTypeEnum.ChangeFunctionBody,
                    stmtToRemove.Tok,
                    stmtToRemove.EndTok,
                    "",
                    "",
                    "");
                  topLevelDecl.Body.Body.RemoveAt(i);
                }
                res = new Tuple<string, Change>(resItem1, resItem2);
              }
            }
          }
        }
      }
      return res;
    }

    // returns true if statement should also be removed in parent
    private static Tuple<bool, Change> EraseFromStatement(Statement stmt, int line) {
      if (stmt is BlockStmt) {
        return new Tuple<bool, Change>(false, EraseFromBlockStmt(stmt as BlockStmt, line));
      }
      else if (stmt is IfStmt) {
        return new Tuple<bool, Change>(false, EraseFromIfStmt(stmt as IfStmt, line));
      }
      else if (stmt is ForallStmt) {
        return EraseFromForallStmt(stmt as ForallStmt, line);
      }
      return new Tuple<bool, Change>(true, null);
    }

    private static Change EraseFromBlockStmt(BlockStmt blockStmt, int line) {
      for(int i = 0; i < blockStmt.Body.Count; i++) {
        if (blockStmt.Body[i].Tok.line <= line && line <= blockStmt.Body[i].EndTok.line) {
          var EraseResult = EraseFromStatement(blockStmt.Body[i], line);
          if (EraseResult.Item1) {
            EraseResult = new Tuple<bool, Change>(EraseResult.Item1, 
              DafnyVerifierClient.CreateChange(ChangeTypeEnum.ChangeFunctionBody,
                blockStmt.Body[i].Tok,
                blockStmt.Body[i].EndTok,
                "", "", "")
              );
            blockStmt.Body.RemoveAt(i);
          }
          return EraseResult.Item2;
        }
      }
      return null;
    }

    private static Change EraseFromIfStmt(IfStmt ifStmt, int line) {
      if (ifStmt.Thn.Tok.line <= line && line <= ifStmt.Thn.EndTok.line) {
        return EraseFromBlockStmt(ifStmt.Thn, line);
      }
      else if (ifStmt.Els != null) {
        return EraseFromStatement(ifStmt.Els, line).Item2;
      } else {
        return null;
      }
    }

    private static Tuple<bool, Change> EraseFromForallStmt(ForallStmt forallStmt, int line) {
      if (line < forallStmt.Body.Tok.line) {
        return new Tuple<bool, Change>(true, null);
      }
      else {
        var change = EraseFromStatement(forallStmt.Body, line);
        return new Tuple<bool, Change>(false, change.Item2);
      }
    }

    public static void InsertStmtListAtLine(Lemma lemma, List<Statement> stmtList, int lineNo)
    {
      if (lineNo == -1) {
        for (int i = 0; i < stmtList.Count; i++) {
          lemma.Body.Body.Insert(i, stmtList[i]);
        }
      }
      else {
        if (lemma.BodyStartTok.line <= lineNo && lineNo <= lemma.BodyEndTok.line) {
          var lemmaStmtList = lemma.Body.Body;
          if (lemmaStmtList.Count == 0) {
            for (int j = 0; j < stmtList.Count; j++) {
              lemma.Body.Body.Insert(j, stmtList[j]);
            }
          } else {
            var i = -1;
            for (i = 0; i < lemmaStmtList.Count; i++) {
              if (lineNo < lemmaStmtList[i].Tok.line) {
                break;
              }
            }
            // i--;
            if (i == lemmaStmtList.Count) {
              for (int j = 0; j < stmtList.Count; j++) {
                lemma.Body.Body.Insert(stmtList.Count, stmtList[j]);
              }
            }
            else if (InsertIntoStatement(lemma.Body.Body[i], stmtList, lineNo)) {
              for (int j = 0; j < stmtList.Count; j++) {
                lemma.Body.Body.Insert(i + j, stmtList[j]);
              }
            }
          }
        }
      }
    }

    public static bool InsertIntoStatement(Statement stmt, List<Statement> stmtList, int lineNo) {
      if (stmt.EndTok.line < lineNo) {
        return true;
      }
      if (stmt is BlockStmt) {
        InsertIntoBlockStmt(stmt as BlockStmt, stmtList, lineNo);
        return false;
      }
      else if (stmt is IfStmt) {
        InsertIntoIfStmt(stmt as IfStmt, stmtList, lineNo);
        return false;
      }
      else if (stmt is ForallStmt) {
        return InsertIntoForallStmt(stmt as ForallStmt, stmtList, lineNo);
      }
      return true;
    }

    public static void InsertIntoBlockStmt(BlockStmt blockStmt, List<Statement> stmtList, int lineNo) {
      int i = 0;
      for(i = 0; i < blockStmt.Body.Count; i++) {
        if (lineNo < blockStmt.Body[i].Tok.line) {
          break;
        }
      }
      if (i != 0) {
        if (InsertIntoStatement(blockStmt.Body[i - 1], stmtList, lineNo)) {
          for (int j = 0; j < stmtList.Count; j++) {
            blockStmt.Body.Insert(i + j, stmtList[j]);
          }
        }
      }
      else {
        for (int j = 0; j < stmtList.Count; j++) {
          blockStmt.Body.Insert(j, stmtList[j]);
        }
      }
    }

    private static void InsertIntoIfStmt(IfStmt ifStmt, List<Statement> stmtList, int lineNo) {
      if (ifStmt.Thn.Tok.line <= lineNo && lineNo <= ifStmt.Thn.EndTok.line) {
        InsertIntoBlockStmt(ifStmt.Thn, stmtList, lineNo);
      }
      else if (ifStmt.Els != null) {
        InsertIntoStatement(ifStmt.Els, stmtList, lineNo);
      }
    }

    private static bool InsertIntoForallStmt(ForallStmt forallStmt, List<Statement> stmtList, int lineNo) {
      if (lineNo < forallStmt.Body.Tok.line) {
        return true;
      }
      else {
        InsertIntoStatement(forallStmt.Body, stmtList, lineNo);
        return false;
      }
    }

    private static Statement GetStatementFromBlockStmt(BlockStmt blockStmt, int lineNo, int col) {
      int i = 0;
      for(i = 0; i < blockStmt.Body.Count; i++) {
        if (blockStmt.Body[i].Tok.line <= lineNo && lineNo <= blockStmt.Body[i].EndTok.line) {
          return GetStatement(blockStmt.Body[i], lineNo, col);
        }
      }
      // Should never reach here
      Contract.Assert(false);
      return null;
    }

    private static Statement GetStatementFromIfStmt(IfStmt ifStmt, int lineNo, int col) {
      if (lineNo <= ifStmt.Thn.Tok.line)
      {
          return ifStmt;
      }
      else if ((ifStmt.Thn.Tok.line < lineNo && lineNo < ifStmt.Thn.EndTok.line) ||
               (ifStmt.Thn.Tok.line == lineNo && lineNo < ifStmt.Thn.EndTok.line && ifStmt.Thn.Tok.col <= col) ||
               (ifStmt.Thn.Tok.line < lineNo && lineNo == ifStmt.Thn.EndTok.line && col <= ifStmt.Thn.EndTok.col)) {
        return GetStatementFromBlockStmt(ifStmt.Thn, lineNo, col);
      }
      else if (ifStmt.Els != null) {
        if ((ifStmt.Els.Tok.line < lineNo && lineNo < ifStmt.Els.EndTok.line) ||
            (ifStmt.Els.Tok.line == lineNo && lineNo < ifStmt.Els.EndTok.line && ifStmt.Els.Tok.col <= col) ||
            (ifStmt.Els.Tok.line < lineNo && lineNo == ifStmt.Els.EndTok.line && col <= ifStmt.Els.EndTok.col)) {
          return GetStatement(ifStmt.Els, lineNo, col);
        }
        else {
          return ifStmt;
        }
      }
      return ifStmt;
    }

    private static Statement GetStatementFromForallStmt(ForallStmt forallStmt, int lineNo, int col) {
      if (lineNo < forallStmt.Body.Tok.line || 
          (lineNo == forallStmt.Body.Tok.line && col < forallStmt.Body.Tok.col)) {
        return forallStmt;
      }
      else {
        return GetStatement(forallStmt.Body, lineNo, col);
      }
    }

    public static Statement GetStatement(Statement stmt, int lineNo, int col) {
      Contract.Assert(stmt.Tok.line <= lineNo && lineNo <= stmt.EndTok.line);
      // if (stmt.EndTok.line < lineNo) {
      //   return null;
      // }
      if (stmt is BlockStmt) {
        if ((stmt as BlockStmt).Body.Count == 0) {
          return stmt;
        }
        if (lineNo < (stmt as BlockStmt).Body[0].Tok.line) {
          return stmt;
        }
        return GetStatementFromBlockStmt(stmt as BlockStmt, lineNo, col);
      }
      else if (stmt is IfStmt) {
        return GetStatementFromIfStmt(stmt as IfStmt, lineNo, col);
      }
      else if (stmt is ForallStmt) {
        return GetStatementFromForallStmt(stmt as ForallStmt, lineNo, col);
      }
      else {
        return stmt;
      }
    }

    public static IToken GetStartingToken(Expression expr) {
      if (expr is ApplySuffix) {
        return GetStartingToken((expr as ApplySuffix).Lhs);
      }
      else {
        return expr.tok;
      }
    }

    public static IToken GetStartingToken(Statement stmt) {
      if (stmt is UpdateStmt updateStmt) {
        if (updateStmt.Lhss.Count > 0) {
          return GetStartingToken(updateStmt.Lhss[0]);
        }
        else {
          if (updateStmt.Rhss[0] is ExprRhs) {
            return GetStartingToken((updateStmt.Rhss[0] as ExprRhs).Expr);
          }
          else {
            throw new NotSupportedException();
          }
        }
      } else if (stmt is ConcreteUpdateStatement concreteUpdateStatement) {
        if (concreteUpdateStatement.Lhss.Count > 0) {
          return GetStartingToken(concreteUpdateStatement.Lhss[0]);
        }
        else {
          return stmt.Tok;
        }
      } else {
        return stmt.Tok;
      }
    }
  }
}
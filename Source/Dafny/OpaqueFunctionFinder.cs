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
  public class OpaqueFunctionFinder {

    public OpaqueFunctionFinder() {
    }

    private bool IsOpaque(Attributes attrs) {
      if (attrs == null) {
        return false;
      }
      if (attrs.Name == "opaque") {
        return true;
      }
      else return IsOpaque(attrs.Prev);
    }

    public IEnumerable<Function> GetOpaqueNonOpaquePredicates(Program program, bool findOpaque) {
      foreach (var kvp in program.ModuleSigs) {
        foreach (var d in kvp.Value.ModuleDef.TopLevelDecls) {
          var cl = d as TopLevelDeclWithMembers;
          if (cl != null) {
            foreach (var member in cl.Members) {
              if (member is Function && (member as Function).Body != null) {
                if (IsOpaque(member.Attributes) == findOpaque) {
                  yield return member as Function;
                }
              }
            }
          }
        }
      }
      yield break;
    }

    public IEnumerable<ExpressionFinder.StatementDepth> GetRevealStatements(Program program) {
      foreach (var opaqueFunc in GetOpaqueNonOpaquePredicates(program, true))
      {
        List<Expression> lhss = new List<Expression>();
        List<AssignmentRhs> rhss = new List<AssignmentRhs>();
        // lhss.Add(new IdentifierExpr(member.tok, $"temp_{cnt}_${i}"));
        rhss.Add(new ExprRhs(new ApplySuffix(opaqueFunc.tok, null, new NameSegment(opaqueFunc.tok, $"reveal_{opaqueFunc.ToString()}", new List<Type>()), new List<ActualBinding>(), opaqueFunc.tok)));
        UpdateStmt updateStmt = new UpdateStmt(opaqueFunc.tok, opaqueFunc.tok, lhss, rhss);
        yield return new ExpressionFinder.StatementDepth(updateStmt, 1);
      }
    }
  }
}
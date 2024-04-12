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
      var expressions = ExpressionFinder.ListArguments(program, func);
      Dictionary<string, HashSet<ExpressionFinder.ExpressionDepth>> typeToExpressionDict = ExpressionFinder.GetRawExpressions(program, func as MemberDecl, expressions);
      foreach (var t in typeToExpressionDict.Keys) {
        Console.WriteLine($"type = {t}");
        foreach (var e in typeToExpressionDict[t]) {
          Console.WriteLine(Printer.ExprToString(e.expr));
        }
        Console.WriteLine("---------------------------------------------");
      }
      foreach (var expr in expressions) {
        yield return expr;
      }
      yield break;
    }

  }
}
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
using System.Threading.Tasks;

namespace Microsoft.Dafny {
  public class IncludeParser {
    private Program program;
    private Dictionary<string, List<string>> affectedFilesList = new Dictionary<string, List<string>>();
    public string commonPrefix;
    private int commonPrefixLength;

    public IncludeParser(Program program) {
      this.program = program;
      CreateIncludeGraph();
    }

    public static string NormalizedRemoveLastBracket(string path)
    {
      var bracketIndex = path.IndexOf('[');
      if (bracketIndex != -1) {
        path = path.Remove(bracketIndex);
      }
      var directoryList = path.Split('/').ToList();
      for (int i = 0; i < directoryList.Count; i++) {
        if (directoryList[i] == "..") {
          directoryList.RemoveAt(i - 1);
          directoryList.RemoveAt(i - 1);
          i -= 2;
        }
      }
      return String.Join('/', directoryList);
    }

    public string Normalized(string path, bool removePrefix = true)
    {
      if (removePrefix) {
        path = path.Remove(0, commonPrefixLength);
      }
      var bracketIndex = path.IndexOf('[');
      if (bracketIndex != -1) {
        path = path.Remove(bracketIndex);
      }
      var directoryList = path.Split('/').ToList();
      for (int i = 0; i < directoryList.Count; i++) {
        if (directoryList[i] == "..") {
          directoryList.RemoveAt(i - 1);
          directoryList.RemoveAt(i - 1);
          i -= 2;
        }
      }
      return String.Join('/', directoryList);
    }

    private void CreateIncludeGraph()
    {
      var samples = new List<string>();
      if (program.DefaultModuleDef.Includes.Count == 0) {
        commonPrefix = Path.GetDirectoryName(program.FullName) + "/";
        commonPrefixLength = commonPrefix.Length;
        return;
      }
      foreach (var file in program.DefaultModuleDef.Includes) {
        samples.Add(file.canonicalPath);
      }
      commonPrefix = new string(
        samples.First().Substring(0, samples.Min(s => s.Length))
        .TakeWhile((c, i) => samples.All(s => s[i] == c)).ToArray());
      commonPrefixLength = commonPrefix.Length;
      foreach (var includePair in program.DefaultModuleDef.Includes) {
        var includedFilename = Normalized(includePair.includedFilename);
        var includerFilename = Normalized(includePair.includerFilename);
        if (!affectedFilesList.ContainsKey(includedFilename)) {
          affectedFilesList.Add(includedFilename, new List<string>());
        }
        affectedFilesList[includedFilename].Add(includerFilename);
      }
    }

    public IEnumerable<string> GetListOfAffectedFilesBy(string file) {
      yield return file;
      if (!affectedFilesList.ContainsKey(file)) {
        yield break;
      }
      foreach (var affected in affectedFilesList[file]) {
        foreach (var x in GetListOfAffectedFilesBy(affected)) {
          yield return x;
        }
      }
    }
  }
}
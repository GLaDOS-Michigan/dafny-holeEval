using System;
using System.Text;
using System.IO;
using System.Text.Json;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Diagnostics;
using System.Reflection;
using System.Linq;
using Microsoft.Boogie;
using System.Threading.Tasks;

namespace Microsoft.Dafny {
    public class OpaqueEvaluator {
        private DafnyVerifierClient dafnyVerifier = null;
        private IncludeParser includeParser = null;
        private List<string> affectedFiles = new List<string>();
        private TasksList tasksList = null;
        private Dictionary<string, VerificationTaskArgs> tasksListDictionary = new Dictionary<string, VerificationTaskArgs>();

        public OpaqueEvaluator() {
        }

        public static string GetNormalizedPath(string path)
        {
            var bracketIndex = path.IndexOf('[');
            if (bracketIndex != -1) {
                path = path.Remove(bracketIndex);
            }
            return Path.GetFullPath(new Uri(path).LocalPath)
                       .TrimEnd(Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar);
        }

        public static Function FindFunction(MemberDecl member, Function func) {
            if (member.Name == func.Name && 
                GetNormalizedPath(member.tok.filename) == GetNormalizedPath(func.tok.filename)) {
                return member as Function;
            }
            else {
                return null;
            }
        }

        public static Function FindFunction(TopLevelDecl topLevelDecl, Function func) {
            if (topLevelDecl is LiteralModuleDecl) {
                return FindFunction((topLevelDecl as LiteralModuleDecl).ModuleDef, func);
            }
            else if (topLevelDecl is AliasModuleDecl || 
                     topLevelDecl is TypeSynonymDecl ||
                     topLevelDecl is ModuleExportDecl) {
                return null;
            }
            else if (topLevelDecl is TypeSynonymDecl) {
                return null;
            }
            else if (topLevelDecl is TopLevelDeclWithMembers) {
                foreach (var member in (topLevelDecl as TopLevelDeclWithMembers).Members) {
                    var result = FindFunction(member, func);
                    if (result != null) {
                        return result;
                    }
                }
                return null;
            }
            else if (topLevelDecl is AbstractModuleDecl) {
                return null;
            }
            else {
                throw new NotImplementedException();
            }
        }

        public static Function FindFunction(ModuleDefinition moduleDef, Function func) {
            foreach (var topLevelDecl in moduleDef.TopLevelDecls) {
                var result = FindFunction(topLevelDecl, func);
                if (result != null) {
                    return result;
                }
            }
            return null;
        }

        public Tuple<Program, Dictionary<string, List<Change>>> CreateOpaqueFunc(Program program, Function nonOpaqueFunc) {
            Cloner cloner = new Cloner();
            var nProgram = cloner.CloneProgram(program);
            var functionInProgramAST = FindFunction(nProgram.DefaultModuleDef, nonOpaqueFunc);
            Dictionary<string, List<Change>> changeList = new Dictionary<string, List<Change>>();
            Contract.Assert(functionInProgramAST != null);
            if (functionInProgramAST is Function) {
                var func = functionInProgramAST as Function;
                func.Attributes = new Attributes("opaque", new List<Expression>(), func.Attributes);
                string funcString;
                using (var wr = new System.IO.StringWriter()) {
                    var pr = new Printer(wr);
                    pr.PrintFunction(func, 0, false);
                    funcString = wr.ToString();
                }
                Change change = DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddOpaqueAttribute, func.tok, func.BodyEndTok, funcString, func.WhatKind, "{:opaque}");
                DafnyVerifierClient.AddFileToChangeList(ref changeList, change);
                return new Tuple<Program, Dictionary<string, List<Change>>>(nProgram, changeList);
            }
            else {
                throw new NotImplementedException();
            }
        }

        private string GetChangeListString(int index) {
            ChangeList changes = new ChangeList();
            foreach (var fileChangePair in EnvIdToChangeList[index].Item2) {
                foreach (var change in fileChangePair.Value) {
                    changes.Changes.Add(change);
                }
            }
            return Google.Protobuf.JsonFormatter.Default.Format(changes);
        }

        private string GetRequestString(int index) {
            var TSRequest = dafnyVerifier.requestsList[index] as TwoStageRequest;
            return TSRequest.ToString() + "\n";
        }

        private string GetResponseString(int index) {
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
                string sanitizedFuncName = "";
                if (request.Arguments[request.Arguments.Count - 1].StartsWith("/proc:*")) {
                    sanitizedFuncName = request.Arguments[request.Arguments.Count - 1].Substring(7);
                }
                if (DafnyOptions.O.HoleEvaluatorVerboseMode)
                {
                    Console.WriteLine($"{index} output for maintain lemma:\n{response}");
                }
                Result res = DafnyVerifierClient.IsCorrectOutputForNoErrors(response);
                if (res != Result.CorrectProof)
                {
                    result[i] = DafnyVerifierClient.GetFailingFunctionResults(sanitizedFuncName, filePath, response);
                }
            }
            return result;
        }

        public Dictionary<int, Tuple<Program, Dictionary<string, List<Change>>>> EnvIdToChangeList =
                new Dictionary<int, Tuple<Program, Dictionary<string, List<Change>>>>();
        public Dictionary<int, Function> EnvIdToNonOpaqueFunc = new Dictionary<int, Function>();
        public Dictionary<string, ModuleDefinition> FileNameToModuleDict = new Dictionary<string, ModuleDefinition>();
        public PriorityQueue<int, UInt64> ExecutionTimeEnvIdTupleList = new PriorityQueue<int, UInt64>();

        public string ChangeListToString(int envId) {
            string output = "";
            if (EnvIdToNonOpaqueFunc[envId] == null) {
                output += $"envId={envId}\tno_change\n";
            }
            else {
                output += $"envId={envId}\t{EnvIdToNonOpaqueFunc[envId].FullDafnyName}\n";
                foreach (var changeFileKV in EnvIdToChangeList[envId].Item2) {
                    foreach (var change in changeFileKV.Value) {
                        output += $"file={changeFileKV.Key}; {change.ToString()}\n";
                    }
                }
            }
            return output;
        }

        public bool ProcessOutput(int envId) {
            var res = GetFailingProofs(envId);
            if (res.Count == 0) {
                Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: found new function to make opaque\n");
                Console.WriteLine(ChangeListToString(envId));
                return true;
            }
            var opaquedFunc = EnvIdToNonOpaqueFunc[envId];
            var opaquedFuncName = opaquedFunc == null ? "no change" : opaquedFunc.FullDafnyName;
            foreach (var failedProofList in res.Values) {
                if (failedProofList == null) {
                    Console.WriteLine($"skipped opaquing {opaquedFuncName} due to not supported output");
                }
            }
            return false;
        }

        public ChangeList ParseChangeProtobuf(string path) {
            var input = File.ReadAllText(path);
            var changeList = Google.Protobuf.JsonParser.Default.Parse<ChangeList>(input);
            return changeList;
        }

        public int GetTimelimitMultiplier(Attributes attrs) {
            if (attrs == null) {
                return 1;
            } else {
                if (attrs.Name == "timeLimitMultiplier") {
                    int multiplier = 0;
                    Contract.Assert(Int32.TryParse(Printer.ExprToString(attrs.Args[0]), out multiplier));
                    return multiplier;
                } else {
                    return GetTimelimitMultiplier(attrs.Prev);
                }
            }
        }

        public void AddVerificationRequestPerCallable(int envId, string filename, List<string> baseArgs) {

            foreach (var func in ModuleDefinition.AllFunctions(FileNameToModuleDict[filename].TopLevelDecls)) {
                baseArgs.Add($"/proc:*{func.FullSanitizedName}");
                var timeLimitMultiplier = GetTimelimitMultiplier(func.Attributes);
                dafnyVerifier.AddVerificationRequestToEnvironment(envId, "", filename, baseArgs, $"{timeLimitMultiplier}m");
                baseArgs.RemoveAt(baseArgs.Count - 1);
            }
            foreach (var lemma in ModuleDefinition.AllLemmas(FileNameToModuleDict[filename].TopLevelDecls)) {
                baseArgs.Add($"/proc:*{lemma.FullSanitizedName}");
                var timeLimitMultiplier = GetTimelimitMultiplier(lemma.Attributes);
                dafnyVerifier.AddVerificationRequestToEnvironment(envId, "", filename, baseArgs, $"{timeLimitMultiplier}m");
                baseArgs.RemoveAt(baseArgs.Count - 1);
            }
        }

        public async Task<bool> Evaluate(Program program, Program unresolvedProgram) {
            if (DafnyOptions.O.HoleEvaluatorCommands != null) {
                var input = File.ReadAllText(DafnyOptions.O.HoleEvaluatorCommands);
                tasksList = Google.Protobuf.JsonParser.Default.Parse<TasksList>(input);
                foreach (var task in tasksList.Tasks) {
                    tasksListDictionary.Add(task.Path, task);
                }
            }
            dafnyVerifier = new DafnyVerifierClient(DafnyOptions.O.HoleEvaluatorServerIpPortList, "output_opaqueEval", ProcessOutput);
            includeParser = new IncludeParser(program);
            dafnyVerifier.InitializeBaseFoldersInRemoteServers(program, includeParser.commonPrefix);

            var opaqueFunctionFinder = new OpaqueFunctionFinder();
            int startEnvId = 0;
            int endEnvId = -1;

            foreach (var kvp in program.ModuleSigs) {
                if (kvp.Value.ModuleDef.tok.filename != null) {
                    var filename = includeParser.Normalized(kvp.Value.ModuleDef.tok.filename);
                    FileNameToModuleDict[filename] = kvp.Value.ModuleDef;
                }
            }

            foreach (var nonOpaqueFunc in opaqueFunctionFinder.GetOpaqueNonOpaquePredicates(program, false)) {
                if (DafnyOptions.O.HoleEvaluatorSpecifiedFunc != "" && nonOpaqueFunc.FullDafnyName != DafnyOptions.O.HoleEvaluatorSpecifiedFunc) {
                    continue;
                }
                if (nonOpaqueFunc.EnclosingClass is not DefaultClassDecl) {
                    continue;
                }
                var newProgramChangeTuple = CreateOpaqueFunc(unresolvedProgram, nonOpaqueFunc);
                var envId = dafnyVerifier.CreateEnvironment(includeParser, newProgramChangeTuple.Item2);
                Console.WriteLine($"envId={envId}\tmaking {nonOpaqueFunc.FullDafnyName} opaque");
                EnvIdToChangeList[envId] = newProgramChangeTuple;
                EnvIdToNonOpaqueFunc[envId] = nonOpaqueFunc;
                var filename = includeParser.Normalized(nonOpaqueFunc.tok.filename);
                var affectedFiles = includeParser.GetListOfAffectedFilesBy(filename).ToList();
                affectedFiles = affectedFiles.Distinct().ToList();
                foreach (var file in affectedFiles) {
                    AddVerificationRequestPerCallable(envId, file, tasksListDictionary[file].Arguments.ToList());
                    // dafnyVerifier.AddVerificationRequestToEnvironment(envId, "", file, tasksListDictionary[file].Arguments.ToList());
                }
                if (envId > endEnvId) {
                    endEnvId = envId;
                }
                // if (endEnvId == 2) {
                //     break;
                // }
            }
            await dafnyVerifier.RunVerificationRequestsStartingFromEnvironment(0, false);
            int newEndEnvId = endEnvId;
            int retries = 0;
            HashSet<int> correctEnvironments = new HashSet<int>();
            while (retries < 4)
            {
                for (int i = startEnvId; i <= endEnvId; i++)
                {
                    var res = GetFailingProofs(i);
                    if (res.Count == 0) {
                        if (!correctEnvironments.Contains(i)) {
                            correctEnvironments.Add(i);
                        }
                        continue;
                    }
                    var changeList = EnvIdToChangeList[i].Item2;
                    var opaquedFunc = EnvIdToNonOpaqueFunc[i];
                    var opaquedFuncModuleName = opaquedFunc.EnclosingClass.FullDafnyName;
                    bool shouldSkip = false;
                    foreach (var failedProofList in res.Values)
                    {
                        if (failedProofList == null) {
                            Console.WriteLine($"skip opaquing {opaquedFunc.FullDafnyName}");
                            shouldSkip = true;
                            break;
                        }
                        bool hasCheckedImport = false;
                        foreach (var failedProof in failedProofList)
                        {
                            MemberDecl resolvedFailedFunc;
                            if (failedProof.FuncBoogieName != null) {
                                var sanitizedFuncName = failedProof.FuncBoogieName.Substring(failedProof.FuncBoogieName.IndexOf("$$") + 2);
                                resolvedFailedFunc = HoleEvaluator.GetMember(program, sanitizedFuncName, true);
                            }
                            else {
                                resolvedFailedFunc = HoleEvaluator.GetMember(program, includeParser, includeParser.Normalized(failedProof.Filename, false), failedProof.Line);
                                failedProof.FuncBoogieName = $"Impl$${resolvedFailedFunc.FullSanitizedName}";
                            }
                            Contract.Assert(resolvedFailedFunc != null);

                            var moduleDef = resolvedFailedFunc.EnclosingClass.EnclosingModuleDefinition;
                            var importType = DafnyVerifierClient.GetImportType(opaquedFuncModuleName, moduleDef);
                            string revealPrefixModuleName = "";
                            if (importType.Item1 != DafnyVerifierClient.ImportType.CompleteImport) {
                                revealPrefixModuleName = $"{opaquedFuncModuleName}.";
                            }
                            if (!hasCheckedImport) {
                                hasCheckedImport = true;
                                if (importType.Item1 == DafnyVerifierClient.ImportType.NoImport) {
                                    Change openModuleChange = DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddImport, moduleDef.BodyStartTok, moduleDef.BodyStartTok, $"{{import {opaquedFuncModuleName}", "", $"{{import {opaquedFuncModuleName}");
                                    DafnyVerifierClient.AddFileToChangeList(ref changeList, openModuleChange);
                                }
                                else if (importType.Item1 == DafnyVerifierClient.ImportType.SpecifiedImport) {
                                    Contract.Assert(importType.Item2.Exports.Count > 0);
                                    var lastExport = importType.Item2.Exports[importType.Item2.Exports.Count - 1];
                                    Change openModuleChange = DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddImport, importType.Item2.tok, lastExport, $"import {opaquedFuncModuleName}", "import", $"import {opaquedFuncModuleName}");
                                    DafnyVerifierClient.AddFileToChangeList(ref changeList, openModuleChange);
                                }
                            }

                            if (failedProof.Line < resolvedFailedFunc.BodyStartTok.line ||
                                (failedProof.Line == resolvedFailedFunc.BodyStartTok.line 
                                    && failedProof.Column < resolvedFailedFunc.BodyStartTok.col) || (retries >= 3)) {
                                if (resolvedFailedFunc is Function) {
                                    var unresolvedFailedFunc = HoleEvaluator.GetMemberFromUnresolved(unresolvedProgram, resolvedFailedFunc.FullDafnyName) as Function;
                                    foreach (var req in unresolvedFailedFunc.Req) {
                                        if (includeParser.Normalized(req.E.tok.filename) != includeParser.Normalized(unresolvedFailedFunc.tok.filename)) {
                                            continue;
                                        }
                                        var firstToken = DafnyVerifierClient.GetFirstToken(req);
                                        var lastToken = DafnyVerifierClient.GetLastToken(req);
                                        if (firstToken != null && lastToken != null && 
                                            ((firstToken.line <= failedProof.Line && failedProof.Line <= lastToken.line) ||
                                            retries >= 2)) {
                                            Change reqChange = DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddRevealStatement, firstToken, lastToken, $"requires ({revealPrefixModuleName}reveal_{opaquedFunc.Name}(); {Printer.ExprToString(req.E)})", "requires", $"{revealPrefixModuleName}reveal_{opaquedFunc.Name}();");
                                            DafnyVerifierClient.AddFileToChangeList(ref changeList, reqChange);
                                        }
                                    }

                                    foreach (var ens in unresolvedFailedFunc.Ens) {
                                        if (includeParser.Normalized(ens.E.tok.filename) != includeParser.Normalized(unresolvedFailedFunc.tok.filename)) {
                                            continue;
                                        }
                                        var firstToken = DafnyVerifierClient.GetFirstToken(ens);
                                        var lastToken = DafnyVerifierClient.GetLastToken(ens);
                                        if (firstToken != null && lastToken != null && 
                                            ((firstToken.line <= failedProof.Line && failedProof.Line <= lastToken.line) ||
                                            retries >= 2)) {
                                            Change ensChange = DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddRevealStatement, firstToken, lastToken, $"ensures ({revealPrefixModuleName}reveal_{opaquedFunc.Name}(); {Printer.ExprToString(ens.E)})", "ensures", $"{revealPrefixModuleName}reveal_{opaquedFunc.Name}();");
                                            DafnyVerifierClient.AddFileToChangeList(ref changeList, ensChange);
                                        }
                                    }
                                }
                                else if (resolvedFailedFunc is Lemma) {
                                    var unresolvedFailedLemma = HoleEvaluator.GetMemberFromUnresolved(unresolvedProgram, resolvedFailedFunc.FullDafnyName) as Lemma;
                                    foreach (var req in unresolvedFailedLemma.Req) {
                                        if (includeParser.Normalized(req.E.tok.filename) != includeParser.Normalized(unresolvedFailedLemma.tok.filename)) {
                                            continue;
                                        }
                                        var firstToken = DafnyVerifierClient.GetFirstToken(req);
                                        var lastToken = DafnyVerifierClient.GetLastToken(req);
                                        if (firstToken != null && lastToken != null && 
                                            ((firstToken.line <= failedProof.Line && failedProof.Line <= lastToken.line) ||
                                            retries >= 2)) {
                                            Change reqChange = DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddRevealStatement, firstToken, lastToken, $"requires ({revealPrefixModuleName}reveal_{opaquedFunc.Name}(); {Printer.ExprToString(req.E)})", "requires", $"{revealPrefixModuleName}reveal_{opaquedFunc.Name}();");
                                            DafnyVerifierClient.AddFileToChangeList(ref changeList, reqChange);
                                        }
                                    }

                                    foreach (var ens in unresolvedFailedLemma.Ens) {
                                        if (includeParser.Normalized(ens.E.tok.filename) != includeParser.Normalized(unresolvedFailedLemma.tok.filename)) {
                                            continue;
                                        }
                                        var firstToken = DafnyVerifierClient.GetFirstToken(ens);
                                        var lastToken = DafnyVerifierClient.GetLastToken(ens);
                                        if (firstToken != null && lastToken != null && 
                                            ((firstToken.line <= failedProof.Line && failedProof.Line <= lastToken.line) ||
                                            retries >= 2)) {
                                            Change ensChange = DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddRevealStatement, firstToken, lastToken, $"ensures ({revealPrefixModuleName}reveal_{opaquedFunc.Name}(); {Printer.ExprToString(ens.E)})", "ensures", $"{revealPrefixModuleName}reveal_{opaquedFunc.Name}();");
                                            DafnyVerifierClient.AddFileToChangeList(ref changeList, ensChange);
                                        }
                                    }
                                } else if (resolvedFailedFunc is Method) {
                                    var unresolvedFailedMethod = HoleEvaluator.GetMemberFromUnresolved(unresolvedProgram, resolvedFailedFunc.FullDafnyName) as Method;
                                    foreach (var req in unresolvedFailedMethod.Req) {
                                        if (includeParser.Normalized(req.E.tok.filename) != includeParser.Normalized(unresolvedFailedMethod.tok.filename)) {
                                            continue;
                                        }
                                        var firstToken = DafnyVerifierClient.GetFirstToken(req);
                                        var lastToken = DafnyVerifierClient.GetLastToken(req);
                                        if (firstToken != null && lastToken != null && 
                                            ((firstToken.line <= failedProof.Line && failedProof.Line <= lastToken.line) ||
                                            retries >= 2)) {
                                            Change reqChange = DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddRevealStatement, firstToken, lastToken, $"requires ({revealPrefixModuleName}reveal_{opaquedFunc.Name}(); {Printer.ExprToString(req.E)})", "requires", $"{revealPrefixModuleName}reveal_{opaquedFunc.Name}();");
                                            DafnyVerifierClient.AddFileToChangeList(ref changeList, reqChange);
                                        }
                                    }

                                    foreach (var ens in unresolvedFailedMethod.Ens) {
                                        if (includeParser.Normalized(ens.E.tok.filename) != includeParser.Normalized(unresolvedFailedMethod.tok.filename)) {
                                            continue;
                                        }
                                        var firstToken = DafnyVerifierClient.GetFirstToken(ens);
                                        var lastToken = DafnyVerifierClient.GetLastToken(ens);
                                        if (firstToken != null && lastToken != null && 
                                            ((firstToken.line <= failedProof.Line && failedProof.Line <= lastToken.line) ||
                                            retries >= 2)) {
                                            Change ensChange = DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddRevealStatement, firstToken, lastToken, $"ensures ({revealPrefixModuleName}reveal_{opaquedFunc.Name}(); {Printer.ExprToString(ens.E)})", "ensures", $"{revealPrefixModuleName}reveal_{opaquedFunc.Name}();");
                                            DafnyVerifierClient.AddFileToChangeList(ref changeList, ensChange);
                                        }
                                    }
                                }
                            }

                            if (resolvedFailedFunc != null && resolvedFailedFunc is Function)
                            {
                                var unresolvedFailedFunc = HoleEvaluator.GetMemberFromUnresolved(unresolvedProgram, resolvedFailedFunc.FullDafnyName) as Function;
                                var newFuncBodyStr = $"{{{revealPrefixModuleName}reveal_{opaquedFunc.Name}();\n{Printer.ExprToString(unresolvedFailedFunc.Body)}}}";
                                Change change = DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddRevealStatement, unresolvedFailedFunc.BodyStartTok, unresolvedFailedFunc.BodyEndTok, newFuncBodyStr, "", $"{revealPrefixModuleName}reveal_{opaquedFunc.Name}();");
                                DafnyVerifierClient.AddFileToChangeList(ref changeList, change);
                            }
                            else if (resolvedFailedFunc != null && resolvedFailedFunc is Lemma) {
                                var unresolvedFailedLemma = HoleEvaluator.GetMemberFromUnresolved(unresolvedProgram, resolvedFailedFunc.FullDafnyName) as Lemma;
                                if (unresolvedFailedLemma.Body == null) {
                                    var fuelAttributeExprList = new List<Expression>();
                                    fuelAttributeExprList.Add(new NameSegment(opaquedFunc.tok, opaquedFunc.Name, null));
                                    fuelAttributeExprList.Add(Expression.CreateIntLiteral(Token.NoToken, 1));
                                    fuelAttributeExprList.Add(Expression.CreateIntLiteral(Token.NoToken, 2));
                                    unresolvedFailedLemma.Attributes = new Attributes("fuel", fuelAttributeExprList, unresolvedFailedLemma.Attributes);
                                    string lemmaString;
                                    using (var wr = new System.IO.StringWriter())
                                    {
                                        var pr = new Printer(wr);
                                        pr.PrintMethod(unresolvedFailedLemma, 0, false);
                                        lemmaString = wr.ToString();
                                    }
                                    Change change = DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddFuelAttribute, unresolvedFailedLemma.tok, unresolvedFailedLemma.BodyEndTok, lemmaString, unresolvedFailedLemma.WhatKind, $"{{:fuel {opaquedFunc.Name}, 1, 2}}");
                                    unresolvedFailedLemma.Attributes = unresolvedFailedLemma.Attributes.Prev;
                                    DafnyVerifierClient.AddFileToChangeList(ref changeList, change);
                                } else if (failedProof.Line < unresolvedFailedLemma.Body.Tok.line || retries >= 2) {
                                    var newLemmaBodyStr = $"{{{revealPrefixModuleName}reveal_{opaquedFunc.Name}();\n{Printer.StatementToString(unresolvedFailedLemma.Body)}\n}}";
                                    Change change = DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddRevealStatement, unresolvedFailedLemma.Body.Tok, unresolvedFailedLemma.BodyEndTok, newLemmaBodyStr, "", $"{revealPrefixModuleName}reveal_{opaquedFunc.Name}();");
                                    DafnyVerifierClient.AddFileToChangeList(ref changeList, change);
                                } else {
                                    var changingStmt = CodeModifier.GetStatement(unresolvedFailedLemma.Body, failedProof.Line, failedProof.Column);
                                    string newStmtStr = "";
                                    if (changingStmt is VarDeclStmt) {
                                        newStmtStr = $"{revealPrefixModuleName}reveal_{opaquedFunc.Name}();\n{Printer.StatementToString(changingStmt)}\n";
                                    } else {
                                        newStmtStr = $"{{\n{revealPrefixModuleName}reveal_{opaquedFunc.Name}();\n{Printer.StatementToString(changingStmt)}\n}}";
                                    }
                                    Change change = DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddRevealStatement, CodeModifier.GetStartingToken(changingStmt), changingStmt.EndTok, newStmtStr, "", $"{revealPrefixModuleName}reveal_{opaquedFunc.Name}();");
                                    DafnyVerifierClient.AddFileToChangeList(ref changeList, change);
                                }
                            }
                            else if (resolvedFailedFunc != null && resolvedFailedFunc is Method) {
                                var unresolvedFailedMethod = HoleEvaluator.GetMemberFromUnresolved(unresolvedProgram, resolvedFailedFunc.FullDafnyName) as Method;
                                Contract.Assert(unresolvedFailedMethod != null);
                                if (unresolvedFailedMethod.Body == null) {
                                    var fuelAttributeExprList = new List<Expression>();
                                    fuelAttributeExprList.Add(new NameSegment(opaquedFunc.tok, opaquedFunc.Name, null));
                                    fuelAttributeExprList.Add(Expression.CreateIntLiteral(Token.NoToken, 1));
                                    fuelAttributeExprList.Add(Expression.CreateIntLiteral(Token.NoToken, 2));
                                    unresolvedFailedMethod.Attributes = new Attributes("fuel", fuelAttributeExprList, unresolvedFailedMethod.Attributes);
                                    string methodString;
                                    using (var wr = new System.IO.StringWriter())
                                    {
                                        var pr = new Printer(wr);
                                        pr.PrintMethod(unresolvedFailedMethod, 0, false);
                                        methodString = wr.ToString();
                                    }
                                    Change change = DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddFuelAttribute, unresolvedFailedMethod.tok, unresolvedFailedMethod.BodyEndTok, methodString, unresolvedFailedMethod.WhatKind, $"{{:fuel {opaquedFunc.Name}, 1, 2}}");
                                    unresolvedFailedMethod.Attributes = unresolvedFailedMethod.Attributes.Prev;
                                    DafnyVerifierClient.AddFileToChangeList(ref changeList, change);
                                } else if (failedProof.Line < unresolvedFailedMethod.Body.Tok.line || retries >= 2) {
                                    var newMethodBodyStr = $"{{{revealPrefixModuleName}reveal_{opaquedFunc.Name}();\n{Printer.StatementToString(unresolvedFailedMethod.Body)}\n}}";
                                    Change change = DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddRevealStatement, unresolvedFailedMethod.Body.Tok, unresolvedFailedMethod.Body.EndTok, newMethodBodyStr, "", $"{revealPrefixModuleName}reveal_{opaquedFunc.Name}();");
                                    DafnyVerifierClient.AddFileToChangeList(ref changeList, change);
                                } else {
                                    var changingStmt = CodeModifier.GetStatement(unresolvedFailedMethod.Body, failedProof.Line, failedProof.Column);
                                    string newStmtStr = "";
                                    if (changingStmt is VarDeclStmt) {
                                        newStmtStr = $"{revealPrefixModuleName}reveal_{opaquedFunc.Name}();\n{Printer.StatementToString(changingStmt)}\n";
                                    } else {
                                        newStmtStr = $"{{\n{revealPrefixModuleName}reveal_{opaquedFunc.Name}();\n{Printer.StatementToString(changingStmt)}\n}}";
                                    }
                                    Change change = DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddRevealStatement, CodeModifier.GetStartingToken(changingStmt), changingStmt.EndTok, newStmtStr, "", $"{revealPrefixModuleName}reveal_{opaquedFunc.Name}();");
                                    DafnyVerifierClient.AddFileToChangeList(ref changeList, change);
                                }
                            }
                            else {
                                throw new NotImplementedException();
                            }
                        }
                        // Change change = new Change()
                    }
                    if (shouldSkip) {
                        continue;
                    }
                    var envId = dafnyVerifier.CreateEnvironment(includeParser, changeList);
                    EnvIdToChangeList[envId] = EnvIdToChangeList[i];
                    EnvIdToNonOpaqueFunc[envId] = opaquedFunc;
                    Console.WriteLine($"envId={envId}\tretry of making {opaquedFunc.FullDafnyName} opaque");
                    var TSRequest = dafnyVerifier.requestsList[i] as TwoStageRequest;
                    foreach (var failedProofList in res)
                    {
                        var fileIndex = failedProofList.Key;
                        var file = TSRequest.SecondStageRequestsList[fileIndex].Path;
                        var argList = TSRequest.SecondStageRequestsList[fileIndex].Arguments.ToList();
                        var timeout = TSRequest.SecondStageRequestsList[fileIndex].Timeout;
                        // foreach (var failedProof in failedProofList.Value) {
                        //     var sanitizedFuncName = failedProof.FuncBoogieName.Substring(failedProof.FuncBoogieName.IndexOf("$$") + 2);
                        //     argList.Add($"/proc:*{sanitizedFuncName}*");
                        // }
                        // argList = argList.Distinct().ToList();
                        dafnyVerifier.AddVerificationRequestToEnvironment(envId, "", file, argList, timeout);
                    }
                    if (envId > newEndEnvId)
                    {
                        newEndEnvId = envId;
                    }
                }
                startEnvId = endEnvId + 1;
                if (endEnvId == newEndEnvId) {
                    break;
                }
                endEnvId = newEndEnvId;
                await dafnyVerifier.RunVerificationRequestsStartingFromEnvironment(startEnvId, false);
                retries++;
            }
            for (int i = 0; i <= endEnvId; i++)
            {
                if (!correctEnvironments.Contains(i)) {
                    var res = GetFailingProofs(i);
                    if (res.Count == 0) {
                        correctEnvironments.Add(i);
                    }
                }
            }
            Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: correct solutions found: {correctEnvironments.Count}");
            Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: number of environments checked: {endEnvId}");
            if (DafnyOptions.O.HoleEvaluatorLogOutputs != "") {
                try {
                    var outputDir = DafnyOptions.O.HoleEvaluatorLogOutputs;
                    if (!Directory.Exists(outputDir))
                    {
                        Directory.CreateDirectory(outputDir);
                    }
                    for (int i = 0; i <= endEnvId; i++) {
                        File.WriteAllText($"{outputDir}/change_{i}.txt", GetChangeListString(i));
                        File.WriteAllText($"{outputDir}/request_{i}.txt", GetRequestString(i));
                        File.WriteAllText($"{outputDir}/response_{i}.txt", GetResponseString(i));
                    }
                } catch (Exception e) {
                    Console.WriteLine($"Error while writing logs: {e.ToString()}");
                }
            }
            if (correctEnvironments.Count == 0) {
                return true;
            }
            HashSet<int> finalEnvironments = new HashSet<int>();
            var noChangeEnvId = dafnyVerifier.CreateEnvironment(includeParser, new Dictionary<string, List<Change>>());
            finalEnvironments.Add(noChangeEnvId);
            EnvIdToChangeList[noChangeEnvId] = null;
            EnvIdToNonOpaqueFunc[noChangeEnvId] = null;
            foreach (var task in tasksListDictionary) {
                dafnyVerifier.AddVerificationRequestToEnvironment(noChangeEnvId, "", task.Key, task.Value.Arguments.ToList());
            }
            Console.WriteLine($"envId={noChangeEnvId}\tno change environment");
            foreach (var envId in correctEnvironments) {
                var newEnvId = dafnyVerifier.CreateEnvironment(includeParser, EnvIdToChangeList[envId].Item2);
                EnvIdToChangeList[newEnvId] = EnvIdToChangeList[envId];
                EnvIdToNonOpaqueFunc[newEnvId] = EnvIdToNonOpaqueFunc[envId];
                Console.WriteLine($"envId={newEnvId}\tfinal execution of making {EnvIdToNonOpaqueFunc[envId].FullDafnyName} opaque");
                finalEnvironments.Add(newEnvId);
                foreach (var task in tasksListDictionary) {
                    dafnyVerifier.AddVerificationRequestToEnvironment(newEnvId, "", task.Key, task.Value.Arguments.ToList());
                }
            }
            await dafnyVerifier.RunVerificationRequestsStartingFromEnvironment(noChangeEnvId, true);
            foreach (var envId in finalEnvironments) {
                if (DafnyOptions.O.HoleEvaluatorLogOutputs != "") {
                    var outputDir = DafnyOptions.O.HoleEvaluatorLogOutputs;
                    File.WriteAllText($"{outputDir}/request_{envId}.txt", GetRequestString(envId));
                    File.WriteAllText($"{outputDir}/response_{envId}.txt", GetResponseString(envId));
                }
                var TSRequest = dafnyVerifier.requestsList[envId] as TwoStageRequest;
                var TSOutput = dafnyVerifier.dafnyOutput[TSRequest] as VerificationResponseList;
                var execTime = TSOutput.ExecutionTimeInMs;
                ExecutionTimeEnvIdTupleList.Enqueue(envId, execTime);
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
                    Result res = DafnyVerifierClient.IsCorrectOutputForNoErrors(response);
                    if (res != Result.CorrectProof)
                    {
                        if (EnvIdToNonOpaqueFunc[envId] == null) {
                            Console.WriteLine("no change results into failure!");
                        }
                        else {
                            Console.WriteLine($"verifying {filePath} failed in when opaquing {EnvIdToNonOpaqueFunc[envId].Name}");
                        }
                    }
                }
                if (EnvIdToNonOpaqueFunc[envId] == null) {
                    Console.WriteLine($"execution time with no change\t\t {execTime}ms = {execTime/60000.0:0.00}min");
                }
                else {
                    Console.WriteLine($"execution time when opaquing {EnvIdToNonOpaqueFunc[envId].Name}\t\t {execTime}ms = {execTime/60000.0:0.00}min");
                }
            }
            // for (int i = 0; i < 10; i++) {
                
            // }
            return true;
        }
    }
}
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

using Change = Microsoft.Dafny.DafnyVerifierClient.Change;

namespace Microsoft.Dafny {
    public class OpaqueEvaluator {
        private DafnyVerifierClient dafnyVerifier = null;
        private IncludeParser includeParser = null;
        private List<string> affectedFiles = new List<string>();
        private TasksList tasksList = null;
        private Dictionary<string, VerificationTaskArgs> tasksListDictionary = new Dictionary<string, VerificationTaskArgs>();

        public OpaqueEvaluator() {
        }

        public static Function FindFunction(MemberDecl member, Function func) {
            if (member.Name == func.Name && member.tok.filename == func.tok.filename) {
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
                Change change = new Change(func.tok, func.BodyEndTok, funcString, func.WhatKind);
                DafnyVerifierClient.AddFileToChangeList(ref changeList, change);
                return new Tuple<Program, Dictionary<string, List<Change>>>(nProgram, changeList);
            }
            else {
                throw new NotImplementedException();
            }
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
                if (DafnyOptions.O.HoleEvaluatorVerboseMode)
                {
                    Console.WriteLine($"{index} output for maintain lemma:\n{response}");
                }
                Result res = DafnyVerifierClient.IsCorrectOutputForNoErrors(response);
                if (res != Result.CorrectProof)
                {
                    result[i] = DafnyVerifierClient.GetFailingFunctionResults(filePath, response);
                }
            }
            return result;
        }

        public Dictionary<int, Tuple<Program, Dictionary<string, List<Change>>>> EnvIdToChangeList =
                new Dictionary<int, Tuple<Program, Dictionary<string, List<Change>>>>();
        public Dictionary<int, Function> EnvIdToNonOpaqueFunc = new Dictionary<int, Function>();

        public void PrintResult(int envId) {
            Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: found new function to make opaque");
            Console.WriteLine($"envId={envId}\t{EnvIdToNonOpaqueFunc[envId].FullDafnyName}");
            foreach (var changeFileKV in EnvIdToChangeList[envId].Item2) {
                foreach (var change in changeFileKV.Value) {
                    Console.WriteLine($"file={changeFileKV.Key}; {change.ToJsonString()}");
                }
            }
            Console.WriteLine("");
        }

        public async Task<bool> Evaluate(Program program, Program unresolvedProgram) {
            if (DafnyOptions.O.HoleEvaluatorCommands != null) {
                var input = File.ReadAllText(DafnyOptions.O.HoleEvaluatorCommands);
                tasksList = Google.Protobuf.JsonParser.Default.Parse<TasksList>(input);
                foreach (var task in tasksList.Tasks) {
                    tasksListDictionary.Add(task.Path, task);
                }
            }
            dafnyVerifier = new DafnyVerifierClient(DafnyOptions.O.HoleEvaluatorServerIpPortList, "output_opaqueEval");
            includeParser = new IncludeParser(program);
            dafnyVerifier.InitializeBaseFoldersInRemoteServers(program, includeParser.commonPrefix);

            var opaqueFunctionFinder = new OpaqueFunctionFinder();
            int startEnvId = 0;
            int endEnvId = -1;
            foreach (var nonOpaqueFunc in opaqueFunctionFinder.GetOpaqueNonOpaquePredicates(program, false)) {
                if (DafnyOptions.O.HoleEvaluatorSpecifiedFunc != "" && nonOpaqueFunc.Name != DafnyOptions.O.HoleEvaluatorSpecifiedFunc) {
                    continue;
                }
                var newProgramChangeTuple = CreateOpaqueFunc(unresolvedProgram, nonOpaqueFunc);
                var envId = dafnyVerifier.CreateEnvironment(includeParser, newProgramChangeTuple.Item2);
                Console.WriteLine($"envId={envId}\tmaking {nonOpaqueFunc.Name} opaque");
                EnvIdToChangeList[envId] = newProgramChangeTuple;
                EnvIdToNonOpaqueFunc[envId] = nonOpaqueFunc;
                var filename = includeParser.Normalized(nonOpaqueFunc.tok.filename);
                var affectedFiles = includeParser.GetListOfAffectedFilesBy(filename).ToList();
                affectedFiles = affectedFiles.Distinct().ToList();
                foreach (var file in affectedFiles) {
                    dafnyVerifier.AddVerificationRequestToEnvironment(envId, "", file, tasksListDictionary[file].Arguments.ToList());
                }
                if (envId > endEnvId) {
                    endEnvId = envId;
                }
                // if (endEnvId == 10) {
                //     break;
                // }
            }
            await dafnyVerifier.RunVerificationRequestsStartingFromEnvironment(0);
            int newEndEnvId = endEnvId;
            int retries = 0;
            HashSet<int> correctEnvironments = new HashSet<int>();
            while (retries < 3)
            {
                retries++;
                for (int i = startEnvId; i <= endEnvId; i++)
                {
                    var res = GetFailingProofs(i);
                    if (res.Count == 0) {
                        if (!correctEnvironments.Contains(i)) {
                            PrintResult(i);
                            correctEnvironments.Add(i);
                        }
                        continue;
                    }
                    var changeList = EnvIdToChangeList[i].Item2;
                    var opaquedFunc = EnvIdToNonOpaqueFunc[i];
                    var opaquedFuncModuleName = opaquedFunc.EnclosingClass.FullDafnyName;
                    foreach (var failedProofList in res.Values)
                    {
                        bool hasCheckedImport = false;
                        foreach (var failedProof in failedProofList)
                        {
                            var sanitizedFuncName = failedProof.FuncBoogieName.Substring(failedProof.FuncBoogieName.IndexOf("$$") + 2);
                            var resolvedFailedFunc = HoleEvaluator.GetMember(program, sanitizedFuncName, true);
                            Contract.Assert(resolvedFailedFunc != null);
                            if (failedProof.Line < resolvedFailedFunc.BodyStartTok.line ||
                                (failedProof.Line == resolvedFailedFunc.BodyStartTok.line 
                                    && failedProof.Column < resolvedFailedFunc.BodyStartTok.col)) {
                                if (resolvedFailedFunc is Function) {
                                    foreach (var req in (resolvedFailedFunc as Function).Req) {
                                        var lastToken = DafnyVerifierClient.GetLastToken(req.E);
                                        if (lastToken != null && req.E.tok.line <= failedProof.Line && failedProof.Line <= lastToken.line) {
                                            Change reqChange = new Change(req.E.Resolved.tok, lastToken, $"requires (reveal_{opaquedFunc.Name}(); {Printer.ExprToString(req.E)})", "requires");
                                            DafnyVerifierClient.AddFileToChangeList(ref changeList, reqChange);
                                        }
                                    }

                                    foreach (var ens in (resolvedFailedFunc as Function).Ens) {
                                        var lastToken = DafnyVerifierClient.GetLastToken(ens.E);
                                        if (lastToken != null && ens.E.tok.line <= failedProof.Line && failedProof.Line <= lastToken.line) {
                                            Change ensChange = new Change(ens.E.Resolved.tok, lastToken, $"ensures (reveal_{opaquedFunc.Name}(); {Printer.ExprToString(ens.E)})", "ensures");
                                            DafnyVerifierClient.AddFileToChangeList(ref changeList, ensChange);
                                        }
                                    }
                                }
                                else if (resolvedFailedFunc is Lemma) {
                                    // throw new NotImplementedException();
                                }
                            }

                            if (!hasCheckedImport) {
                                hasCheckedImport = true;
                                var moduleDef = resolvedFailedFunc.EnclosingClass.EnclosingModuleDefinition;
                                var importType = DafnyVerifierClient.GetImportType(opaquedFuncModuleName, moduleDef);
                                if (importType.Item1 == DafnyVerifierClient.ImportType.NoImport) {
                                    Change openModuleChange = new Change(moduleDef.BodyStartTok, moduleDef.BodyStartTok, $"{{import opened {opaquedFuncModuleName}", "");
                                    DafnyVerifierClient.AddFileToChangeList(ref changeList, openModuleChange);
                                }
                                else if (importType.Item1 == DafnyVerifierClient.ImportType.SpecifiedImport) {
                                    Contract.Assert(importType.Item2.Exports.Count > 0);
                                    var lastExport = importType.Item2.Exports[importType.Item2.Exports.Count - 1];
                                    Change openModuleChange = new Change(importType.Item2.tok, lastExport, $"import opened {opaquedFuncModuleName}", "import");
                                    DafnyVerifierClient.AddFileToChangeList(ref changeList, openModuleChange);
                                }
                            }

                            if (resolvedFailedFunc != null && resolvedFailedFunc is Function)
                            {
                                var unresolvedFailedFunc = HoleEvaluator.GetMemberFromUnresolved(unresolvedProgram, resolvedFailedFunc.FullDafnyName) as Function;
                                var newFuncBodyStr = $"{{reveal_{opaquedFunc.Name}();\n{Printer.ExprToString(unresolvedFailedFunc.Body)}}}";
                                Change change = new Change(unresolvedFailedFunc.BodyStartTok, unresolvedFailedFunc.BodyEndTok, newFuncBodyStr, "");
                                DafnyVerifierClient.AddFileToChangeList(ref changeList, change);
                            }
                            else if (resolvedFailedFunc != null && resolvedFailedFunc is Lemma) {
                                
                                var unresolvedFailedLemma = HoleEvaluator.GetMemberFromUnresolved(unresolvedProgram, resolvedFailedFunc.FullDafnyName) as Lemma;
                                if (failedProof.Line < unresolvedFailedLemma.Body.Tok.line) {
                                    var newLemmaBodyStr = $"{{reveal_{opaquedFunc.Name}();\n{Printer.StatementToString(unresolvedFailedLemma.Body)}\n}}";
                                    Change change = new Change(unresolvedFailedLemma.Body.Tok, unresolvedFailedLemma.Body.EndTok, newLemmaBodyStr, "");
                                    DafnyVerifierClient.AddFileToChangeList(ref changeList, change);
                                } else {
                                    var changingStmt = CodeModifier.GetStatement(unresolvedFailedLemma.Body, failedProof.Line, failedProof.Column);
                                    var newStmtStr = $"{{\nreveal_{opaquedFunc.Name}();\n{Printer.StatementToString(changingStmt)}\n}}";
                                    Change change = new Change(CodeModifier.GetStartingToken(changingStmt), changingStmt.EndTok, newStmtStr, "");
                                    DafnyVerifierClient.AddFileToChangeList(ref changeList, change);
                                }
                            }
                            else if (resolvedFailedFunc != null && resolvedFailedFunc is Method) {
                                var unresolvedFailedMethod = HoleEvaluator.GetMemberFromUnresolved(unresolvedProgram, resolvedFailedFunc.FullDafnyName) as Method;
                                Contract.Assert(unresolvedFailedMethod != null);
                                if (failedProof.Line < unresolvedFailedMethod.Body.Tok.line) {
                                    var newMethodBodyStr = $"{{reveal_{opaquedFunc.Name}();\n{Printer.StatementToString(unresolvedFailedMethod.Body)}\n}}";
                                    Change change = new Change(unresolvedFailedMethod.Body.Tok, unresolvedFailedMethod.Body.EndTok, newMethodBodyStr, "");
                                    DafnyVerifierClient.AddFileToChangeList(ref changeList, change);
                                } else {
                                    var changingStmt = CodeModifier.GetStatement(unresolvedFailedMethod.Body, failedProof.Line, failedProof.Column);
                                    var newStmtStr = $"{{\nreveal_{opaquedFunc.Name}();\n{Printer.StatementToString(changingStmt)}\n}}";
                                    Change change = new Change(CodeModifier.GetStartingToken(changingStmt), changingStmt.EndTok, newStmtStr, "");
                                    DafnyVerifierClient.AddFileToChangeList(ref changeList, change);
                                }
                            }
                            else {
                                throw new NotImplementedException();
                            }
                        }
                        // Change change = new Change()
                    }
                    var envId = dafnyVerifier.CreateEnvironment(includeParser, changeList);
                    EnvIdToChangeList[envId] = EnvIdToChangeList[i];
                    EnvIdToNonOpaqueFunc[envId] = opaquedFunc;
                    var TSRequest = dafnyVerifier.requestsList[i] as TwoStageRequest;
                    foreach (var failedProofList in res)
                    {
                        var fileIndex = failedProofList.Key;
                        var file = TSRequest.SecondStageRequestsList[fileIndex].Path;
                        dafnyVerifier.AddVerificationRequestToEnvironment(envId, "", file, tasksListDictionary[file].Arguments.ToList());
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
                await dafnyVerifier.RunVerificationRequestsStartingFromEnvironment(startEnvId);
            }
            for (int i = 0; i <= endEnvId; i++)
            {
                if (!correctEnvironments.Contains(i)) {
                    var res = GetFailingProofs(i);
                    if (res.Count == 0) {
                        PrintResult(i);
                        correctEnvironments.Add(i);
                    }
                }
            }
            Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: correct solutions found: {correctEnvironments.Count}");
            Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: number of environments checked: {endEnvId}");
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
            foreach (var envId in correctEnvironments) {
                var newEnvId = dafnyVerifier.CreateEnvironment(includeParser, EnvIdToChangeList[envId].Item2);
                EnvIdToChangeList[newEnvId] = EnvIdToChangeList[envId];
                EnvIdToNonOpaqueFunc[newEnvId] = EnvIdToNonOpaqueFunc[envId];
                finalEnvironments.Add(newEnvId);
                foreach (var task in tasksListDictionary) {
                    dafnyVerifier.AddVerificationRequestToEnvironment(newEnvId, "", task.Key, task.Value.Arguments.ToList());
                }
            }
            await dafnyVerifier.RunVerificationRequestsStartingFromEnvironment(noChangeEnvId);
            foreach (var envId in finalEnvironments) {
                var TSRequest = dafnyVerifier.requestsList[envId] as TwoStageRequest;
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
                Console.WriteLine($"new execution time: {envId - noChangeEnvId}\t\t {execTime}ms");
            }
            return true;
        }
    }
}
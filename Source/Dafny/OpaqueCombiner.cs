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
using System.Dynamic;
using Grpc.Core.Interceptors;

namespace Microsoft.Dafny {
    public class OpaqueCombiner {
        private DafnyVerifierClient dafnyVerifier = null;
        private IncludeParser includeParser = null;
        private List<string> affectedFiles = new List<string>();
        private TasksList tasksList = null;
        private Dictionary<string, VerificationTaskArgs> tasksListDictionary = new Dictionary<string, VerificationTaskArgs>();

        public OpaqueCombiner() {
        }

        private string GetChangeListString(int index) {
            return Google.Protobuf.JsonFormatter.Default.Format(EnvIdToChangeList[index]);
        }

        public static  List<double> ParseExecTimes(string path) {
            List<double> res = new List<double>();
            var input = File.ReadAllLines(path);
            foreach (var line in input) {
                res.Add(Double.Parse(line));
            }
            return res;
        }

        public static List<ChangeList> ParseChangeProtobuf(string path) {
            List<ChangeList> res = new List<ChangeList>();
            var input = File.ReadAllLines(path);
            foreach (var line in input) {
                var changeList = Google.Protobuf.JsonParser.Default.Parse<ChangeList>(line);
                res.Add(changeList);
            }
            return res;
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

        public Dictionary<int, ChangeList> EnvIdToChangeList = new Dictionary<int, ChangeList>();
        public Dictionary<string, ModuleDefinition> FileNameToModuleDict = new Dictionary<string, ModuleDefinition>();
        public PriorityQueue<int, UInt64> ExecutionTimeEnvIdTupleList = new PriorityQueue<int, UInt64>();

        public bool ProcessOutput(int envId) {
            var res = GetFailingProofs(envId);
            if (res.Count == 0) {
                Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: found new function to make opaque\n");
                Console.WriteLine(GetChangeListString(envId));
                return true;
            }
            return false;
        }

        public List<Change> MethodCombineChanges(string methodName, Method unresolvedMethod, List<Change> changeList) {
            List<Change> res = new List<Change>();
            List<Change> SortedChangeList = changeList.OrderByDescending(o=>o.StartTokLine).ToList();
            Method newMethod = new Cloner().CloneMethod(unresolvedMethod);
            var methodBodyStartTok = newMethod.BodyStartTok;
            Dictionary<int, List<Change>> methodSpecRevealsPerLine = new Dictionary<int, List<Change>>();
            HashSet<string> addedRevealsToMethodBody = new HashSet<string>();
            HashSet<string> addedFuelAttributes = new HashSet<string>();
            foreach (var c in SortedChangeList) {
                switch (c.ChangeType) {
                    case ChangeTypeEnum.AddOpaqueAttribute: throw new NotSupportedException();
                    case ChangeTypeEnum.AddRevealStatement:
                        if (c.StartTokLine < methodBodyStartTok.line || 
                            (c.StartTokLine == methodBodyStartTok.line && c.StartTokColumn < methodBodyStartTok.col)) {
                            if (!methodSpecRevealsPerLine.ContainsKey(c.StartTokLine)) {
                                methodSpecRevealsPerLine[c.StartTokLine] = new List<Change>();
                            }
                            methodSpecRevealsPerLine[c.StartTokLine].Add(c);
                        } else {
                            addedRevealsToMethodBody.Add(c.AddedString);
                        }
                        break;
                    case ChangeTypeEnum.AddFuelAttribute:
                        var str = c.AddedString.Substring(7);
                        str = str.Remove(str.IndexOf(','));
                        addedFuelAttributes.Add(str);
                        break;
                    case ChangeTypeEnum.AddImport:  throw new NotSupportedException();
                }
            }
            if (addedFuelAttributes.Count != 0) {
                Contract.Assert(addedRevealsToMethodBody.Count == 0);
                Contract.Assert(methodSpecRevealsPerLine.Count == 0);
                foreach (var opaquedFuncName in addedFuelAttributes) {
                    var fuelAttributeExprList = new List<Expression>();
                    fuelAttributeExprList.Add(new NameSegment(unresolvedMethod.tok, opaquedFuncName, null));
                    fuelAttributeExprList.Add(Expression.CreateIntLiteral(Token.NoToken, 1));
                    fuelAttributeExprList.Add(Expression.CreateIntLiteral(Token.NoToken, 2));
                    newMethod.Attributes = new Attributes("fuel", fuelAttributeExprList, newMethod.Attributes);
                }
                string methodString;
                using (var wr = new System.IO.StringWriter())
                {
                    var pr = new Printer(wr);
                    pr.PrintMethod(newMethod, 0, false);
                    methodString = wr.ToString();
                }
                res.Add(DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddFuelAttribute, newMethod.tok, newMethod.BodyEndTok, methodString, newMethod.WhatKind, ""));
                return res;
            }
            
            foreach (var lineChangeKV in methodSpecRevealsPerLine) {
                var combinedReveals = String.Join(' ', lineChangeKV.Value.Select(x => x.AddedString));
                var firstParenLoc = lineChangeKV.Value[0].Replacement.IndexOf('(');
                var endOfRevealLoc = lineChangeKV.Value[0].Replacement.IndexOf(';');
                var start = lineChangeKV.Value[0].Replacement.Remove(firstParenLoc);
                var end = lineChangeKV.Value[0].Replacement.Substring(endOfRevealLoc);
                var newStr = $"{start} {combinedReveals} {end}";
                res.Add(DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddRevealStatement, 
                    lineChangeKV.Value[0].StartTokLine,
                    lineChangeKV.Value[0].StartTokColumn,
                    lineChangeKV.Value[0].EndTokLine,
                    lineChangeKV.Value[0].EndTokColumn,
                    lineChangeKV.Value[0].FileName,
                    newStr,
                    lineChangeKV.Value[0].StartString, combinedReveals));
            }
            var joinedStrForMethodBodyReveals = String.Join(' ', addedRevealsToMethodBody);
            var newMethodBodyStr = $"{{{joinedStrForMethodBodyReveals}\n{Printer.StatementToString(newMethod.Body)}\n}}";
            Change change = DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddRevealStatement, newMethod.Body.Tok, newMethod.Body.EndTok, newMethodBodyStr, "", joinedStrForMethodBodyReveals);
            res.Add(change);
            return res;
        }

        public List<Change> FunctionCombineChanges(string methodName, Function unresolvedFunc, List<Change> changeList) {
            List<Change> res = new List<Change>();
            List<Change> SortedChangeList = changeList.OrderByDescending(o=>o.StartTokLine).ToList();
            var funcBodyStartTok = unresolvedFunc.BodyStartTok;
            Dictionary<int, List<Change>> funcSpecRevealsPerLine = new Dictionary<int, List<Change>>();
            List<string> addedRevealsToFuncBody = new List<string>();
            bool shouldAddOpaque = false;
            foreach (var c in SortedChangeList) {
                switch (c.ChangeType) {
                    case ChangeTypeEnum.AddOpaqueAttribute:
                        shouldAddOpaque = true;
                        if (SortedChangeList.Count > 1) {
                            throw new NotSupportedException();
                        }
                        break;
                    case ChangeTypeEnum.AddRevealStatement:
                        if (c.StartTokLine < funcBodyStartTok.line || 
                            (c.StartTokLine == funcBodyStartTok.line && c.StartTokColumn < funcBodyStartTok.col)) {
                            if (!funcSpecRevealsPerLine.ContainsKey(c.StartTokLine)) {
                                funcSpecRevealsPerLine[c.StartTokLine] = new List<Change>();
                            }
                            funcSpecRevealsPerLine[c.StartTokLine].Add(c);
                        } else {
                            addedRevealsToFuncBody.Add(c.AddedString);
                        }
                        break;
                    case ChangeTypeEnum.AddFuelAttribute: throw new NotSupportedException();
                    case ChangeTypeEnum.AddImport: throw new NotSupportedException();
                }
            }

            foreach (var lineChangeKV in funcSpecRevealsPerLine) {
                var combinedReveals = String.Join(' ', lineChangeKV.Value.Select(x => x.AddedString));
                var firstParenLoc = lineChangeKV.Value[0].Replacement.IndexOf('(');
                var endOfRevealLoc = lineChangeKV.Value[0].Replacement.IndexOf(';');
                var start = lineChangeKV.Value[0].Replacement.Remove(firstParenLoc);
                var end = lineChangeKV.Value[0].Replacement.Substring(endOfRevealLoc);
                var newStr = $"{start} {combinedReveals} {end}";
                res.Add(DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddRevealStatement, 
                    lineChangeKV.Value[0].StartTokLine,
                    lineChangeKV.Value[0].StartTokColumn,
                    lineChangeKV.Value[0].EndTokLine,
                    lineChangeKV.Value[0].EndTokColumn,
                    lineChangeKV.Value[0].FileName,
                    newStr,
                    lineChangeKV.Value[0].StartString, combinedReveals));
            }
            if (shouldAddOpaque) {
                unresolvedFunc.Attributes = new Attributes("opaque", new List<Expression>(), unresolvedFunc.Attributes);
                string funcString;
                using (var wr = new System.IO.StringWriter()) {
                    var pr = new Printer(wr);
                    pr.PrintFunction(unresolvedFunc, 0, false);
                    funcString = wr.ToString();
                }
                res.Add(DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddOpaqueAttribute, unresolvedFunc.tok, unresolvedFunc.BodyEndTok, funcString, unresolvedFunc.WhatKind, "{:opaque}"));
            }
            if (addedRevealsToFuncBody.Count > 0) {
                var joinedStrForFuncBodyReveals = String.Join(' ', addedRevealsToFuncBody);
                var newFuncBodyStr = $"{{{joinedStrForFuncBodyReveals}\n{Printer.ExprToString(unresolvedFunc.Body)}\n}}";
                Change change = DafnyVerifierClient.CreateChange(ChangeTypeEnum.AddRevealStatement, unresolvedFunc.BodyStartTok, unresolvedFunc.BodyEndTok, newFuncBodyStr, "", joinedStrForFuncBodyReveals);
                res.Add(change);
            }
            return res;
        }

        public List<Change> CombineChanges(string methodName, MemberDecl unresolvedMember, List<Change> changeList) {
            if (unresolvedMember is Method unresolvedMethod) {
                return MethodCombineChanges(methodName, unresolvedMethod, changeList);
            } else if (unresolvedMember is Lemma unresolvedLemma) {
                return MethodCombineChanges(methodName, unresolvedLemma, changeList);
            } else if (unresolvedMember is Function unresolvedFunction) {
                return FunctionCombineChanges(methodName, unresolvedFunction, changeList);
            } else {
                throw new NotSupportedException();
            }
        }

        public ChangeList ConvertToProtoChangeList(Dictionary<string, List<Change>> changeListPerFile) {
            var changeList = new ChangeList();
            foreach (var cPerFile in changeListPerFile) {
                foreach (var c in cPerFile.Value) {
                    changeList.Changes.Add(c);
                }
            }
            return changeList;
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

            int startEnvId = 0;
            int endEnvId = -1;

            foreach (var kvp in program.ModuleSigs) {
                if (kvp.Value.ModuleDef.tok.filename != null) {
                    var filename = includeParser.Normalized(kvp.Value.ModuleDef.tok.filename);
                    FileNameToModuleDict[filename] = kvp.Value.ModuleDef;
                }
            }

            var allChangeList = ParseChangeProtobuf(DafnyOptions.O.ChangeListPath);
            var execTimes = ParseExecTimes($"{DafnyOptions.O.ChangeListPath}_execTime.txt");
            List<Tuple<double, int>> sortedExecTimes = new List<Tuple<double, int>>();
            for (int i = 0; i < execTimes.Count; i++) {
                sortedExecTimes.Add(new Tuple<double, int>(execTimes[i], i));
            }
            sortedExecTimes.Sort();

            Dictionary<string, List<Change>> LemmaToChangeListDict = new Dictionary<string, List<Change>>();
            Dictionary<string, List<Change>> CombinedLemmaToChangeListDict = new Dictionary<string, List<Change>>();
            Dictionary<string, List<Change>> AddedImportsPerFile = new Dictionary<string, List<Change>>();

            var combiningChangeLists = new List<int>();
            for (int i = 0; i < 3; i++) {
                Console.WriteLine($"Combining envId={sortedExecTimes[i].Item2} with execTime of {sortedExecTimes[i].Item1}min");
                combiningChangeLists.Add(sortedExecTimes[i].Item2);
            }
            foreach (var changeListIndex in combiningChangeLists) {
                var cList = allChangeList[changeListIndex];
                foreach (var c in cList.Changes) {
                    if (c.ChangeType != ChangeTypeEnum.AddImport) {
                        // var unresolvedMember = HoleEvaluator.GetMemberFromUnresolved(unresolvedProgram, c.FileName, c.StartTokLine);
                        var resolvedMember = HoleEvaluator.GetMember(program, includeParser, includeParser.Normalized(c.FileName), c.StartTokLine);
                        if (!LemmaToChangeListDict.ContainsKey(resolvedMember.FullDafnyName)) {
                            LemmaToChangeListDict[resolvedMember.FullDafnyName] = new List<Change>();
                        }
                        LemmaToChangeListDict[resolvedMember.FullDafnyName].Add(c);
                        // Console.WriteLine($"{resolvedMember.FullDafnyName}\t\t{unresolvedMember.Name}");
                    }
                    else {
                        if (!AddedImportsPerFile.ContainsKey(c.FileName)) {
                            AddedImportsPerFile[c.FileName] = new List<Change>();
                        }
                        AddedImportsPerFile[c.FileName].Add(c);
                    }
                    // DafnyVerifierClient.CombineChangeWithChangeList(ref combinedChangeList, c);
                }
            }
            foreach (var memberChangeListKV in LemmaToChangeListDict) {
                CombinedLemmaToChangeListDict[memberChangeListKV.Key] = CombineChanges(memberChangeListKV.Key, HoleEvaluator.GetMemberFromUnresolved(unresolvedProgram, memberChangeListKV.Key), memberChangeListKV.Value);
            }
            var changeList = new Dictionary<string, List<Change>>();
            foreach (var fileImportsKV in AddedImportsPerFile) {
                HashSet<string> addedImports = new HashSet<string>();
                foreach (var import in fileImportsKV.Value) {
                    if (addedImports.Contains(import.AddedString) == false) {
                        addedImports.Add(import.AddedString.Substring(1));
                    }
                }
                var combinedImportStr = $"{{{String.Join(' ', addedImports)}";
                var combinedChange = new Change(fileImportsKV.Value[0]);
                combinedChange.Replacement = combinedImportStr;
                combinedChange.AddedString = combinedImportStr;
                DafnyVerifierClient.AddFileToChangeList(ref changeList, combinedChange);
            }
            foreach (var member in CombinedLemmaToChangeListDict) {
                foreach (var c in member.Value) {
                    DafnyVerifierClient.AddFileToChangeList(ref changeList, c);
                }
            }

            HashSet<int> finalEnvironments = new HashSet<int>();
            var combinedEnvId = dafnyVerifier.CreateEnvironment(includeParser, changeList);
            EnvIdToChangeList[combinedEnvId] = ConvertToProtoChangeList(changeList);
            finalEnvironments.Add(combinedEnvId);
            foreach (var task in tasksListDictionary) {
                dafnyVerifier.AddVerificationRequestToEnvironment(combinedEnvId, "", task.Key, task.Value.Arguments.ToList());
            }
            await dafnyVerifier.RunVerificationRequestsStartingFromEnvironment(0, true);
            if (DafnyOptions.O.HoleEvaluatorLogOutputs != "") {
                var outputDir = DafnyOptions.O.HoleEvaluatorLogOutputs;
                if (!Directory.Exists(outputDir))
                {
                    Directory.CreateDirectory(outputDir);
                }
            }
            foreach (var envId in finalEnvironments) {
                if (DafnyOptions.O.HoleEvaluatorLogOutputs != "") {
                    var outputDir = DafnyOptions.O.HoleEvaluatorLogOutputs;
                    File.WriteAllText($"{outputDir}/change_{envId}.txt", GetChangeListString(envId));
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
                        Console.WriteLine($"verifying {filePath} failed for envId=${envId}");
                    }
                }
                Console.WriteLine($"execution time for envId=${envId}\t\t {execTime}ms = {execTime/60000.0:0.00}min");
            }
            return true;
        }
    }
}
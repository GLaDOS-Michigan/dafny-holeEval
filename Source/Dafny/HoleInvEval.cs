using System;
using System.Text;
using System.IO;
using System.Text.Json;
using System.Collections;
using System.Collections.Generic;
using System.Collections.Concurrent;
using System.Diagnostics.Contracts;
using System.Diagnostics;
using System.Reflection;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.Boogie;
using System.Threading.Tasks;
using Grpc.Core.Interceptors;

namespace Microsoft.Dafny {
    public class HoleInvEval {

        public Cloner cloner;
        private DafnyVerifierClient dafnyVerifier = null;
        private IncludeParser includeParser = null;
        private List<string> affectedFiles = new List<string>();
        private TasksList tasksList = null;
        private Dictionary<string, VerificationTaskArgs> tasksListDictionary = new Dictionary<string, VerificationTaskArgs>();
        public Dictionary<int, ChangeList> EnvIdToChangeList = new Dictionary<int, ChangeList>();
        public Dictionary<int, FuncCallChainCalculator.FunctionCallNode> EnvIdToFuncCallChain = new Dictionary<int, FuncCallChainCalculator.FunctionCallNode>();
        public ConcurrentDictionary<int, Dictionary<int, List<DafnyVerifierClient.ProofFailResult>>> EnvIdToFailingProofs = new ConcurrentDictionary<int, Dictionary<int, List<DafnyVerifierClient.ProofFailResult>>>();
        public Dictionary<string, ModuleDefinition> FileNameToModuleDict = new Dictionary<string, ModuleDefinition>();

        public CallGraph<string> CG;
        public DNFNode rootDNFnode;
        public Dictionary<string, int> MaxWeightPerNode = new Dictionary<string, int>();
        public Dictionary<string, int> CorrectVerificationCount = new Dictionary<string, int>();
        public Dictionary<string, int> FailedVerificationCount = new Dictionary<string, int>();
        public Dictionary<string, int> TimeoutVerificationCount = new Dictionary<string, int>();

        private string baseChangeFile = "";
        private Change baseChange = null;
        private int DNFGraphCalcEnvCount = 0;
        public Dictionary<string, List<Change>> GetBaseChangeList() {
            Dictionary<string, List<Change>> res = new Dictionary<string, List<Change>>();
            if (baseChange != null) {
                res[baseChange.FileName] = new List<Change>();
                res[baseChange.FileName].Add(baseChange);
            }
            return res;
        }

        public HoleInvEval() {
        }

        public string GetNodeColor(string funcName) {
            if (CorrectVerificationCount.ContainsKey(funcName) == false) {
                return "black";
            }
            if (CorrectVerificationCount[funcName] >= 1) {
                return "#009E73";
            }
            if (FailedVerificationCount.ContainsKey(funcName) == false) {
                return "black";
            }
            if (FailedVerificationCount[funcName] > 0) {
                return "#D55E00";
            } else {
                return "#0072B2";
            }
        }

        public void IncreaseChainCorrectCount(FuncCallChainCalculator.FunctionCallNode node) {
            CorrectVerificationCount[node.Func.FullDafnyName]++;
            foreach (var callee in node.CalleeList) {
                IncreaseChainCorrectCount(callee);
            }
        }

        public void IncreaseChainFailedVerifyCount(FuncCallChainCalculator.FunctionCallNode node, int count) {
            FailedVerificationCount[node.Func.FullDafnyName] += count;
            foreach (var callee in node.CalleeList) {
                IncreaseChainFailedVerifyCount(callee, count);
            }
        }

        public void IncreaseChainTimeoutVerifyCount(FuncCallChainCalculator.FunctionCallNode node, int count) {
            TimeoutVerificationCount[node.Func.FullDafnyName] += count;
            foreach (var callee in node.CalleeList) {
                IncreaseChainTimeoutVerifyCount(callee, count);
            }
        }

        public void AddWeightForChain(FuncCallChainCalculator.FunctionCallNode node, int value) {
            if (!MaxWeightPerNode.ContainsKey(node.Func.FullDafnyName)) {
                MaxWeightPerNode[node.Func.FullDafnyName] = 0;
                TimeoutVerificationCount[node.Func.FullDafnyName] = 0;
                FailedVerificationCount[node.Func.FullDafnyName] = 0;
                CorrectVerificationCount[node.Func.FullDafnyName] = 0;
            }
            MaxWeightPerNode[node.Func.FullDafnyName] += value;
            foreach (var child in node.CalleeList) {
                AddWeightForChain(child, value);
            }
        }

        public List<string> FlattenChain(FuncCallChainCalculator.FunctionCallNode node, int indentation, string prev) {
            Func<int, string> indent = (int i) => new string(' ', indentation + i * 2);
            List<string> res = new List<string>();
            if (prev != node.Func.FullDafnyName) {
                res.Add(node.Func.FullDafnyName);
            }
            foreach (var child in node.CalleeList) {
                foreach (var s in FlattenChain(child, indentation + 2, node.Func.FullDafnyName)) {
                    if (s.Length > 0) {
                        res.Add(s);
                    }
                }
            }
            return res;
        }

        public DNFNode MarkChainAsCorrect(FuncCallChainCalculator.FunctionCallNode funcCallNode, DNFNode node, string prev) {
            var prevNode = node;
            if (prev != funcCallNode.Func.FullDafnyName) {
                prevNode = node.GetChild(funcCallNode.Func.FullDafnyName);
                prevNode.AddCorrectCase();
            }
            foreach (var child in funcCallNode.CalleeList) {
                prevNode = MarkChainAsCorrect(child, prevNode, funcCallNode.Func.FullDafnyName);
            }
            return prevNode;
        }

        public DNFNode MarkChainAsFailed(FuncCallChainCalculator.FunctionCallNode funcCallNode, DNFNode node, string prev) {
            var prevNode = node;
            if (prev != funcCallNode.Func.FullDafnyName) {
                prevNode = node.GetChild(funcCallNode.Func.FullDafnyName);
                prevNode.AddFailedCase();
            }
            foreach (var child in funcCallNode.CalleeList) {
                prevNode = MarkChainAsFailed(child, prevNode, funcCallNode.Func.FullDafnyName);
            }
            return prevNode;
        }

        public DNFNode MarkChainAsTimeout(FuncCallChainCalculator.FunctionCallNode funcCallNode, DNFNode node, string prev) {
            var prevNode = node;
            if (prev != funcCallNode.Func.FullDafnyName) {
                prevNode = node.GetChild(funcCallNode.Func.FullDafnyName);
                prevNode.AddTimeoutCase();
            }
            foreach (var child in funcCallNode.CalleeList) {
                prevNode = MarkChainAsTimeout(child, prevNode, funcCallNode.Func.FullDafnyName);
            }
            return prevNode;
        }

        public DNFNode MarkChainAsVacuous(FuncCallChainCalculator.FunctionCallNode funcCallNode, DNFNode node, string prev) {
            var prevNode = node;
            if (prev != funcCallNode.Func.FullDafnyName) {
                prevNode = node.GetChild(funcCallNode.Func.FullDafnyName);
                prevNode.AddVacuousCase();
            }
            foreach (var child in funcCallNode.CalleeList) {
                prevNode = MarkChainAsVacuous(child, prevNode, funcCallNode.Func.FullDafnyName);
            }
            return prevNode;
        }

        public DNFNode AddChainNodesToGraph(FuncCallChainCalculator.FunctionCallNode funcCallNode, ref DNFNode node, string prev) {
            DNFNode nextNode = node;
            if (prev != funcCallNode.Func.FullDafnyName) {
                nextNode = node.AddChild(funcCallNode.Func.FullDafnyName);
            }
            foreach (var child in funcCallNode.CalleeList) {
                nextNode = AddChainNodesToGraph(child, ref nextNode, funcCallNode.Func.FullDafnyName);
            }
            return nextNode;
        }

        public string ConvertCallGraphToGraphViz(CallGraph<string> graph) {
            string graphVizOutput = $"strict digraph \"call_graph\" {{\n";
            graphVizOutput += "  // The list of nodes\n";
            foreach (var v in graph.AdjacencyList) {
                graphVizOutput += $"  \"{v.Key}\" [color={GetNodeColor(v.Key)}, fontcolor={GetNodeColor(v.Key)}";
                if (CorrectVerificationCount.ContainsKey(v.Key) == true) {
                    graphVizOutput += $", tooltip=\"Correct={CorrectVerificationCount[v.Key]}&#10;Failed={FailedVerificationCount[v.Key]}&#10;Timeout={TimeoutVerificationCount[v.Key]}\"];\n";
                } else {
                    graphVizOutput += $"];\n";
                }
            }
            graphVizOutput += "\n  // The list of edges:\n";
            foreach (var vAdj in graph.AdjacencyList) {
                foreach (var edge in vAdj.Value) {
                    graphVizOutput += $"  \"{vAdj.Key}\" -> \"{edge}\";\n";
                }
            }
            graphVizOutput += "}\n";
            return graphVizOutput;
        }

        private bool IsCandidatePassPrerequisites(int index)
        {
            var TSRequest = dafnyVerifier.requestsList[index] as TwoStageRequest;
            var TSOutput = dafnyVerifier.dafnyOutput[TSRequest] as VerificationResponseList;
            if (TSOutput.ResponseList.Count < 
                    TSRequest.PrerequisiteForSecondStageRequestsList.Count + 
                    TSRequest.SecondStageRequestsList.Count)
            {
                return false;
            } else {
                return true;
            }
        }

        private Dictionary<int, List<DafnyVerifierClient.ProofFailResult>> IsPassingPartialSelfInductiveTest(int index)
        {
            Dictionary<int, List<DafnyVerifierClient.ProofFailResult>> result = 
                new Dictionary<int, List<DafnyVerifierClient.ProofFailResult>>();
            var TSRequest = dafnyVerifier.requestsList[index] as TwoStageRequest;
            var TSOutput = dafnyVerifier.dafnyOutput[TSRequest] as VerificationResponseList;
            var execTime = TSOutput.ExecutionTimeInMs;
            int timeoutVerifyCount = 0;
            int failedVerifyCount = 0;
            var combinedRequests = new List<VerificationRequest>();
            combinedRequests.AddRange(TSRequest.PrerequisiteForSecondStageRequestsList);
            combinedRequests.AddRange(TSRequest.SecondStageRequestsList);
            for (int i = 0; i < combinedRequests.Count; i++)
            {
                var request = combinedRequests[i];
                if (request.Arguments.Count == 0)
                {
                    continue;
                }
                if (i >= TSOutput.ResponseList.Count) {
                    // one of the prerequisites has failed and second stage requests are not executed
                    break;
                }
                var output = TSOutput.ResponseList[i];
                var response = output.Response.ToStringUtf8();
                var filePath = output.FileName;
                string sanitizedFuncName = "";
                if (request.Arguments[request.Arguments.Count - 1].StartsWith("/proc:*")) {
                    sanitizedFuncName = request.Arguments[request.Arguments.Count - 1].Substring(7);
                }
                if (request.ShouldPassNotFail == false) {
                    // should fail in this case
                    Result res = DafnyVerifierClient.IsCorrectOutputForValidityCheck(response);
                    if (res == Result.ProvedFalse) {
                        Console.WriteLine($"make inv false in envId={index} : {response}");
                        result[i] = DafnyVerifierClient.GetFailingFunctionResults(sanitizedFuncName, filePath, response);
                        failedVerifyCount++;
                        return result;
                    }
                } else {
                    // should pass
                    Result res = DafnyVerifierClient.IsCorrectOutputForNoErrors(response);
                    if (res != Result.CorrectProof)
                    {
                        Console.WriteLine($"incorrect proof for envId={index} : {response}");
                        result[i] = DafnyVerifierClient.GetFailingFunctionResults(sanitizedFuncName, filePath, response);
                        if (res == Result.InconclusiveProof) {
                            timeoutVerifyCount++;
                        } else {
                            failedVerifyCount++;
                        }
                    }
                }
            }
            return result;
        }

        private Dictionary<int, List<DafnyVerifierClient.ProofFailResult>> GetFailingProofs(int index)
        {
            Dictionary<int, List<DafnyVerifierClient.ProofFailResult>> result = 
                new Dictionary<int, List<DafnyVerifierClient.ProofFailResult>>();
            var TSRequest = dafnyVerifier.requestsList[index] as TwoStageRequest;
            var TSOutput = dafnyVerifier.dafnyOutput[TSRequest] as VerificationResponseList;
            var execTime = TSOutput.ExecutionTimeInMs;
            int timeoutVerifyCount = 0;
            int failedVerifyCount = 0;
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
                if (i == 0) {
                    Result res = DafnyVerifierClient.IsCorrectOutputForValidityCheck(response);
                    if (res == Result.ProvedFalse) {
                        // remove this envId from chains
                        rootDNFnode.AddVacuousCase();
                        MarkChainAsVacuous(EnvIdToFuncCallChain[index], rootDNFnode, rootDNFnode.Name);
                        return result;
                    }
                } else {
                    Result res = DafnyVerifierClient.IsCorrectOutputForNoErrors(response);
                    string sanitizedFuncName = "";
                    if (request.Arguments[request.Arguments.Count - 1].StartsWith("/proc:*")) {
                        sanitizedFuncName = request.Arguments[request.Arguments.Count - 1].Substring(7);
                    }
                    if (res != Result.CorrectProof)
                    {
                        Console.WriteLine($"incorrect proof for envId={index} : {response}");
                        result[i] = DafnyVerifierClient.GetFailingFunctionResults(sanitizedFuncName, filePath, response);
                        if (res == Result.InconclusiveProof) {
                            timeoutVerifyCount++;
                        } else {
                            failedVerifyCount++;
                        }
                    }
                }
            }
            if (failedVerifyCount == 0 && timeoutVerifyCount == 0) {
                rootDNFnode.AddCorrectCase();
                MarkChainAsCorrect(EnvIdToFuncCallChain[index], rootDNFnode, rootDNFnode.Name);
            }
            if (failedVerifyCount > 0) {
                rootDNFnode.AddFailedCase();
                MarkChainAsFailed(EnvIdToFuncCallChain[index], rootDNFnode, rootDNFnode.Name);
            }
            if (timeoutVerifyCount > 0) {
                rootDNFnode.AddTimeoutCase();
                MarkChainAsTimeout(EnvIdToFuncCallChain[index], rootDNFnode, rootDNFnode.Name);
            }
            return result;
        }

        public void CalculateNodeColors(DNFNode node) {
            if (node.FailedCount > 0) {
                DNFGraph.SetColor(node.Id, "#D55E00");
            } else if (node.TimeoutCount > 0) {
                DNFGraph.SetColor(node.Id, "blue");
            } else if (node.CorrectCount > 0) {
                DNFGraph.SetColor(node.Id, "green");
            } else if (node.VacuousCount > 0) {
                DNFGraph.SetShape(node.Id, "box");
                DNFGraph.SetColor(node.Id, "black");
            }
            DNFGraph.SetTooltip(node.Id, $"correct={node.CorrectCount}&#10;timeout={node.TimeoutCount}&#10;failed={node.FailedCount}&#10;vacuous={node.VacuousCount}");
            foreach (var child in node.Children) {
                CalculateNodeColors(child);
            }
        }

        public void RemoveVacuousNodes(DNFNode root) {
            if (root.CorrectCount == 0 && root.TimeoutCount == 0 && root.FailedCount == 0) {
                DNFGraph.EraseNode(root.Id);
                foreach (var child in root.Children) {
                    RemoveVacuousNodes(child);
                }
                root.Children.Clear();
            } else {
                foreach (var child in root.Children) {
                    RemoveVacuousNodes(child);
                }
            }
        }

        public string ConvertDNFGraphToGraphviz(DNFNode root, bool removeVacuousNodes = true) {
            if (removeVacuousNodes) {
                RemoveVacuousNodes(root);
                DNFGraph.TraverseGraphAndRemoveHangingNodes(root.Id);
            }
            CalculateNodeColors(root);
            string graphVizOutput = $"strict digraph \"DNFGraph\" {{\n";
            graphVizOutput += "  // The list of nodes\n";
            foreach (var kvp in DNFGraph.Nodes) {
                graphVizOutput += $"  \"{kvp.Key}\" [label=\"{kvp.Value}\", ";
                if (DNFGraph.NodeShape.ContainsKey(kvp.Key)) {
                    graphVizOutput += $"shape=\"{DNFGraph.NodeShape[kvp.Key]}\", ";
                }
                if (DNFGraph.NodeColor.ContainsKey(kvp.Key)) {
                    graphVizOutput += $"color=\"{DNFGraph.NodeColor[kvp.Key]}\", fontcolor=\"{DNFGraph.NodeColor[kvp.Key]}\", tooltip=\"{DNFGraph.NodeTooltip[kvp.Key]}\"";
                } else {
                    graphVizOutput += $"tooltip=\"{DNFGraph.NodeTooltip[kvp.Key]}\"";
                }
                graphVizOutput += "];\n";
            }
            graphVizOutput += "\n  // The list of edges:\n";
            foreach (var node in DNFGraph.Nodes) {
                foreach (var edge in DNFGraph.Edges[node.Key]) {
                    graphVizOutput += $"  \"{node.Key}\" -> \"{edge}\";\n";
                }
            }
            graphVizOutput += "}\n";
            return graphVizOutput;
        }

        private string GetChangeListString(int index) {
            return Google.Protobuf.JsonFormatter.Default.Format(EnvIdToChangeList[index]);
        }

        private string GetRequestString(int index) {
            var TSRequest = dafnyVerifier.requestsList[index] as TwoStageRequest;
            return TSRequest.ToString() + "\n";
        }

        private string GetResponseString(int index) {
            var TSRequest = dafnyVerifier.requestsList[index] as TwoStageRequest;
            var TSOutput = dafnyVerifier.dafnyOutput[TSRequest] as VerificationResponseList;
            var res = "";
            var combinedRequests = new List<VerificationRequest>();
            combinedRequests.AddRange(TSRequest.PrerequisiteForSecondStageRequestsList);
            combinedRequests.AddRange(TSRequest.SecondStageRequestsList);
            for (int i = 0; i < combinedRequests.Count; i++)
            {
                var request = combinedRequests[i];
                if (request.Arguments.Count == 0)
                {
                    continue;
                }
                if (i >= TSOutput.ResponseList.Count) {
                    break;
                }
                var output = TSOutput.ResponseList[i];
                var response = output.Response.ToStringUtf8();
                var filePath = output.FileName;
                res += $"{filePath} response:\n{response}\n\n";
            }
            return res;
        }

        public bool ProcessOutput(int envId) {
            if (envId >= DNFGraphCalcEnvCount) {
                var res = IsPassingPartialSelfInductiveTest(envId);
                if (!EnvIdToFailingProofs.ContainsKey(envId)) {
                    EnvIdToFailingProofs[envId] = res;
                }
                if (res.Count == 0) {
                    Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: found a correct path. envId={envId}\n");
                    Console.WriteLine(GetChangeListString(envId));
                    return true;
                }
                return false;
            } else {
                var res = GetFailingProofs(envId);
                if (!EnvIdToFailingProofs.ContainsKey(envId)) {
                    EnvIdToFailingProofs[envId] = res;
                }
                if (res.Count == 0) {
                    Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: found a correct path. envId={envId}\n");
                    Console.WriteLine(GetChangeListString(envId));
                    return true;
                }
                return false;
            }
        }

        public string ReplaceVariableInExpr(Expression expr, Function nextPredicate, Function inductiveInv) {
            var argsSubstMap = new Dictionary<IVariable, Expression>();  // maps formal arguments to actuals
            Dictionary<string, HashSet<Expression>> typeToExpressionDictForInputs = new Dictionary<string, HashSet<Expression>>();
            foreach (var formal in nextPredicate.Formals) {
                var identExpr = Expression.CreateIdentExpr(formal);
                var typeString = formal.Type.ToString();
                if (typeToExpressionDictForInputs.ContainsKey(typeString)) {
                    typeToExpressionDictForInputs[typeString].Add(identExpr);
                } else {
                    var lst = new HashSet<Expression> {
                      identExpr
                    };
                    typeToExpressionDictForInputs.Add(typeString, lst);
                }
            }
            if (typeToExpressionDictForInputs.Count == 1) {
                var typeStr = nextPredicate.Formals[0].Type.ToString();
                Contract.Assert(typeToExpressionDictForInputs[typeStr].Count == 2);
                Contract.Assert(inductiveInv.Formals.Count == 1);
                Contract.Assert(inductiveInv.Formals[0].Type.ToString() == typeStr);
                argsSubstMap.Add(nextPredicate.Formals[0], Expression.CreateIdentExpr(nextPredicate.Formals[1]));
                var substituter = new AlphaConvertingSubstituter(expr, argsSubstMap, new Dictionary<TypeParameter, Type>());
                var subtitutedNamesExpr = substituter.Substitute(expr);
                return Printer.ExprToString(subtitutedNamesExpr);
            } else {
                var typeStr = nextPredicate.Formals[1].Type.ToString();
                Contract.Assert(typeToExpressionDictForInputs[typeStr].Count == 2);
                Contract.Assert(nextPredicate.Formals.Count == 3);
                Contract.Assert(inductiveInv.Formals.Count == 2);
                Contract.Assert(inductiveInv.Formals[1].Type.ToString() == typeStr);
                argsSubstMap.Add(nextPredicate.Formals[1], Expression.CreateIdentExpr(nextPredicate.Formals[2]));
                var substituter = new AlphaConvertingSubstituter(expr, argsSubstMap, new Dictionary<TypeParameter, Type>());
                var subtitutedNamesExpr = substituter.Substitute(expr);
                return Printer.ExprToString(subtitutedNamesExpr);
            }
        }

        public string GetCandidateInductivityLemmaPrefix(Function nextFunc, Function inductiveInv, bool includeModuleInTypes) {
            string res = "lemma candidateInductivityLemma(";
            var nextParamList = HoleEvaluator.GetFunctionParamList(nextFunc, "", includeModuleInTypes);
            var invParamList = HoleEvaluator.GetFunctionParamList(inductiveInv, "", includeModuleInTypes);
            res += nextParamList.Item2;
            res += ")\n";
            res += $"\trequires {nextFunc.Name}({String.Join(", ", nextParamList.Item1)})\n";
            res += $"\trequires {inductiveInv.Name}({String.Join(", ", invParamList.Item1)})\n";
            return res;
        }

        public string GetCandidateMakeInvFalseLemma(Function nextFunc, Function inductiveInv, bool includeModuleInTypes) {
            string res = "lemma candidateMakeInvFalseLemma(";
            var nextParamList = HoleEvaluator.GetFunctionParamList(nextFunc, "", includeModuleInTypes);
            var invParamList = HoleEvaluator.GetFunctionParamList(inductiveInv, "", includeModuleInTypes);
            res += nextParamList.Item2;
            res += ")\n";
            res += $"\trequires {nextFunc.Name}({String.Join(", ", nextParamList.Item1)})\n";
            res += $"\trequires {inductiveInv.Name}({String.Join(", ", invParamList.Item1)})\n";
            res += $"\tensures false\n{{}}\n";
            return res;
        }

        public string GetCandidateAlreadyIncludedLemma(Function nextFunc, Function inductiveInv, Expression candidate, bool includeModuleInTypes) {
            string res = "lemma candidateAlreadyIncludedLemma(";
            var nextParamList = HoleEvaluator.GetFunctionParamList(nextFunc, "", includeModuleInTypes);
            var invParamList = HoleEvaluator.GetFunctionParamList(inductiveInv, "", includeModuleInTypes);
            res += nextParamList.Item2;
            res += ")\n";
            res += $"\trequires {nextFunc.Name}({String.Join(", ", nextParamList.Item1)})\n";
            res += $"\trequires {inductiveInv.Name}({String.Join(", ", invParamList.Item1)})\n";
            res += $"\tensures {Printer.ExprToString(candidate)}\n{{}}\n";
            return res;
        }

        private bool HasResultedIntoFalseInv(int envId) {
            if (EnvIdToFailingProofs.ContainsKey(envId) == false) {
                return false;
            }
            var res = EnvIdToFailingProofs[envId];
            if (res.Count == 1 && res.ContainsKey(0) && res[0].Count == 1) {
                var failedResult = res[0][0];
                if (failedResult.FuncBoogieName.EndsWith("candidateMakeInvFalseLemma")) {
                    return true;
                }
            }
            return false;
        }
        private int CreateEnvironmentForCandidate(MemberDecl baseFunc, MemberDecl indInv, ExpressionFinder.ExpressionDepth candidate) {
            Expression invNewBody = Expression.CreateAnd((indInv as Function).Body, candidate.expr);
            string invNewBodyStr = $"{{{Printer.ExprToString(invNewBody)}}}\n";
            string candidateMakeInvFalseLemmaStr = GetCandidateMakeInvFalseLemma(baseFunc as Function, indInv as Function, false);
            string candidateAlreadyIncludedLemmaStr = GetCandidateAlreadyIncludedLemma(baseFunc as Function, indInv as Function, candidate.expr, false);
            string candidateInductivityLemmaStr = GetCandidateInductivityLemmaPrefix(baseFunc as Function, indInv as Function, false);
            var candidateInvReplacedWithNewState = ReplaceVariableInExpr(candidate.expr, baseFunc as Function, indInv as Function);

            candidateInductivityLemmaStr += $"\trequires {Printer.ExprToString(candidate.expr)}\n";
            candidateInductivityLemmaStr += $"\tensures  {candidateInvReplacedWithNewState}\n{{}}";
            invNewBodyStr += candidateInductivityLemmaStr + "\n\n" + candidateMakeInvFalseLemmaStr + "\n" + candidateAlreadyIncludedLemmaStr + "\n";
            Change invChange = DafnyVerifierClient.CreateChange(
                ChangeTypeEnum.ChangeFunctionBody,
                indInv.BodyStartTok,
                indInv.BodyEndTok,
                invNewBodyStr,
                "",
                invNewBodyStr
            );
            var changeList = GetBaseChangeList();
            DafnyVerifierClient.AddFileToChangeList(ref changeList, invChange);
            var envId = dafnyVerifier.CreateEnvironment(includeParser, changeList);

            EnvIdToChangeList[envId] = OpaqueCombiner.ConvertToProtoChangeList(changeList);
            EnvIdToFuncCallChain[envId] = null;

            var filename = includeParser.Normalized(indInv.tok.filename);
            var affectedFiles = includeParser.GetListOfAffectedFilesBy(filename).ToList();
            if (baseChangeFile != "") {
                var baseChangeAffectedFiles = includeParser.GetListOfAffectedFilesBy(includeParser.Normalized(baseChangeFile));
                affectedFiles.AddRange(baseChangeAffectedFiles);
            }
            affectedFiles = affectedFiles.Distinct().ToList();

            var baseArgs = tasksListDictionary[filename].Arguments.ToList();
            
            baseArgs.Add($"/proc:*candidateMakeInvFalseLemma");
            dafnyVerifier.AddVerificationRequestToEnvironment(envId, "", filename, baseArgs, true, false, $"1m", 5);
            baseArgs.RemoveAt(baseArgs.Count - 1);

            baseArgs.Add($"/proc:*candidateAlreadyIncludedLemma");
            dafnyVerifier.AddVerificationRequestToEnvironment(envId, "", filename, baseArgs, true, true, $"1m", 5);
            baseArgs.RemoveAt(baseArgs.Count - 1);

            baseArgs.Add($"/proc:*candidateInductivityLemma");
            dafnyVerifier.AddVerificationRequestToEnvironment(envId, "", filename, baseArgs, true, true, $"1m", 5);
            baseArgs.RemoveAt(baseArgs.Count - 1);

            foreach (var file in affectedFiles) {
                OpaqueEvaluator.AddVerificationRequestPerCallable(envId, file, tasksListDictionary[file].Arguments.ToList(), dafnyVerifier, FileNameToModuleDict, 5);
            }
            return envId;
        }

        public async Task<bool> Evaluate(Program program, Program unresolvedProgram, string funcName, int depth) {
            if (DafnyOptions.O.HoleEvaluatorBaseFunctionName == "") {
                Console.WriteLine("no function specified as the root of protocol actions");
                return false;
            }
            if (DafnyOptions.O.HoleEvaluatorCommands != null) {
                var input = File.ReadAllText(DafnyOptions.O.HoleEvaluatorCommands);
                tasksList = Google.Protobuf.JsonParser.Default.Parse<TasksList>(input);
                foreach (var task in tasksList.Tasks) {
                    tasksListDictionary.Add(task.Path, task);
                }
            }

            dafnyVerifier = new DafnyVerifierClient(DafnyOptions.O.HoleEvaluatorServerIpPortList, "output_HoleInvEval", ProcessOutput);
            includeParser = new IncludeParser(program);
            dafnyVerifier.InitializeBaseFoldersInRemoteServers(program, includeParser.commonPrefix);

            foreach (var kvp in program.ModuleSigs) {
                if (kvp.Value.ModuleDef.tok.filename != null) {
                    var filename = includeParser.Normalized(kvp.Value.ModuleDef.tok.filename);
                    FileNameToModuleDict[filename] = kvp.Value.ModuleDef;
                }
            }

            var member = HoleEvaluator.GetMember(program, DafnyOptions.O.HoleEvaluatorBaseFunctionName);
            var unresolvedMember = HoleEvaluator.GetMemberFromUnresolved(unresolvedProgram, DafnyOptions.O.HoleEvaluatorBaseFunctionName);

            CG = DNFCalculator.GetCallGraph(member as Function);
            Console.WriteLine(ConvertCallGraphToGraphViz(CG));
            var DNFform = DNFCalculator.GetDisjunctiveNormalForm(member);
            
            HashSet<int> envIdList = new HashSet<int>();
            rootDNFnode = new DNFNode(member.FullDafnyName);
            foreach (var exprCallChainTuple in DNFform) {
                break;
                var flattenChain = FlattenChain(exprCallChainTuple.Item2, 0, "");
                if (!flattenChain.Contains(funcName)) {
                    continue;
                }
                // Console.WriteLine(String.Join('\n', flattenChain));
                var expr = exprCallChainTuple.Item1;
                var changeList = GetBaseChangeList();
                var vacuityLemmaStr = DNFCalculator.GetVacuityLemma(member);
                // var newFuncBodyStr = $"{{\n\t({Printer.ExprToString(expr)})\n  && {Printer.ExprToString((unresolvedMember as Function).Body)}}}";
                var newFuncBodyStr = $"{{ ({Printer.ExprToString(expr)}) }}\n\n{vacuityLemmaStr}";
                Change change = DafnyVerifierClient.CreateChange(ChangeTypeEnum.ChangeFunctionBody, 
                    member.BodyStartTok, member.BodyEndTok, newFuncBodyStr, "", "");
                DafnyVerifierClient.AddFileToChangeList(ref changeList, change);
                var envId = dafnyVerifier.CreateEnvironment(includeParser, changeList);

                var exprStr = Printer.ExprToString(expr);
                Console.WriteLine($"{envId} -> {exprStr}");
                AddChainNodesToGraph(exprCallChainTuple.Item2, ref rootDNFnode, rootDNFnode.Name);
                // PrintChainNodes(exprCallChainTuple.Item2);
                // foreach (var s in FuncCallChainCalculator.GetFunctionCallNode((exprStr)) {
                //     if (HoleEvaluator.GetMember(program, s)) {}
                //     Console.WriteLine(s);
                // }
                // Console.WriteLine("---------------------------------------");
                // AddWeightForChain(exprCallChainTuple.Item2, 1);
                EnvIdToChangeList[envId] = OpaqueCombiner.ConvertToProtoChangeList(changeList);
                EnvIdToFuncCallChain[envId] = exprCallChainTuple.Item2;

                var filename = includeParser.Normalized(member.tok.filename);
                var affectedFiles = includeParser.GetListOfAffectedFilesBy(filename).ToList();
                if (baseChangeFile != "") {
                    var baseChangeAffectedFiles = includeParser.GetListOfAffectedFilesBy(includeParser.Normalized(baseChangeFile));
                    affectedFiles.AddRange(baseChangeAffectedFiles);
                }
                affectedFiles = affectedFiles.Distinct().ToList();
                
                var baseArgs = tasksListDictionary[filename].Arguments.ToList();
                baseArgs.Add($"/proc:*{member.FullSanitizedName}VacuityLemma");
                dafnyVerifier.AddVerificationRequestToEnvironment(envId, "", filename, baseArgs, true, false, $"1m", 5);
                baseArgs.RemoveAt(baseArgs.Count - 1);
                
                foreach (var file in affectedFiles) {
                    OpaqueEvaluator.AddVerificationRequestPerCallable(envId, file, tasksListDictionary[file].Arguments.ToList(), dafnyVerifier, FileNameToModuleDict, 5);
                }
                // foreach (var task in tasksListDictionary) {
                //     dafnyVerifier.AddVerificationRequestToEnvironment(envId, "", task.Key, task.Value.Arguments.ToList());
                // }
                envIdList.Add(envId);
                // if (envId == 9) {
                //     break;
                // }
            }
            DNFGraphCalcEnvCount = envIdList.Count;
            Console.WriteLine(ConvertDNFGraphToGraphviz(rootDNFnode, false));
            // foreach (var envId in envIdList) {
            //     Console.WriteLine(envId);
            //     PrintChainNodes(EnvIdToFuncCallChain[envId]);
            //     Console.WriteLine("-------------------------------------------------------");
            // }
            // await dafnyVerifier.RunVerificationRequestsStartingFromEnvironment(0, true);
            // foreach (var f in CorrectVerificationCount.Keys) {
            //     Console.WriteLine($"{f}");
            //     Console.WriteLine($"\tCorrects:\t{CorrectVerificationCount[f]}");
            //     Console.WriteLine($"\tFailed:\t{FailedVerificationCount[f]}");
            //     Console.WriteLine($"\tTimeouts:\t{TimeoutVerificationCount[f]}\n");
            // }
            // for (int i = 0; i < envIdList.Count; i++) {
            //     if (EnvIdToFailingProofs[i].Count > 0) {
            //         Console.WriteLine(i);
            //     }
            // }
            var singletonCandidateInvariants = InvariantFinder.GetCandidateInvariants(program, member as Function).ToList();
            List<ExpressionFinder.ExpressionDepth> candidateInvariants = new List<ExpressionFinder.ExpressionDepth>();
            candidateInvariants.AddRange(singletonCandidateInvariants);
            
            var indInv = HoleEvaluator.GetMember(program, DafnyOptions.O.HoleEvaluatorInvariant);
            var unresolvedIndInv = HoleEvaluator.GetMemberFromUnresolved(unresolvedProgram, DafnyOptions.O.HoleEvaluatorInvariant);
            foreach (var candidate in candidateInvariants) {
                var envId = CreateEnvironmentForCandidate(member, indInv, candidate);
                envIdList.Add(envId);
                Console.WriteLine($"{envId} -> {Printer.ExprToString(candidate.expr)}");
            }
            if (DafnyOptions.O.HoleEvaluatorIncludeFunctionInvocations) {
                var arguments = ExpressionFinder.ListArguments(program, member as Function, true);
                foreach (var e in ExpressionFinder.ExtendFunctionInvocationExpressions(program, arguments)) {
                    if (Printer.ExprToString(e.expr).StartsWith($"{member.EnclosingClass.FullDafnyName}.")) {
                        Contract.Requires(e.expr is FunctionCallExpr);
                        (e.expr as FunctionCallExpr).Name = (e.expr as FunctionCallExpr).Name.Substring(member.EnclosingClass.FullDafnyName.Length + 1);
                    }
                    var envId = CreateEnvironmentForCandidate(member, indInv, e);
                    envIdList.Add(envId);
                    Console.WriteLine($"{envId} -> {Printer.ExprToString(e.expr)}");
                }
            }
            await dafnyVerifier.RunVerificationRequestsStartingFromEnvironment(0, false);
            var lastProcessedEnvId = envIdList.Count;
            if (DafnyOptions.O.HoleEvaluatorDepth > 1) {
                Contract.Assert(DafnyOptions.O.HoleEvaluatorDepth <= 2);
                for (int i = 0; i < singletonCandidateInvariants.Count; i++) {
                    if (HasResultedIntoFalseInv(i)) {
                        continue;
                    }
                    var e0 = singletonCandidateInvariants[i];
                    if (e0.depth + 2 > DafnyOptions.O.HoleEvaluatorExpressionDepth) {
                        continue;
                    }
                    for (int j = i + 1; j < singletonCandidateInvariants.Count; j++) {
                        if (HasResultedIntoFalseInv(j)) {
                           continue;
                        }
                        var e1 = singletonCandidateInvariants[j];
                        if (e0.depth + e1.depth + 1 > DafnyOptions.O.HoleEvaluatorExpressionDepth) {
                            continue;
                        }
                        {
                            var andExpr = Expression.CreateAnd(e0.expr, e1.expr);
                            var candidate = new ExpressionFinder.ExpressionDepth(andExpr, e0.depth + e1.depth + 1, false);
                            candidateInvariants.Add(candidate);
                            var envId = CreateEnvironmentForCandidate(member, indInv, candidate);
                            envIdList.Add(envId);
                            Console.WriteLine($"{envId} -> {Printer.ExprToString(candidate.expr)}");
                        }
                        {
                            var orExpr = Expression.CreateOr(e0.expr, e1.expr);
                            var candidate = new ExpressionFinder.ExpressionDepth(orExpr, e0.depth + e1.depth + 1, false);
                            candidateInvariants.Add(candidate);
                            var envId = CreateEnvironmentForCandidate(member, indInv, candidate);
                            envIdList.Add(envId);
                            Console.WriteLine($"{envId} -> {Printer.ExprToString(candidate.expr)}");
                        }
                        if (e0.isNegateOfAnotherExpression || e1.isNegateOfAnotherExpression) 
                        {
                            continue;
                        }
                        {
                            var eqExpr = Expression.CreateEq(e0.expr, e1.expr, e0.expr.Type);
                            var candidate = new ExpressionFinder.ExpressionDepth(eqExpr, e0.depth + e1.depth + 1, false);
                            candidateInvariants.Add(candidate);
                            var envId = CreateEnvironmentForCandidate(member, indInv, candidate);
                            envIdList.Add(envId);
                            Console.WriteLine($"{envId} -> {Printer.ExprToString(candidate.expr)}");
                        }
                        {
                            var neqExpr = Expression.CreateNot(e0.expr.tok, Expression.CreateEq(e0.expr, e1.expr, e0.expr.Type));
                            var candidate = new ExpressionFinder.ExpressionDepth(neqExpr, e0.depth + e1.depth + 1, true);
                            candidateInvariants.Add(candidate);
                            var envId = CreateEnvironmentForCandidate(member, indInv, candidate);
                            envIdList.Add(envId);
                            Console.WriteLine($"{envId} -> {Printer.ExprToString(candidate.expr)}");
                        }
                    }
                }
            }
            // return false;
            await dafnyVerifier.RunVerificationRequestsStartingFromEnvironment(lastProcessedEnvId, false);
            HashSet<int> correctEnvironments = new HashSet<int>();
            int passingPrerequisiteCount = 0;
            for (int i = 0; i < envIdList.Count; i++)
            {
                var failingProofs = IsPassingPartialSelfInductiveTest(i);
                if (EnvIdToFailingProofs.ContainsKey(i)) {
                    if (EnvIdToFailingProofs[i].Count == 0) {
                        Console.WriteLine($"correct solution: {i}");
                        correctEnvironments.Add(i);
                    }
                }
                if (IsCandidatePassPrerequisites(i)) {
                    passingPrerequisiteCount++;
                }
            }
            Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: correct solutions found: {correctEnvironments.Count}");
            Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: candidates passing prerequisites: {passingPrerequisiteCount}");
            Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: number of environments checked: {envIdList.Count}");
            if (DafnyOptions.O.HoleEvaluatorLogOutputs != "") {
                try {
                    var outputDir = DafnyOptions.O.HoleEvaluatorLogOutputs;
                    if (!Directory.Exists(outputDir))
                    {
                        Directory.CreateDirectory(outputDir);
                    }
                    for (int i = 0; i < envIdList.Count; i++) {
                        File.WriteAllText($"{outputDir}/change_{i}.txt", GetChangeListString(i));
                        File.WriteAllText($"{outputDir}/request_{i}.txt", GetRequestString(i));
                        File.WriteAllText($"{outputDir}/response_{i}.txt", GetResponseString(i));
                    }
                } catch (Exception e) {
                    Console.WriteLine($"Error while writing logs: {e.ToString()}");
                }
            }
            return true;
            var DNFGraphGraphviz = ConvertDNFGraphToGraphviz(rootDNFnode);
            if (DafnyOptions.O.LogDotGraph != "") {
                File.WriteAllText(DafnyOptions.O.LogDotGraph, DNFGraphGraphviz);
            }
            Console.WriteLine(DNFGraphGraphviz);

            // Console.WriteLine(ConvertCallGraphToGraphViz(CG));
            return true;
        }
    }
}
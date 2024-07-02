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
    public class ChangeListEvaluator {
        private DafnyVerifierClient dafnyVerifier = null;
        private IncludeParser includeParser = null;
        private List<string> affectedFiles = new List<string>();
        private TasksList tasksList = null;
        private Dictionary<string, VerificationTaskArgs> tasksListDictionary = new Dictionary<string, VerificationTaskArgs>();

        public ChangeListEvaluator() {
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

        public ChangeList ConvertToProtoChangeList(Dictionary<string, List<Change>> changeListPerFile) {
            var changeList = new ChangeList();
            foreach (var cPerFile in changeListPerFile) {
                foreach (var c in cPerFile.Value) {
                    changeList.Changes.Add(c);
                }
            }
            return changeList;
        }

        public Dictionary<string, List<Change>> ConvertToDictionaryChangeList(ChangeList changeList) {
            var res = new Dictionary<string, List<Change>>();
            foreach (var change in changeList.Changes) {
                if (!res.ContainsKey(change.FileName)) {
                    res[change.FileName] = new List<Change>();
                }
                res[change.FileName].Add(change);
            }
            return res;
        }

        public async Task<bool> Evaluate(Program program, Program unresolvedProgram) {
            if (DafnyOptions.O.HoleEvaluatorCommands != null) {
                var input = File.ReadAllText(DafnyOptions.O.HoleEvaluatorCommands);
                tasksList = Google.Protobuf.JsonParser.Default.Parse<TasksList>(input);
                foreach (var task in tasksList.Tasks) {
                    tasksListDictionary.Add(task.Path, task);
                }
            }
            dafnyVerifier = new DafnyVerifierClient(DafnyOptions.O.HoleEvaluatorServerIpPortList, "output_changeListEval", ProcessOutput);
            includeParser = new IncludeParser(program);
            dafnyVerifier.InitializeBaseFoldersInRemoteServers(program, includeParser.commonPrefix);

            int startEnvId = 0;
            int endEnvId = -1;

            var changeListProto = OpaqueCombiner.ParseChangeProtobuf(DafnyOptions.O.ChangeListPath);
            var allChangeList = new List<Dictionary<string, List<Change>>>();
            allChangeList.Add(new Dictionary<string, List<Change>>());
            foreach (var changeList in changeListProto) {
                allChangeList.Add(ConvertToDictionaryChangeList(changeList));
            }
            HashSet<int> finalEnvironments = new HashSet<int>();
            foreach (var changeList in allChangeList) {
                var envId = dafnyVerifier.CreateEnvironment(includeParser, changeList);
                if (envId == 0) {
                    EnvIdToChangeList[envId] = new ChangeList();
                }
                else {
                    EnvIdToChangeList[envId] = changeListProto[envId - 1];
                }
                finalEnvironments.Add(envId);
                foreach (var task in tasksListDictionary) {
                    dafnyVerifier.AddVerificationRequestToEnvironment(envId, "", task.Key, task.Value.Arguments.ToList(), false, true);
                }
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
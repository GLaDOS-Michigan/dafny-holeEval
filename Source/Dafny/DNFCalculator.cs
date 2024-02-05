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
using Grpc.Core.Interceptors;

namespace Microsoft.Dafny {
    public class DNFCalculator {

        public Cloner cloner;
        private DafnyVerifierClient dafnyVerifier = null;
        private IncludeParser includeParser = null;
        private List<string> affectedFiles = new List<string>();
        private TasksList tasksList = null;
        private Dictionary<string, VerificationTaskArgs> tasksListDictionary = new Dictionary<string, VerificationTaskArgs>();
        public Dictionary<int, ChangeList> EnvIdToChangeList = new Dictionary<int, ChangeList>();
        public Dictionary<string, ModuleDefinition> FileNameToModuleDict = new Dictionary<string, ModuleDefinition>();

        public DNFCalculator() {
        }

        public void AppendPrefix(string prefix, Expression expr) {
            if (prefix == "" || expr == null) {
                return;
            } else if (expr is BinaryExpr binaryExpr) {
                AppendPrefix(prefix, binaryExpr.E0);
                AppendPrefix(prefix, binaryExpr.E1);
            } else if (expr is UnaryOpExpr unaryOpExpr) {
                AppendPrefix(prefix, unaryOpExpr.E);
            } else if (expr is NestedMatchExpr nestedMatchExpr) {
                AppendPrefix(prefix, nestedMatchExpr.Resolved);
            } else if (expr is NameSegment nameSegment) {
                if (!Printer.ExprToString(nameSegment).Contains('.')) {
                    nameSegment.Prefix = prefix;
                }
            } else if (expr is IdentifierExpr identifierExpr) {
                identifierExpr.Prefix = prefix;
            } else if (expr is LiteralExpr) {
                return;
            } else if (expr is ExprDotName exprDotName) {
                AppendPrefix(prefix, exprDotName.Lhs);
            } else if (expr is SeqSelectExpr seqSelectExpr) {
                AppendPrefix(prefix, seqSelectExpr.Seq);
                AppendPrefix(prefix, seqSelectExpr.E0);
                AppendPrefix(prefix, seqSelectExpr.E1);
            } else if (expr is SeqDisplayExpr seqDisplayExpr) {
                foreach (var e in seqDisplayExpr.Elements) {
                    AppendPrefix(prefix, e);
                }
            } else if (expr is SetDisplayExpr setDisplayExpr) {
                foreach (var e in setDisplayExpr.Elements) {
                    AppendPrefix(prefix, e);
                }
            } else if (expr is MultiSetDisplayExpr multiSetDisplayExpr) {
                foreach (var e in multiSetDisplayExpr.Elements) {
                    AppendPrefix(prefix, e);
                }
            } else if (expr is MapDisplayExpr mapDisplayExpr) {
                foreach (var e in mapDisplayExpr.Elements) {
                    AppendPrefix(prefix, e.A);
                    AppendPrefix(prefix, e.B);
                }
            } else if (expr is ApplySuffix applySuffix) {
                foreach (var binding in applySuffix.Bindings.ArgumentBindings) {
                    AppendPrefix(prefix, binding.Actual);
                }
            } else if (expr is ParensExpression parensExpression) {
                AppendPrefix(prefix, parensExpression.E);
            } else if (expr is ITEExpr iteExpr) {
                AppendPrefix(prefix, iteExpr.Test);
                AppendPrefix(prefix, iteExpr.Thn);
                AppendPrefix(prefix, iteExpr.Els);
            } else if (expr is ComprehensionExpr comprehensionExpr) {
                foreach (var bVar in comprehensionExpr.BoundVars) {
                    if (!bVar.Name.StartsWith(prefix)) {
                        bVar.Name = prefix + bVar.Name;
                    }
                }
                AppendPrefix(prefix, comprehensionExpr.Term);
                AppendPrefix(prefix, comprehensionExpr.Range);
            } else if (expr is ChainingExpression chainingExpression) {
                AppendPrefix(prefix, chainingExpression.E);
            } else if (expr is SeqUpdateExpr seqUpdateExpr) {
                AppendPrefix(prefix, seqUpdateExpr.Seq);
                AppendPrefix(prefix, seqUpdateExpr.Index);
                AppendPrefix(prefix, seqUpdateExpr.Value);
            } else if (expr is LetExpr letExpr) {
                foreach (var rhs in letExpr.RHSs) {
                    AppendPrefix(prefix, rhs);
                }
                AppendPrefix(prefix, letExpr.Body);
            } else {
                throw new NotSupportedException($"do not support appending prefix to {expr.GetType()} for {Printer.ExprToString(expr)}");
                // return;
            }
        }

        public IEnumerable<Expression> GetDisjunctiveNormalForm(Expression expr, string funcNamePrefix) {
            if (expr is BinaryExpr binaryExpr) {
                if (binaryExpr.Op == BinaryExpr.Opcode.And) {
                    foreach (var e0 in GetDisjunctiveNormalForm(binaryExpr.E0, funcNamePrefix)) {
                        foreach (var e1 in GetDisjunctiveNormalForm(binaryExpr.E1, funcNamePrefix)) {
                            yield return Expression.CreateAnd(e0, e1);
                        }
                    }
                } else if (binaryExpr.Op == BinaryExpr.Opcode.Or) {
                    foreach (var e in GetDisjunctiveNormalForm(binaryExpr.E0, funcNamePrefix)) {
                        yield return e;
                    }
                    foreach (var e in GetDisjunctiveNormalForm(binaryExpr.E1, funcNamePrefix)) {
                        yield return e;
                    }
                } else {
                    // var res = cloner.CloneExpr(expr);
                    AppendPrefix(funcNamePrefix, expr);
                    yield return expr;
                }
            }
            else if (expr is NestedMatchExpr nestedMatchExpr) {
                foreach (var e in GetDisjunctiveNormalForm(nestedMatchExpr.Resolved, funcNamePrefix)) {
                    yield return e;
                }
            } else if (expr is MatchExpr matchExpr) {
                if (matchExpr.Source.Type.IsDatatype && matchExpr.Cases.Count > 1) {
                    foreach (var c in matchExpr.Cases) {
                        // if (c.Pat.Tok.val.StartsWith("_")) {
                        //     foreach (var datatypeCase in missingDatatypeCases) {
                        //         var e = new ExprDotName(nestedMatchExpr.Source.tok, nestedMatchExpr.Source, datatypeCase + "?", null);
                        //         foreach (var x in GetDisjunctiveNormalForm(c.Body)) {
                        //             yield return Expression.CreateAnd(e, x);
                        //         }
                        //     }
                        // } else {
                        var source = cloner.CloneExpr(matchExpr.Source);
                        AppendPrefix(funcNamePrefix, source);
                        var cond = new ExprDotName(matchExpr.Source.tok, source, c.Ctor.tok.val + "?", null);
                        Dictionary<string, int> caseArguments = new Dictionary<string, int>();
                        Dictionary<int, string> argumentReplacement = new Dictionary<int, string>();
                        Dictionary<int, Type> argumentReplacementType = new Dictionary<int, Type>();
                        for (int i = 0; i < c.Arguments.Count; i++) {
                            caseArguments.Add(c.Arguments[i].Name, i);
                        }
                        // Contract.Assert(c.Body is LetExpr);
                        var e = c.Body;
                        while (e is LetExpr letExpr) {
                            e = letExpr.Body;
                            for (int i = 0; i < letExpr.RHSs.Count; i++) {
                                if (letExpr.RHSs[i] is IdentifierExpr identifierExpr) {
                                    if (caseArguments.ContainsKey(identifierExpr.Name)) {
                                        argumentReplacement.Add(caseArguments[identifierExpr.Name], funcNamePrefix + letExpr.LHSs[i].Id);
                                        argumentReplacementType.Add(caseArguments[identifierExpr.Name], letExpr.LHSs[i].Expr.Type);
                                    }
                                }
                            }
                        }
                        if (argumentReplacement.Count > 0)
                        {
                            var LHSs = new List<CasePattern<BoundVar>>();
                            var actualBindings = new List<ActualBinding>();
                            for (int i = 0; i < argumentReplacement.Count; i++)
                            {
                                LHSs.Add(new CasePattern<BoundVar>(c.Arguments[i].tok, new BoundVar(c.Arguments[i].tok, argumentReplacement[i], argumentReplacementType[i])));
                                actualBindings.Add(new ActualBinding(null, new NameSegment(c.Arguments[i].tok, argumentReplacement[i], null)));
                            }
                            var applySuffix = new ApplySuffix(matchExpr.Source.tok, null, new NameSegment(c.Ctor.tok, c.Ctor.tok.val, null), actualBindings, null);
                            var RHSs = new List<Expression>();
                            RHSs.Add(new BinaryExpr(matchExpr.Source.tok, BinaryExpr.Opcode.Eq, source, applySuffix));
                            foreach (var x in GetDisjunctiveNormalForm(e, funcNamePrefix))
                            {
                                var letExpr = new LetExpr(matchExpr.Source.tok, LHSs, RHSs, x, false);
                                yield return Expression.CreateAnd(cond, letExpr);
                            }
                        }
                        else
                        {
                            foreach (var x in GetDisjunctiveNormalForm(e, funcNamePrefix))
                            {
                                yield return Expression.CreateAnd(cond, x);
                            }
                        }
                        // }
                    }
                    yield break;
                }
            }
            else if (expr is ITEExpr iteExpr) {
                var testExpr = cloner.CloneExpr(iteExpr.Test);
                AppendPrefix(funcNamePrefix, testExpr);
                testExpr.Type = iteExpr.Test.Type;
                var clonedExpr = cloner.CloneExpr(iteExpr.Test);
                AppendPrefix(funcNamePrefix, clonedExpr);
                clonedExpr.Type = iteExpr.Test.Type;
                var notTextExpr = Expression.CreateNot(iteExpr.Test.tok, clonedExpr);
                foreach (var x in GetDisjunctiveNormalForm(iteExpr.Thn, funcNamePrefix)) {
                    yield return Expression.CreateAnd(testExpr, x);
                }
                foreach (var x in GetDisjunctiveNormalForm(iteExpr.Els, funcNamePrefix)) {
                    yield return Expression.CreateAnd(notTextExpr, x);
                }
            }
            else if (expr is LetExpr letExpr) {
                foreach (var x in GetDisjunctiveNormalForm(letExpr.Body, funcNamePrefix)) {
                    List<Expression> RHSs = new List<Expression>();
                    foreach (var lhs in letExpr.LHSs) {
                        // lhs.Id = funcNamePrefix + "_" + lhs.Id;
                        if (!lhs.Var.Name.StartsWith(funcNamePrefix)) {
                            lhs.Var.Name = funcNamePrefix + lhs.Var.Name;
                        }
                        AppendPrefix(funcNamePrefix, lhs.Expr);
                    }
                    foreach (var rhs in letExpr.RHSs) {
                        // var newRHS = cloner.CloneExpr(rhs);
                        AppendPrefix(funcNamePrefix, rhs);
                        RHSs.Add(rhs);
                    }
                    yield return new LetExpr(letExpr.tok, letExpr.LHSs, RHSs, x, letExpr.Exact);
                }
            }
            else if (expr is ApplySuffix applySuffix) {
                // Console.WriteLine("hh");
                var func = (applySuffix.Lhs.Resolved as MemberSelectExpr).Member as Function;
                var LHSs = new List<CasePattern<BoundVar>>();
                var actualBindings = new List<ActualBinding>();
                var RHSs = new List<Expression>();
                for (int i = 0; i < func.Formals.Count; i++)
                {
                    LHSs.Add(new CasePattern<BoundVar>(func.Formals[i].tok, new BoundVar(func.Formals[i].tok, func.Name + "_" + func.Formals[i].Name, func.Formals[i].Type)));
                    actualBindings.Add(new ActualBinding(null, new NameSegment(func.Formals[i].tok, funcNamePrefix + func.Formals[i].Name, null)));
                    var suffixArg = cloner.CloneExpr(applySuffix.Args[i]);
                    AppendPrefix(funcNamePrefix, suffixArg);
                    RHSs.Add(suffixArg);
                }
                var DNFList = GetDisjunctiveNormalForm(func.Body, func.Name + "_").ToList();
                AppendPrefix(funcNamePrefix, expr);
                if (DNFList.Count > 1) {
                    foreach (var e in DNFList) {
                        var withFuncCallExpr = new LetExpr(applySuffix.tok, LHSs, RHSs, Expression.CreateAnd(expr, e), true);
                        yield return withFuncCallExpr;
                    } 
                } else {
                    // AppendPrefix(funcNamePrefix, expr);
                    yield return expr;
                }
            }
            else {
                AppendPrefix(funcNamePrefix, expr);
                yield return expr;
            }
            yield break;
        }

        public IEnumerable<Expression> GetDisjunctiveNormalForm(MemberDecl member) {
            if (member is Function func) {
                foreach (var expr in GetDisjunctiveNormalForm(func.Body, "")) {
                    yield return expr;
                }
                yield break;
            } else {
                throw new NotSupportedException($"do not support getting DNF from {member.GetType()}");
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
                Result res = DafnyVerifierClient.IsCorrectOutputForNoErrors(response);
                string sanitizedFuncName = "";
                if (request.Arguments[request.Arguments.Count - 1].StartsWith("/proc:*")) {
                    sanitizedFuncName = request.Arguments[request.Arguments.Count - 1].Substring(7);
                }
                if (res != Result.CorrectProof)
                {
                    Console.WriteLine($"incorrect proof for envId={index} : {response}");
                    result[i] = DafnyVerifierClient.GetFailingFunctionResults(sanitizedFuncName, filePath, response);
                }
            }
            return result;
        }

        private string GetChangeListString(int index) {
            return Google.Protobuf.JsonFormatter.Default.Format(EnvIdToChangeList[index]);
        }

        public bool ProcessOutput(int envId) {
            var res = GetFailingProofs(envId);
            if (res.Count == 0) {
                Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: found a correct path\n");
                Console.WriteLine(GetChangeListString(envId));
                return true;
            }
            return false;
        }

        public async Task<bool> Evaluate(Program program, Program unresolvedProgram) {
            if (DafnyOptions.O.HoleEvaluatorSpecifiedFunc == "") {
                Console.WriteLine("no function specified to calculate the DNF for");
                return false;
            }
            if (DafnyOptions.O.HoleEvaluatorCommands != null) {
                var input = File.ReadAllText(DafnyOptions.O.HoleEvaluatorCommands);
                tasksList = Google.Protobuf.JsonParser.Default.Parse<TasksList>(input);
                foreach (var task in tasksList.Tasks) {
                    tasksListDictionary.Add(task.Path, task);
                }
            }

            dafnyVerifier = new DafnyVerifierClient(DafnyOptions.O.HoleEvaluatorServerIpPortList, "output_DNFCalculator", ProcessOutput);
            includeParser = new IncludeParser(program);
            dafnyVerifier.InitializeBaseFoldersInRemoteServers(program, includeParser.commonPrefix);

            foreach (var kvp in program.ModuleSigs) {
                if (kvp.Value.ModuleDef.tok.filename != null) {
                    var filename = includeParser.Normalized(kvp.Value.ModuleDef.tok.filename);
                    FileNameToModuleDict[filename] = kvp.Value.ModuleDef;
                }
            }

            var member = HoleEvaluator.GetMember(program, DafnyOptions.O.HoleEvaluatorSpecifiedFunc);
            var unresolvedMember = HoleEvaluator.GetMemberFromUnresolved(unresolvedProgram, DafnyOptions.O.HoleEvaluatorSpecifiedFunc);
            var DNFform = GetDisjunctiveNormalForm(member);
            cloner = new Cloner();
            HashSet<int> envIdList = new HashSet<int>();
            foreach (var expr in DNFform) {
                var changeList = new Dictionary<string, List<Change>>();
                // var newFuncBodyStr = $"{{\n\t({Printer.ExprToString(expr)})\n  && {Printer.ExprToString((unresolvedMember as Function).Body)}}}";
                var newFuncBodyStr = $"{{ ({Printer.ExprToString(expr)}) }}";
                Change change = DafnyVerifierClient.CreateChange(ChangeTypeEnum.ChangeFunctionBody, member.BodyStartTok, member.BodyEndTok, newFuncBodyStr, "", "");
                DafnyVerifierClient.AddFileToChangeList(ref changeList, change);
                var envId = dafnyVerifier.CreateEnvironment(includeParser, changeList);
                Console.WriteLine($"{envId} -> {Printer.ExprToString(expr)}");
                EnvIdToChangeList[envId] = OpaqueCombiner.ConvertToProtoChangeList(changeList);

                var filename = includeParser.Normalized(member.tok.filename);
                var affectedFiles = includeParser.GetListOfAffectedFilesBy(filename).ToList();
                affectedFiles = affectedFiles.Distinct().ToList();
                foreach (var file in affectedFiles) {
                    OpaqueEvaluator.AddVerificationRequestPerCallable(envId, file, tasksListDictionary[file].Arguments.ToList(), dafnyVerifier, FileNameToModuleDict, 10);
                }
                // foreach (var task in tasksListDictionary) {
                //     dafnyVerifier.AddVerificationRequestToEnvironment(envId, "", task.Key, task.Value.Arguments.ToList());
                // }
                envIdList.Add(envId);
                // if (envId == 9) {
                //     break;
                // }
            }
            await dafnyVerifier.RunVerificationRequestsStartingFromEnvironment(0, true);
            return true;
        }
    }
}
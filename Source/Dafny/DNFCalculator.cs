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
using System.Text.RegularExpressions;
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
        public Dictionary<int, FuncCallChainCalculator.FunctionCallNode> EnvIdToFuncCallChain = new Dictionary<int, FuncCallChainCalculator.FunctionCallNode>();
        public Dictionary<string, ModuleDefinition> FileNameToModuleDict = new Dictionary<string, ModuleDefinition>();

        public CallGraph<string> CG;
        public DNFNode rootDNFnode;
        public Dictionary<string, int> MaxWeightPerNode = new Dictionary<string, int>();
        public Dictionary<string, int> CorrectVerificationCount = new Dictionary<string, int>();
        public Dictionary<string, int> FailedVerificationCount = new Dictionary<string, int>();
        public Dictionary<string, int> TimeoutVerificationCount = new Dictionary<string, int>();

        private string baseChangeFile = "";
        private Change baseChange = null;
        public Dictionary<string, List<Change>> GetBaseChangeList() {
            Dictionary<string, List<Change>> res = new Dictionary<string, List<Change>>();
            if (baseChange != null) {
                res[baseChange.FileName] = new List<Change>();
                res[baseChange.FileName].Add(baseChange);
            }
            return res;
        }

        public DNFCalculator() {
        }

        public static void AppendPrefix(string prefix, Statement stmt) {
            if (prefix == "" || stmt == null) {
                return;
            } else if (stmt is UpdateStmt updateStmt) {
                foreach (var lhs in updateStmt.Lhss) {
                    AppendPrefix(prefix, lhs);
                }
                foreach (var rhs in updateStmt.Rhss) {
                    if (rhs is ExprRhs exprRhs) {
                        AppendPrefix(prefix, exprRhs.Expr);
                    } else {
                        throw new NotSupportedException($"do not support AppendPrefix for {Printer.StatementToString(stmt)} with type {rhs.GetType()}");
                    }
                }
            } else {
                throw new NotSupportedException($"do not support AppendPrefix for {Printer.StatementToString(stmt)} with type {stmt.GetType()}");
            }
        }

        public static void AppendPrefix(string prefix, Expression expr) {
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
                if (nameSegment.WasResolved() && (nameSegment.Resolved is Resolver_IdentifierExpr resolver_IdentifierExpr) && resolver_IdentifierExpr.Decl.WhatKind == "module") {
                    return;
                }
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
            } else if (expr is MultiSetFormingExpr multiSetFormingExpr) {
                AppendPrefix(prefix, multiSetFormingExpr.E);
            } else if (expr is MapDisplayExpr mapDisplayExpr) {
                foreach (var e in mapDisplayExpr.Elements) {
                    AppendPrefix(prefix, e.A);
                    AppendPrefix(prefix, e.B);
                }
            } else if (expr is ApplySuffix applySuffix) {
                if (!(applySuffix.Lhs is NameSegment || applySuffix.Lhs is IdentifierExpr)) {
                    AppendPrefix(prefix, applySuffix.Lhs);
                }
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
                foreach (var cp in letExpr.LHSs) {
                    if (cp.Arguments != null) {
                        foreach (var bvar in cp.Arguments) {
                            if (!bvar.Var.Name.StartsWith(prefix)) {
                                bvar.Var.Name = prefix + bvar.Var.Name;
                            }
                        }
                    }
                    if (!cp.Var.Name.StartsWith(prefix)) {
                        cp.Var.Name = prefix + cp.Var.Name;
                    }
                }
                foreach (var rhs in letExpr.RHSs) {
                    AppendPrefix(prefix, rhs);
                }
                AppendPrefix(prefix, letExpr.Body);
            } else if (expr is DatatypeUpdateExpr datatypeUpdateExpr) {
                AppendPrefix(prefix, datatypeUpdateExpr.Root);
                foreach (var update in datatypeUpdateExpr.Updates) {
                    AppendPrefix(prefix, update.Item3);
                }
            } else if (expr is StmtExpr stmtExpr) {
                AppendPrefix(prefix, stmtExpr.S);
                AppendPrefix(prefix, stmtExpr.E);
            } else if (expr is DatatypeValue datatypeValue) {
                foreach (var arg in datatypeValue.Arguments) {
                    AppendPrefix(prefix, arg);
                }
            } else if (expr is ThisExpr) {
                return;
            } else {
                throw new NotSupportedException($"do not support appending prefix to {expr.GetType()} for {Printer.ExprToString(expr)}");
                // return;
            }
        }

        public static IEnumerable<Tuple<Expression, FuncCallChainCalculator.FunctionCallNode>>
                GetDisjunctiveNormalForm(Expression expr, string funcNamePrefix, Function func, HashSet<string> seenFunctions) {
            if (expr is BinaryExpr binaryExpr) {
                if (binaryExpr.Op == BinaryExpr.Opcode.And) {
                    foreach (var e0 in GetDisjunctiveNormalForm(binaryExpr.E0, funcNamePrefix, func, seenFunctions)) {
                        foreach (var e1 in GetDisjunctiveNormalForm(binaryExpr.E1, funcNamePrefix, func, seenFunctions)) {
                            FuncCallChainCalculator.FunctionCallNode node = new FuncCallChainCalculator.FunctionCallNode(func);
                            node.CalleeList.Add(e0.Item2);
                            node.CalleeList.Add(e1.Item2);
                            yield return new Tuple<Expression, FuncCallChainCalculator.FunctionCallNode>(Expression.CreateAnd(e0.Item1, e1.Item1), node);
                        }
                    }
                } else if (binaryExpr.Op == BinaryExpr.Opcode.Or) {
                    foreach (var e in GetDisjunctiveNormalForm(binaryExpr.E0, funcNamePrefix, func, seenFunctions)) {
                        yield return e;
                    }
                    foreach (var e in GetDisjunctiveNormalForm(binaryExpr.E1, funcNamePrefix, func, seenFunctions)) {
                        yield return e;
                    }
                // } else if (binaryExpr.Op == BinaryExpr.Opcode.Eq) {
                //     foreach (var e0 in GetDisjunctiveNormalForm(binaryExpr.E0, funcNamePrefix, func, seenFunctions)) {
                //         foreach (var e1 in GetDisjunctiveNormalForm(binaryExpr.E1, funcNamePrefix, func, seenFunctions)) {
                //             FuncCallChainCalculator.FunctionCallNode node = new FuncCallChainCalculator.FunctionCallNode(func);
                //             node.CalleeList.Add(e0.Item2);
                //             node.CalleeList.Add(e1.Item2);
                //             yield return new Tuple<Expression, FuncCallChainCalculator.FunctionCallNode>(Expression.CreateEq(e0.Item1, e1.Item1, Type.Bool), node);
                //         }
                //     }
                } else {
                    FuncCallChainCalculator.FunctionCallNode node = new FuncCallChainCalculator.FunctionCallNode(func);
                    AppendPrefix(funcNamePrefix, expr);
                    yield return new Tuple<Expression, FuncCallChainCalculator.FunctionCallNode>(expr, node);
                }
            }
            else if (expr is ParensExpression parensExpression) {
                foreach (var e in GetDisjunctiveNormalForm(parensExpression.E, funcNamePrefix, func, seenFunctions)) {
                    yield return new Tuple<Expression, FuncCallChainCalculator.FunctionCallNode>(new ParensExpression(parensExpression.tok, parensExpression.CloseParenthesisTok, e.Item1) {Type = e.Item1.Type}, e.Item2);
                }
            }
            else if (expr is NestedMatchExpr nestedMatchExpr) {
                foreach (var e in GetDisjunctiveNormalForm(nestedMatchExpr.Resolved, funcNamePrefix, func, seenFunctions)) {
                    yield return e;
                }
            } else if (expr is MatchExpr matchExpr) {
                if (matchExpr.Source.Type.IsDatatype) {
                    if (matchExpr.Cases.Count > 1) {
                        foreach (var c in matchExpr.Cases) {
                            // if (c.Pat.Tok.val.StartsWith("_")) {
                            //     foreach (var datatypeCase in missingDatatypeCases) {
                            //         var e = new ExprDotName(nestedMatchExpr.Source.tok, nestedMatchExpr.Source, datatypeCase + "?", null);
                            //         foreach (var x in GetDisjunctiveNormalForm(c.Body)) {
                            //             yield return Expression.CreateAnd(e, x);
                            //         }
                            //     }
                            // } else {
                            var source = (new Cloner()).CloneExpr(matchExpr.Source);
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
                                foreach (var x in GetDisjunctiveNormalForm(e, funcNamePrefix, func, seenFunctions))
                                {
                                    var letExpr = new LetExpr(matchExpr.Source.tok, LHSs, RHSs, x.Item1, false);
                                    yield return new Tuple<Expression, FuncCallChainCalculator.FunctionCallNode>(Expression.CreateAnd(cond, letExpr), x.Item2);
                                }
                            }
                            else
                            {
                                foreach (var x in GetDisjunctiveNormalForm(e, funcNamePrefix, func, seenFunctions))
                                {
                                    yield return new Tuple<Expression, FuncCallChainCalculator.FunctionCallNode>(Expression.CreateAnd(cond, x.Item1), x.Item2);
                                }
                            }
                        }
                        yield break;
                    }
                    else {
                        foreach (var f in GetDisjunctiveNormalForm(matchExpr.Cases[0].Body, funcNamePrefix, func, seenFunctions)) {
                            yield return f;
                        }
                    }
                }
            }
            else if (expr is ITEExpr iteExpr) {
                foreach (var testExpr in GetDisjunctiveNormalForm(iteExpr.Test, funcNamePrefix, func, seenFunctions)) {
                    foreach (var x in GetDisjunctiveNormalForm(iteExpr.Thn, funcNamePrefix, func, seenFunctions)) {
                        FuncCallChainCalculator.FunctionCallNode node = new FuncCallChainCalculator.FunctionCallNode(func);
                        node.CalleeList.Add(testExpr.Item2);
                        node.CalleeList.Add(x.Item2);
                        yield return new Tuple<Expression, FuncCallChainCalculator.FunctionCallNode>(Expression.CreateITE(testExpr.Item1, x.Item1, Expression.CreateBoolLiteral(x.Item1.tok, false)),
                        node);
                    }
                    foreach (var x in GetDisjunctiveNormalForm(iteExpr.Els, funcNamePrefix, func, seenFunctions)) {
                        FuncCallChainCalculator.FunctionCallNode node = new FuncCallChainCalculator.FunctionCallNode(func);
                        node.CalleeList.Add(testExpr.Item2);
                        node.CalleeList.Add(x.Item2);
                        yield return new Tuple<Expression, FuncCallChainCalculator.FunctionCallNode>(Expression.CreateITE(testExpr.Item1, Expression.CreateBoolLiteral(x.Item1.tok, false), x.Item1),
                        node);
                    }
                }
            }
            else if (expr is LetExpr letExpr) {
                foreach (var x in GetDisjunctiveNormalForm(letExpr.Body, funcNamePrefix, func, seenFunctions)) {
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
                    yield return new Tuple<Expression, FuncCallChainCalculator.FunctionCallNode>(
                        new LetExpr(letExpr.tok, letExpr.LHSs, RHSs, x.Item1, letExpr.Exact) {Type = x.Item1.Type},
                        x.Item2);
                }
            }
            else if (expr is ApplySuffix applySuffix) {
                // Console.WriteLine("hh");
                if (!(applySuffix.Lhs.Resolved is MemberSelectExpr)) {
                    FuncCallChainCalculator.FunctionCallNode node = new FuncCallChainCalculator.FunctionCallNode(func);
                    AppendPrefix(funcNamePrefix, expr);
                    yield return new Tuple<Expression, FuncCallChainCalculator.FunctionCallNode>(expr, node);
                    yield break;
                }
                var callee = (applySuffix.Lhs.Resolved as MemberSelectExpr).Member as Function;
                if (seenFunctions.Contains(callee.FullDafnyName)) {
                    FuncCallChainCalculator.FunctionCallNode node = new FuncCallChainCalculator.FunctionCallNode(func);
                    AppendPrefix(funcNamePrefix, expr);
                    yield return new Tuple<Expression, FuncCallChainCalculator.FunctionCallNode>(expr, node);
                    yield break;
                }
                var LHSs = new List<CasePattern<BoundVar>>();
                var actualBindings = new List<ActualBinding>();
                var RHSs = new List<Expression>();
                for (int i = 0; i < callee.Formals.Count; i++)
                {
                    LHSs.Add(new CasePattern<BoundVar>(callee.Formals[i].tok, new BoundVar(callee.Formals[i].tok, callee.Name + "_" + callee.Formals[i].Name, callee.Formals[i].Type)));
                    actualBindings.Add(new ActualBinding(null, new NameSegment(callee.Formals[i].tok, funcNamePrefix + callee.Formals[i].Name, null)));
                    var suffixArg = (new Cloner()).CloneExpr(applySuffix.Args[i]);
                    AppendPrefix(funcNamePrefix, suffixArg);
                    RHSs.Add(suffixArg);
                }
                seenFunctions.Add(callee.FullDafnyName);
                var DNFList = GetDisjunctiveNormalForm(callee.Body, callee.Name + "_", callee, seenFunctions).ToList();
                seenFunctions.Remove(callee.FullDafnyName);
                AppendPrefix(funcNamePrefix, expr);
                if (DNFList.Count > 1) {
                    foreach (var e in DNFList) {
                        FuncCallChainCalculator.FunctionCallNode node = new FuncCallChainCalculator.FunctionCallNode(func);
                        node.CalleeList.Add(e.Item2);
                        var withFuncCallExpr = new Tuple<Expression, FuncCallChainCalculator.FunctionCallNode>(
                            new LetExpr(applySuffix.tok, LHSs, RHSs, Expression.CreateAnd(expr, e.Item1), true) {Type = Type.Bool},
                            node);
                        yield return withFuncCallExpr;
                    } 
                } else {
                    FuncCallChainCalculator.FunctionCallNode node = new FuncCallChainCalculator.FunctionCallNode(func);
                    node.CalleeList.Add(DNFList[0].Item2);
                    // AppendPrefix(funcNamePrefix, expr);
                    yield return new Tuple<Expression, FuncCallChainCalculator.FunctionCallNode>(expr, node);
                }
            } 
            else if (expr is ForallExpr forallExpr) {
                foreach (var x in GetDisjunctiveNormalForm(forallExpr.Term, funcNamePrefix, func, seenFunctions)) {
                    foreach (var bvar in forallExpr.BoundVars) {
                        if (!bvar.Name.StartsWith(funcNamePrefix)) {
                            bvar.Name = funcNamePrefix + bvar.Name;
                        }
                    }
                    AppendPrefix(funcNamePrefix, forallExpr.Range);
                    yield return new Tuple<Expression, FuncCallChainCalculator.FunctionCallNode>(
                        new ForallExpr(forallExpr.tok, forallExpr.BodyEndTok, forallExpr.TypeArgs, forallExpr.BoundVars, forallExpr.Range, x.Item1, forallExpr.Attributes) {Type = Type.Bool},
                        x.Item2);
                }
            }
            else if (expr is ExistsExpr existsExpr) {
                foreach (var x in GetDisjunctiveNormalForm(existsExpr.Term, funcNamePrefix, func, seenFunctions)) {
                    foreach (var bvar in existsExpr.BoundVars) {
                        if (!bvar.Name.StartsWith(funcNamePrefix)) {
                            bvar.Name = funcNamePrefix + bvar.Name;
                        }
                    }
                    AppendPrefix(funcNamePrefix, existsExpr.Range);
                    yield return new Tuple<Expression, FuncCallChainCalculator.FunctionCallNode>(
                        new ExistsExpr(existsExpr.tok, existsExpr.BodyEndTok, existsExpr.TypeArgs, existsExpr.BoundVars, existsExpr.Range, x.Item1, existsExpr.Attributes) {Type = Type.Bool},
                        x.Item2);
                }
            }
            else {
                FuncCallChainCalculator.FunctionCallNode node = new FuncCallChainCalculator.FunctionCallNode(func);
                AppendPrefix(funcNamePrefix, expr);
                yield return new Tuple<Expression, FuncCallChainCalculator.FunctionCallNode>(expr, node);
            }
            yield break;
        }

        public static IEnumerable<Tuple<Expression, FuncCallChainCalculator.FunctionCallNode>>
                GetDisjunctiveNormalForm(MemberDecl member) {
            if (member is Function func) {
                var seenFunctions = new HashSet<string>();
                seenFunctions.Add(func.FullDafnyName);
                foreach (var expr in GetDisjunctiveNormalForm(func.Body, "", func, seenFunctions)) {
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

        public bool ProcessOutput(int envId) {
            var res = GetFailingProofs(envId);
            if (res.Count == 0) {
                Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: found a correct path. envId={envId}\n");
                Console.WriteLine(GetChangeListString(envId));
                return true;
            }
            return false;
        }

        public List<string> GetNames(string exprStr) {
            List<string> split = exprStr.Split(new Char[] { ',', '\\', ' ', '(', ')', '[', ']', ';', '.', '=', ':', '&', '<' , '>', '|', '?'},
                                 StringSplitOptions.RemoveEmptyEntries).ToList();
            return split;
        }

        public static CallGraph<string> GetCallGraph(Function func) {
            Queue<FuncCallChainCalculator.FunctionCallNode> Q = new Queue<FuncCallChainCalculator.FunctionCallNode>();
            CallGraph<string> graph = new CallGraph<string>();
            foreach (var chain in FuncCallChainCalculator.GetFunctionCallNode(func, func.Body)) {
                Q.Enqueue(chain);
            }
            while (Q.Count() != 0) {
                var front = Q.Peek();
                Q.Dequeue();
                foreach (var c in front.CalleeList) {
                    Q.Enqueue(c);
                }
                graph.AddVertex(front.Func.FullDafnyName);
                for (int i = 0; i < front.CalleeList.Count; i++) {
                    if (front.CalleeList[i].Func.FullDafnyName == front.Func.FullDafnyName) {
                        continue;
                    }
                    graph.AddVertex(front.CalleeList[i].Func.FullDafnyName);
                    graph.AddEdge(front.Func.FullDafnyName, front.CalleeList[i].Func.FullDafnyName);
                }
            }
            return graph;
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

        public void PrintChainNodes(FuncCallChainCalculator.FunctionCallNode node) {
            Console.WriteLine(node.Func.FullDafnyName);
            foreach (var child in node.CalleeList) {
                PrintChainNodes(child);
            }
        }

        public static string GetVacuityLemma(MemberDecl member) {
            var res = $"lemma {member.Name}VacuityLemma (";
            if (member is Function func) {
                var sep = "";
                var formalsNameStr = "";
                foreach (var formal in func.Formals) {
                    formalsNameStr += sep + formal.Name;
                    res += $"{sep}{formal.Name}: {formal.Type.ToString()}";
                    sep = ", ";
                }
                res += ")\n";
                foreach (var req in func.Req) {
                    res += $"\trequires {Printer.ExprToString(req.E)}\n";
                }
                res += $"\trequires {member.Name}({formalsNameStr})\n";
                res += $"\tensures false\n";
                res += $"{{}}\n";
            } else {
                throw new NotSupportedException($"do not support GetVacuityLemma for {member.GetType()}");
            }
            return res;
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

        public string ConvertDNFGraphToGraphviz(DNFNode root) {
            RemoveVacuousNodes(root);
            DNFGraph.TraverseGraphAndRemoveHangingNodes(root.Id);
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

        public async Task<bool> EvaluateAfterRemoveFileLine(
                Program program,
                Program unresolvedProgram,
                string removeFileLine,
                string removePredicateName)
        {
            var unresolvedFunc = HoleEvaluator.GetMemberFromUnresolved(unresolvedProgram, removePredicateName) as Function;
            var fileLineArray = removeFileLine.Split(':');
            baseChangeFile = fileLineArray[0];
            var line = Int32.Parse(fileLineArray[1]);
            baseChange = CodeModifier.EraseFromPredicate(unresolvedFunc as Predicate, line);
            Console.WriteLine(Google.Protobuf.JsonFormatter.Default.Format(baseChange));
            // var funcNameChangeTuple = CodeModifier.Erase(program, removeFileLine);
            // baseChange = funcNameChangeTuple.Item2;
            return await Evaluate(program, unresolvedProgram);
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
            CG = GetCallGraph(member as Function);
            Console.WriteLine(ConvertCallGraphToGraphViz(CG));
            var DNFform = GetDisjunctiveNormalForm(member);
            cloner = new Cloner();
            HashSet<int> envIdList = new HashSet<int>();
            rootDNFnode = new DNFNode(member.FullDafnyName);
            foreach (var exprCallChainTuple in DNFform) {
                var flattenChain = FlattenChain(exprCallChainTuple.Item2, 0, "");
                Console.WriteLine(String.Join('\n', flattenChain));
                var expr = exprCallChainTuple.Item1;
                var changeList = GetBaseChangeList();
                var vacuityLemmaStr = GetVacuityLemma(member);
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
            // foreach (var envId in envIdList) {
            //     Console.WriteLine(envId);
            //     PrintChainNodes(EnvIdToFuncCallChain[envId]);
            //     Console.WriteLine("-------------------------------------------------------");
            // }
            await dafnyVerifier.RunVerificationRequestsStartingFromEnvironment(0, true);
            // foreach (var f in CorrectVerificationCount.Keys) {
            //     Console.WriteLine($"{f}");
            //     Console.WriteLine($"\tCorrects:\t{CorrectVerificationCount[f]}");
            //     Console.WriteLine($"\tFailed:\t{FailedVerificationCount[f]}");
            //     Console.WriteLine($"\tTimeouts:\t{TimeoutVerificationCount[f]}\n");
            // }
            var DNFGraphGraphviz = ConvertDNFGraphToGraphviz(rootDNFnode);
            if (DafnyOptions.O.LogDotGraph != "") {
                File.WriteAllText(DafnyOptions.O.LogDotGraph, DNFGraphGraphviz);
            }
            Console.WriteLine(DNFGraphGraphviz);

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
            // Console.WriteLine(ConvertCallGraphToGraphViz(CG));
            return true;
        }
    }
}
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
    public class FuncCallChainCalculator {

        public class FunctionCallNode {
            public Function Func;
            public List<FunctionCallNode> CalleeList = new List<FunctionCallNode>();
            public FunctionCallNode(Function func) {
                this.Func = func;
            }

            override public string ToString() {
                string res = Func.Name + "\n";
                foreach (var node in CalleeList) {
                    res += "\t" + Func.Name + " -> " + node.ToString() + "\n";
                }
                return res;
            }

            // public void Normalize() {
            //     foreach (var c in CalleeList) {
            //         c.Normalize();
            //     }
            //     HashSet<string> firstSeenPerCallee = new HashSet<string>();
            //     for(int i = 0; i < CalleeList.Count; i++) {
            //         var str = CalleeList[i].ToString();
            //         if (firstSeenPerCallee.ContainsKey(str)) {
            //             CalleeList.Erase(i);
            //             i--;
            //         } else {
            //             firstSeenPerCallee.Insert(str);
            //         }
            //     }
            // }
        }

        public FuncCallChainCalculator() {
        }

        static public IEnumerable<FunctionCallNode> GetFunctionCallNode(Function func, Expression expr) {
            if (expr is BinaryExpr binaryExpr) {
                if (binaryExpr.Op == BinaryExpr.Opcode.And) {
                    foreach (var f0 in GetFunctionCallNode(func, binaryExpr.E0)) {
                        foreach (var f1 in GetFunctionCallNode(func, binaryExpr.E1)) {
                            FunctionCallNode res = new FunctionCallNode(func);
                            res.CalleeList.Add(f0);
                            res.CalleeList.Add(f1);
                            yield return res;
                        }
                    }
                } else if (binaryExpr.Op == BinaryExpr.Opcode.Or) {
                    foreach (var f in GetFunctionCallNode(func, binaryExpr.E0)) {
                        yield return f;
                    }
                    foreach (var f in GetFunctionCallNode(func, binaryExpr.E1)) {
                        yield return f;
                    }
                } else {
                    FunctionCallNode res = new FunctionCallNode(func);
                    yield return res;
                }
            }
            else if (expr is NestedMatchExpr nestedMatchExpr) {
                foreach (var e in GetFunctionCallNode(func, nestedMatchExpr.Resolved)) {
                    yield return e;
                }
            } else if (expr is MatchExpr matchExpr) {
                if (matchExpr.Source.Type.IsDatatype) {
                    foreach (var c in matchExpr.Cases) {
                        foreach (var f in GetFunctionCallNode(func, c.Body)) {
                            yield return f;
                        }
                    }
                    yield break;
                }
            }
            else if (expr is ITEExpr iteExpr) {
                foreach (var testF in GetFunctionCallNode(func, iteExpr.Test)) {
                    foreach (var thenF in GetFunctionCallNode(func, iteExpr.Thn)) {
                        FunctionCallNode res = new FunctionCallNode(func);
                        res.CalleeList.Add(testF);
                        res.CalleeList.Add(thenF);
                        yield return res;
                    }
                    foreach (var elseF in GetFunctionCallNode(func, iteExpr.Els)) {
                        FunctionCallNode res = new FunctionCallNode(func);
                        res.CalleeList.Add(testF);
                        res.CalleeList.Add(elseF);
                        yield return res;
                    }
                }
            }
            else if (expr is LetExpr letExpr) {
                foreach (var f in GetFunctionCallNode(func, letExpr.Body)) {
                    yield return f;
                }
            }
            else if (expr is ApplySuffix applySuffix) {
                var callee = (applySuffix.Lhs.Resolved as MemberSelectExpr).Member as Function;
                foreach (var f in GetFunctionCallNode(callee, callee.Body)) {
                    var res = new FunctionCallNode(func);
                    res.CalleeList.Add(f);
                    yield return res;
                }
            }
            else {
                FunctionCallNode res = new FunctionCallNode(func);
                yield return res;
            }
            yield break;
        }

    }
}
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
    public class DatatypeModel {
        public DatatypeModel() {
        }
        public async Task<bool> Evaluate(Program program, Program unresolvedProgram, string initPredName) {
            var initPred = HoleEvaluator.GetMember(program, initPredName);
            var unresolvedInitPred = HoleEvaluator.GetMemberFromUnresolved(unresolvedProgram, initPredName);
            return true;
        }
    }
}
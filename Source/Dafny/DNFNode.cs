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
    public class DNFGraph {
        public static Dictionary<int, string> Nodes = new Dictionary<int, string>();
        public static Dictionary<int, string> NodeColor = new Dictionary<int, string>();
        public static Dictionary<int, string> NodeShape = new Dictionary<int, string>();
        public static Dictionary<int, string> NodeTooltip = new Dictionary<int, string>();
        public static Dictionary<int, List<int>> Edges = new Dictionary<int, List<int>>();

        public static void AddNode(int id, string name) {
            Nodes[id] = name;
            Edges[id] = new List<int>();
        }
        public static void AddEdge(int src, int dst) {
            Edges[src].Add(dst);
        }
        public static void SetColor(int id, string color) {
            NodeColor[id] = color;
        }
        public static void SetShape(int id, string shape) {
            NodeShape[id] = shape;
        }
        public static void SetTooltip(int id, string value) {
            NodeTooltip[id] = value;
        }

        public static void EraseNode(int id) {
            Edges[id].Clear();
        }
        public static void TraverseGraphAndRemoveHangingNodes(int rootId) {
            Queue<int> Q = new Queue<int>();
            Q.Enqueue(rootId);
            var SeenNodes = new HashSet<int>();
            while(Q.Count > 0) {
                var v = Q.Dequeue();
                SeenNodes.Add(v);
                for (int i = 0; i < Edges[v].Count; i++) {
                    Q.Enqueue(Edges[v][i]);
                }
            }
            var originalNodesCount = Nodes.Count;
            for (int i = 0; i < originalNodesCount; i++) {
                if (SeenNodes.Contains(i) == false) {
                    Nodes.Remove(i);
                }
            }
        }
    }
    public class DNFNode {
        public static int uniqueId = 0;
        public string Name;
        public int Id;
        public int VacuousCount = 0;
        public int FailedCount = 0;
        public int TimeoutCount = 0;
        public int CorrectCount = 0;
        public List<DNFNode> Children = new List<DNFNode>();

        public DNFNode(string name) {
            this.Name = name;
            this.Id = uniqueId;
            DNFGraph.AddNode(Id, Name);
            uniqueId++;
        }

        public DNFNode AddChild(string childName) {
            for (int i = 0; i < Children.Count; i++) {
                if (Children[i].Name == childName) {
                    return Children[i];
                }
            }
            var newChild = new DNFNode(childName);
            Children.Add(newChild);
            DNFGraph.AddEdge(this.Id, newChild.Id);
            return Children[Children.Count - 1];
        }

        public DNFNode GetChild(string childName) {
            for (int i = 0; i < Children.Count; i++) {
                if (Children[i].Name == childName) {
                    return Children[i];
                }
            }
            throw new ArgumentException("should not happen");
        }

        public void AddVacuousCase() {
            VacuousCount++;
        }
        public void AddTimeoutCase() {
            TimeoutCount++;
        }
        public void AddFailedCase() {
            FailedCount++;
        }
        public void AddCorrectCase() {
            CorrectCount++;
        }
    }
}
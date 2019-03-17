(*<*)theory Thesis imports "TSP.Specification" begin(*>*)

text\<open>dummy citation:~@{cite fixme}\<close>

section \<open>MST Heuristic\<close>

text \<open>Since the removal of an edge transforms a TSP tour into a spanning tree, the Minimum
 Spanning Tree (MST) of a complete graph always has a summed length less than or equal to the
 optimal TSP tour.

This observation gives rise to an easy 2-approximation(to-do:explain): Generate a minimum spanning
 tree, then visit the cities along its edges. A DFS(to-do: explain *once* in the thesis) on the
 tree does this. It uses every edge twice (once on discovering an edge, and once on backtracking from
 it). Thus it generates a sequence with at most twice the cost of the optimal one.

Duplicate visits to cities can be dropped afterwards. This does not increase
the cost, as these shortcuts satisfy the triangle inequality.
\<close>

section \<open>Metrics, Input graph\<close>

text \<open>To generate a graph that satisfies the triangle inequality, we put some points into a
 space with integer coordinates and compute the pairwise distances. Special care is to be put in the
choice of the metric function: The standard euclidean distance may generated graph edges with
 irrational weights, which are difficult to represent in way that allows easy comparison.
\<close>

(*<*)end(*>*)

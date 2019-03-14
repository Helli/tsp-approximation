(*<*)theory Thesis imports "TSP_Approximation.Specification" begin(*>*)

section \<open>MST Heuristic\<close>

text \<open>The Minimum Spanning Tree of a complete graph always has a summed length less than or equal to
  the optimal TSP tour because the removal of an edge transforms a TSP tour into a spanning forest.
This observation give rise to an easy 2-approximation (to-do: explain): Generate a minimum spanning
 tree, then visit the cities along its edges. A DFS (to-do: explain *once* in the thesis) on the
 tree does this. It uses every edge twice (once on discovering an edge, and once on backtracking from
 it). Thus it generates a sequence with at most twice the cost of the optimal one.
Duplicate visits to cities can be dropped in a second stage, this does not increase
the cost, as these shortcuts satisfy the triangle inequality.
\<close>

section \<open>Metrics, Input graph\<close>

(*<*)end(*>*)

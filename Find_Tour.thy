section \<open>Finding a Path between Nodes\<close>
theory Find_Tour
imports
  CAVA_Automata.Digraph
  Specification
  DFS_Framework.DFS_Framework
begin
text \<open>
  We instantiate the DFS framework to find a path to some reachable node 
  that satisfies a given predicate. We present four variants of the algorithm:
  Finding any path, and finding path of at least length one, combined with
  searching the whole graph, and searching the graph restricted to a given set 
  of nodes. The restricted variants are efficiently implemented by 
  pre-initializing the visited set (cf. @{theory DFS_Framework.Restr_Impl}).

  The restricted variants can be used for incremental search, ignoring already 
  searched nodes in further searches. This is required, e.g., for the inner 
  search of nested DFS (Buchi automaton emptiness check).
\<close>

subsection \<open>Including empty Path\<close>
record 'v fp0_state = "'v state" +
  tour_list :: "'v list"

type_synonym 'v fp0_param = "('v, ('v,unit) fp0_state_ext) parameterization"

lemma [simp]: "s\<lparr> state.more := \<lparr> tour_list = foo \<rparr> \<rparr> = s \<lparr> tour_list := foo \<rparr>"
  by (cases s) simp

definition fp0_params :: "'v fp0_param" where
"fp0_params \<equiv> dflt_parametrization state.more
  (RETURN \<lparr> tour_list = [] \<rparr>)
  \<lparr> on_discover := \<lambda>_ n s. RETURN \<lparr>tour_list = tour_list s @ [n]\<rparr> \<rparr>"

lemmas fp0_params_simp[simp] =
  gen_parameterization.simps[mk_record_simp, OF fp0_params_def[simplified]]

locale node_and_MST_in_graph =
  complete_finite_metric_graph G +
  T: tree T
  for G::\<open>('v::metric_space,real) graph\<close>
  and T::\<open>('v,real) graph\<close> +
  fixes v\<^sub>0::\<open>'v\<close>
  assumes v_in_V: \<open>v\<^sub>0 \<in> V\<close>
  and mst: \<open>minimum_spanning_tree T G\<close>
begin

lemma n_in_TV_iff: \<open>n \<in> T.V \<longleftrightarrow> n \<in> V\<close>
  using mst[unfolded minimum_spanning_tree_def spanning_tree_def]
  by (meson subgraph_node)

lemma v_in_TV: \<open>v\<^sub>0 \<in> T.V\<close>
  using n_in_TV_iff v_in_V by blast

lemma subgraphTG: \<open>subgraph T G\<close>
  using minimum_spanning_tree_def mst spanning_tree_def by blast

lemma finiteTE: \<open>finite T.E\<close>
  using finite_E finite_subset subgraphTG subgraph_def by blast

lemma finiteTV: \<open>finite T.V\<close>
  by (metis s.finiteV subgraphTG subgraph_def)

lemma finite01: \<open>finite {(va,w,v'). (va, w, v') \<in> T.E}\<close>
  using finiteTE by force

lemma finite02: \<open>finite {(w,v'). (v, w, v') \<in> T.E}\<close>
  using finiteTE by (metis succ_def succ_finite)

lemma finite03: \<open>finite {(w,v')| w v'. (v, w, v') \<in> T.E}\<close>
  using finite02 by auto

lemma finite04: \<open>{v'. \<exists>w. (v, w, v') \<in> T.E} \<subseteq> T.V\<close>
  using T.E_validD(2) by blast

lemma finite04': \<open>{v'. \<exists>w. (v', w, v) \<in> T.E} \<subseteq> T.V\<close>
  using T.E_validD(1) by blast

lemma finite05: \<open>finite {v'. \<exists>w. (v, w, v') \<in> T.E}\<close>
  using finite04 finiteTV infinite_super by blast

lemma finite05': \<open>finite {v'. \<exists>w. (v', w, v) \<in> T.E}\<close>
  using finite04' finiteTV finite_subset by blast

definition T' where
  \<open>T' = \<lparr>g_V = V, g_E = {(v,v'). (\<exists>w.(v,w,v')\<in>T.E) \<or> (\<exists>w.(v',w,v)\<in>T.E)}, g_V0 = {v\<^sub>0}\<rparr>\<close>
sublocale dfs: DFS T' fp0_params \<comment> \<open>to-do: try without qualifier\<close>
  apply unfold_locales
  apply (auto simp: T'_def E_validD v_in_TV v_in_V)
  using T.E_validD(1) n_in_TV_iff apply blast
  using T.E_validD(2) n_in_TV_iff apply blast
  using T.E_validD(2) n_in_TV_iff apply blast
  using T.E_validD(1) n_in_TV_iff apply blast
  by (simp_all add: finite05 finite05' T.E_valid)

lemma dfsV_V[simp]: \<open>dfs.V = V\<close>
  by (simp add: T'_def)

lemma start_nodes_are_nodes[simp]: "v \<in> dfs.V0 \<Longrightarrow> v \<in> V"
  by (simp add: T'_def v_in_V)

lemma finite_dfsgraph_reachable: \<open>finite dfs.reachable\<close>
  using dfs.finite_E by (simp add: T'_def)

  lemma [simp]: 
    "tour_list (dfs.empty_state \<lparr>tour_list = e\<rparr>) = e"
    by (simp add: dfs.empty_state_def)

  lemma [simp]: 
    "tour_list (s\<lparr>state.more := state.more s'\<rparr>) = tour_list s'"
    by (cases s, cases s') auto

(* This was above the simp lemmas, but isn't it superseded anyway by the sublocale statement?
locale fp0 = param_DFS
  where G = G and param = "fp0_params"
  for G
begin
*)(*
  sublocale DFS where param = "fp0_params"
    by unfold_locales simp_all*)

end

lemma dfsI:
  assumes \<open>node_and_MST_in_graph G T v\<^sub>0\<close>
  shows \<open>DFS (node_and_MST_in_graph.T' G T v\<^sub>0) fp0_params\<close>
proof - interpret node_and_MST_in_graph G T v\<^sub>0 by fact show ?thesis by unfold_locales qed

locale fp0_invar = node_and_MST_in_graph +
  DFS_invar where G = T' and param = "fp0_params"

lemma fp0_invar_intro[intro]:
  assumes "DFS_invar (node_and_MST_in_graph.T' G T v\<^sub>0) fp0_params s"
    and "node_and_MST_in_graph G T v\<^sub>0"
  shows "fp0_invar G T v\<^sub>0 s"
  using assms
proof -
  assume "DFS_invar (node_and_MST_in_graph.T' G T v\<^sub>0) fp0_params s"
  interpret DFS_invar \<open>node_and_MST_in_graph.T' G T v\<^sub>0\<close> "fp0_params" s by fact
  assume \<open>node_and_MST_in_graph G T v\<^sub>0\<close>
  interpret tmp: node_and_MST_in_graph G T v\<^sub>0 by fact
  show ?thesis by unfold_locales
qed

lemma fp0_invar_2_DFS:
  \<open>fp0_invar G T v\<^sub>0 s \<Longrightarrow> DFS_invar (node_and_MST_in_graph.T' G T v\<^sub>0) fp0_params s\<close>
proof -
  fix s
  assume "fp0_invar G T v\<^sub>0 s"
  interpret fp0_invar G T v\<^sub>0 s by fact
  show "DFS_invar (node_and_MST_in_graph.T' G T v\<^sub>0) fp0_params s" by unfold_locales
qed

abbreviation (in valid_graph) \<open>ind' V' \<equiv> \<lparr>nodes=V', edges = E \<inter> V'\<times>UNIV\<times>V'\<rparr>\<close>

lemma (in valid_graph) valid_graph_ind': \<open>valid_graph (ind' V')\<close>
  by unfold_locales auto

lemma (in complete_finite_weighted_graph) subgraph_complete:
  \<open>V' \<subseteq> V \<Longrightarrow> complete_finite_weighted_graph (ind' V') weight\<close>
proof unfold_locales
  assume \<open>V' \<subseteq> V\<close>
  then show "finite (nodes \<lparr>nodes = V', edges = E \<inter> V' \<times> UNIV \<times> V'\<rparr>)"
    by (simp add: finite_subset)
  fix v w v'
  assume \<open>(v, w, v') \<in> edges \<lparr>nodes = V', edges = E \<inter> V' \<times> UNIV \<times> V'\<rparr>\<close>
  then show "weight v v' = w"
    using edge_unique by auto
qed (auto simp: edge_exists subsetD)

lemma (in complete_finite_metric_graph) subgraph_complete_metric:
  \<open>V' \<subseteq> V \<Longrightarrow> complete_finite_metric_graph (ind' V')\<close>
  unfolding complete_finite_metric_graph_def by (simp add: subgraph_complete)

context node_and_MST_in_graph begin

lemma i_snd_pending_sane: \<open>dfs.is_invar (\<lambda>s. snd ` (pending s) \<subseteq> V)\<close>
  by (induction rule: dfs.establish_invarI) (use dfs.E_ss in auto)
lemmas (in fp0_invar) snd_pending_sane = i_snd_pending_sane[THEN make_invar_thm, rule_format]

lemma i_stack_sane: \<open>dfs.is_invar (\<lambda>s. set (stack s) \<subseteq> V)\<close>
proof (induction rule: dfs.establish_invarI)
  case (finish s s' u)
  then show ?case
    by auto (meson in_hd_or_tl_conv subset_iff)
next
  case (discover s s' u v)
  then show ?case unfolding dfs.discover_def
    by auto (use i_snd_pending_sane in \<open>meson DFS_invar.make_invar_thm img_snd subset_iff\<close>)
qed auto
lemmas (in fp0_invar) stack_sane = i_stack_sane[THEN make_invar_thm, rule_format]

lemma i_discovered_sane: \<open>dfs.is_invar (\<lambda>s. dom (discovered s) \<subseteq> V)\<close>
proof (induction rule: dfs.establish_invarI)
  case (discover s s' u v) then interpret fp0_invar where s=s
    using node_and_MST_in_graph_axioms by blast
  show ?case using discover unfolding dfs.discover_def
    by (auto simp: T'_def) (use snd_pending_sane in blast)
qed auto
lemmas (in fp0_invar) discovered_sane = i_discovered_sane[THEN make_invar_thm, rule_format]

lemma \<open>dfs.is_invar (\<lambda>s. valid_graph.tour (ind' (dom (discovered s))) (tour_list s))\<close>
proof (induction rule: dfs.establish_invarI)
  case (discover s s' u v) then interpret fp0_invar where s=s
    using node_and_MST_in_graph_axioms by blast
  interpret s: complete_finite_metric_graph \<open>ind' (dom (discovered s))\<close>
    by (fact subgraph_complete_metric[OF discovered_sane])
  from discover have ne: "stack s \<noteq> []" by simp
  from discover have vnis: "v\<notin>set (stack s)" using stack_discovered by auto
  have discovered'[simp]: \<open>dom (discovered s') = insert v (dom (discovered s))\<close>
    using discover[unfolded dfs.discover_def] by auto
  interpret s': complete_finite_metric_graph \<open>ind' (insert v (dom (discovered s)))\<close>
    using discover snd_pending_sane discovered_sane by (auto intro!: subgraph_complete_metric)
  have tour_list': \<open>tour_list s' = tour_list s\<close>
    using discover[unfolded dfs.discover_def] by auto
  have a: \<open>on_discover fp0_params u v s' \<le> SPEC (\<lambda>r. r = \<lparr>tour_list = tour_list s' @ [v]\<rparr>)\<close>
    by simp
  then have b: \<open>on_discover fp0_params u v s' \<le>\<^sub>n SPEC (\<lambda>r. r = \<lparr>tour_list = tour_list s' @ [v]\<rparr>)\<close>
    using leof_lift by blast
  have c: \<open>on_discover fp0_params u v s' \<le> SPEC (\<lambda>r. r = \<lparr>tour_list = tour_list s @ [v]\<rparr>)\<close>
    by (simp add: tour_list')
  then have d: \<open>on_discover fp0_params u v s' \<le>\<^sub>n SPEC (\<lambda>r. r = \<lparr>tour_list = tour_list s @ [v]\<rparr>)\<close>
    using leof_lift by blast
  have \<open>s'.tour (tour_list s @ [v])\<close>
  proof (cases \<open>tour_list s\<close>)
    case (Cons p ps)
    show ?thesis
    proof (cases ps)
      case Nil
      then have s_tour: \<open>s.tour [p]\<close>
        using discover(2) Cons by argo
      then have s'V: \<open>s'.V = {p,v}\<close> \<open>insert v (dom (discovered s)) = {p, v}\<close>
        by force+
      have pv: \<open>p \<in> V\<close> \<open>v \<in> V\<close> \<open>v \<noteq> p\<close>
        using s.tour_set_V[OF s_tour] discovered_sane apply fastforce
        using discover snd_pending_sane apply fast
        by (metis Un_empty discover(6,9) discovered_eq_finished_un_stack insert_absorb insert_absorb2 insert_ident insert_not_empty s'V(2) set_empty2)
      have \<open>s'.the_path [p, v] p = [(p,dist p v,v),(v,dist v p,p)]\<close>
        oops

end

end

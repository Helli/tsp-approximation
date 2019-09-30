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
  ppath :: "'v list"

type_synonym 'v fp0_param = "('v, ('v,unit) fp0_state_ext) parameterization"

lemma [simp]: "s\<lparr> state.more := \<lparr> ppath = foo \<rparr> \<rparr> = s \<lparr> ppath := foo \<rparr>"
  by (cases s) simp

definition fp0_params :: "'v fp0_param"
where "fp0_params \<equiv> dflt_parametrization state.more
  (RETURN \<lparr> ppath = [] \<rparr>) \<lparr>
  on_discover := \<lambda>_ n s. RETURN \<lparr>ppath = ppath s @ [n]\<rparr>
  \<^cancel>\<open>,on_back_edge := \<lambda>_ _ . RETURN o state.more,\<close>
  \<^cancel>\<open>is_break := \<lambda>s. break s = []\<close> \<rparr>"

lemmas fp0_params_simp[simp] =
  gen_parameterization.simps[mk_record_simp, OF fp0_params_def[simplified]]

locale node_and_MST_in_graph =
  complete_finite_weighted_graph G weight +
  T: tree T
  for G::\<open>('v,'w::weight) graph\<close> and weight
  and T::\<open>('v,'w) graph\<close> +
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
sublocale dfs: DFS T' fp0_params
  apply standard
  apply (auto simp: T'_def E_validD v_in_TV v_in_V)
  using T.E_validD(1) n_in_TV_iff apply blast
  using T.E_validD(2) n_in_TV_iff apply blast
  using T.E_validD(2) n_in_TV_iff apply blast
  using T.E_validD(1) n_in_TV_iff apply blast
  by (simp_all add: finite05 finite05' T.E_valid)

lemma finite_dTgraph_reachable: \<open>finite dfs.reachable\<close>
  unfolding T'_def using dTgraph.finite_E by (simp add: T'_def)

lemma finite_dTgraph_V0: \<open>finite dTgraph.V0\<close>
  by (simp add: dTgraph.finite_V0 finite_dTgraph_reachable)

lemma reachable_finite: \<open>\<And>v. v \<in> dTgraph.reachable \<Longrightarrow> finite (dTgraph.E `` {v})\<close>
  by (simp add: dTgraph.fb_graphI_fr fb_graph.finitely_branching finite_dTgraph_reachable)

  lemma [simp]: 
    "ppath (empty_state \<lparr>ppath = e\<rparr>) = e"
    by (simp add: empty_state_def)

  lemma [simp]: 
    "ppath (s\<lparr>state.more := state.more s'\<rparr>) = ppath s'"
    by (cases s, cases s') auto

(* This was above the simp lemmas, but isn't it superseded anyway by the sublocale statement?
locale fp0 = param_DFS
  where G = G and param = "fp0_params"
  for G
begin
*)
  sublocale DFS where param = "fp0_params"
    by unfold_locales simp_all

end

lemma fp0I: assumes "fb_graph G" shows "fp0 G"
proof - interpret fb_graph G by fact show ?thesis by unfold_locales qed

locale fp0_invar = fp0 +
  DFS_invar where param = "fp0_params"

lemma fp0_invar_eq[simp]: 
  "DFS_invar G fp0_params = fp0_invar G"
proof (intro ext iffI)
  fix s
  assume "DFS_invar G fp0_params s"
  interpret DFS_invar G "fp0_params" s by fact
  show "fp0_invar G s" by unfold_locales
next
  fix s
  assume "fp0_invar G s"
  interpret fp0_invar G s by fact
  show "DFS_invar G fp0_params s" by unfold_locales
qed

context fp0 begin

lemma (in node_and_MST_in_graph) \<open>is_invar (\<lambda>s. tour (break s))\<close>

  lemma i_no_path_no_P_discovered:
    "is_invar (\<lambda>s. ppath s = None \<longrightarrow> dom (discovered s) \<inter> Collect P = {})"
  by (rule establish_invarI) simp_all

  lemma i_path_to_P:
    "is_invar (\<lambda>s. ppath s = Some (vs,v) \<longrightarrow> P v)"
  by (rule establish_invarI) auto
  
  lemma i_path_invar:
    "is_invar (\<lambda>s. ppath s = Some (vs,v) \<longrightarrow> 
                   (vs \<noteq> [] \<longrightarrow> hd vs \<in> V0 \<and> path E (hd vs) vs v) 
                 \<and> (vs = [] \<longrightarrow> v \<in> V0 \<and> path E v vs v)
                 \<and> (distinct (vs@[v]))
                 )"
  proof (induct rule: establish_invarI)
    case (discover s s' u v) then interpret fp0_invar where s=s 
      by simp

    from discover have ne: "stack s \<noteq> []" by simp
    from discover have vnis: "v\<notin>set (stack s)" using stack_discovered by auto

    from pendingD discover have "v \<in> succ (hd (stack s))" by simp
    with hd_succ_stack_is_path[OF ne] have "\<exists>v0\<in>V0. path E v0 (rev (stack s)) v" .
    moreover from last_stack_in_V0 ne have "last (stack s) \<in> V0" by simp
    ultimately have "path E (hd (rev (stack s)))  (rev (stack s)) v" "hd (rev (stack s)) \<in> V0"
      using hd_rev[OF ne] path_hd[where p="rev (stack s)"] ne
      by auto
    with ne discover vnis show ?case by (auto simp: stack_distinct)
  qed auto
end

context fp0_invar
begin
  lemmas no_path_no_P_discovered
    = i_no_path_no_P_discovered[THEN make_invar_thm, rule_format]

  lemmas path_to_P
    = i_path_to_P[THEN make_invar_thm, rule_format]

  lemmas path_invar
    = i_path_invar[THEN make_invar_thm, rule_format]

  lemma path_invar_nonempty:
    assumes "ppath s = Some (vs,v)"
    and "vs \<noteq> []"
    shows "hd vs \<in> V0" "path E (hd vs) vs v"
    using assms path_invar
    by auto

  lemma path_invar_empty:
    assumes "ppath s = Some (vs,v)"
    and "vs = []"
    shows "v \<in> V0" "path E v vs v"
    using assms path_invar
    by auto

  lemma fp0_correct:
    assumes "\<not>cond s"
    shows "case ppath s of 
      None \<Rightarrow> \<not>(\<exists>v0\<in>V0. \<exists>v. (v0,v) \<in> E\<^sup>* \<and> P v)
    | Some (p,v) \<Rightarrow> (\<exists>v0\<in>V0. path E v0 p v \<and> P v \<and> distinct (p@[v]))" 
  proof (cases "ppath s")
    case None with assms nc_discovered_eq_reachable no_path_no_P_discovered have
      "reachable \<inter> Collect P = {}" by auto
    thus ?thesis by (auto simp add: None)
  next
    case (Some vvs) then obtain v vs where [simp]: "vvs = (vs,v)" 
      by (cases vvs) auto

    from Some path_invar[of vs v] path_to_P[of _ v] show ?thesis
      by auto
  qed

end

context fp0 begin
  lemma fp0_correct: "it_dfs \<le> SPEC (\<lambda>s. case ppath s of 
      None \<Rightarrow> \<not>(\<exists>v0\<in>V0. \<exists>v. (v0,v) \<in> E\<^sup>* \<and> P v)
    | Some (p,v) \<Rightarrow> (\<exists>v0\<in>V0. path E v0 p v \<and> P v \<and> distinct (p@[v])))" 
    apply (rule weaken_SPEC[OF it_dfs_correct])
    apply clarsimp
    apply (simp add: fp0_invar.fp0_correct)
    done
end

subsubsection \<open>Basic Interface\<close>
text \<open>Use this interface, rather than the internal stuff above! \<close>
(* Making it a well-defined interface. This interface should be used, not
  the internal stuff. If more information about the result is needed, this 
  interface should be extended! *)

type_synonym 'v fp_result = "('v list \<times> 'v) option"
definition "find_path0_pred G P \<equiv> \<lambda>r. case r of 
    None \<Rightarrow> (g_E G)\<^sup>* `` g_V0 G \<inter> Collect P = {}
  | Some (vs,v) \<Rightarrow> P v \<and> distinct (vs@[v]) \<and> (\<exists> v0 \<in> g_V0 G. path (g_E G) v0 vs v)"

definition find_path0_spec
  :: "('v, _) graph_rec_scheme \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> 'v fp_result nres"
  \<comment> \<open>Searches a path from the root nodes to some target node that satisfies a 
      given predicate. If such a path is found, the path and the target node
      are returned\<close>
where
  "find_path0_spec G P \<equiv> do {
    ASSERT (fb_graph G);
    SPEC (find_path0_pred G P)
  }"

definition find_path0 
  :: "('v, 'more) graph_rec_scheme \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> 'v fp_result nres"
  where "find_path0 G P \<equiv> do {
  ASSERT (fp0 G);
  s \<leftarrow> fp0.it_dfs TYPE('more) G P;
  RETURN (ppath s)
}"

lemma find_path0_correct:
  shows "find_path0 G P \<le> find_path0_spec G P"
  unfolding find_path0_def find_path0_spec_def find_path0_pred_def
  apply (refine_vcg le_ASSERTI order_trans[OF fp0.fp0_correct])
  apply (erule fp0I)
  apply (auto split: option.split) []
  done

lemmas find_path0_spec_rule[refine_vcg] = 
  ASSERT_le_defI[OF find_path0_spec_def]
  ASSERT_leof_defI[OF find_path0_spec_def]

subsection \<open>Restricting the Graph\<close>
text \<open> Extended interface, propagating set of already searched nodes (restriction) \<close>
(* Invariant for restriction: The restriction is closed under E 
  and contains no P-nodes *)
definition restr_invar 
  \<comment> \<open>Invariant for a node restriction, i.e., a transition closed set of nodes 
    known to not contain a target node that satisfies a predicate.\<close>
  where
  "restr_invar E R P \<equiv> E `` R \<subseteq> R \<and> R \<inter> Collect P = {}"

lemma restr_invar_triv[simp, intro!]: "restr_invar E {} P" 
  unfolding restr_invar_def by simp

lemma restr_invar_imp_not_reachable: "restr_invar E R P \<Longrightarrow> E\<^sup>*``R \<inter> Collect P = {}"
  unfolding restr_invar_def by (simp add: Image_closed_trancl)

type_synonym 'v fpr_result = "'v set + ('v list \<times> 'v)"
definition "find_path0_restr_pred G P R \<equiv> \<lambda>r. 
    case r of 
      Inl R' \<Rightarrow> R' = R \<union> (g_E G)\<^sup>* `` g_V0 G \<and> restr_invar (g_E G) R' P
    | Inr (vs,v) \<Rightarrow> P v \<and> (\<exists> v0 \<in> g_V0 G - R. path (rel_restrict (g_E G) R) v0 vs v)"

definition find_path0_restr_spec 
  \<comment> \<open>Find a path to a target node that satisfies a predicate, not considering
      nodes from the given node restriction. If no path is found, an extended
      restriction is returned, that contains the start nodes\<close>
  where "find_path0_restr_spec G P R \<equiv> do {
    ASSERT (fb_graph G \<and> restr_invar (g_E G) R P);
    SPEC (find_path0_restr_pred G P R)}"

lemmas find_path0_restr_spec_rule[refine_vcg] = 
  ASSERT_le_defI[OF find_path0_restr_spec_def]
  ASSERT_leof_defI[OF find_path0_restr_spec_def]


definition find_path0_restr 
  :: "('v, 'more) graph_rec_scheme \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> 'v set \<Rightarrow> 'v fpr_result nres"
  where "find_path0_restr G P R \<equiv> do {
  ASSERT (fb_graph G);
  ASSERT (fp0 (graph_restrict G R));
  s \<leftarrow> fp0.it_dfs TYPE('more) (graph_restrict G R) P;
  case ppath s of
    None \<Rightarrow> do {
      ASSERT (dom (discovered s) = dom (finished s));
      RETURN (Inl (R \<union> dom (finished s)))
    }
  | Some (vs,v) \<Rightarrow> RETURN (Inr (vs,v))
}"


lemma find_path0_restr_correct:
  shows "find_path0_restr G P R \<le> find_path0_restr_spec G P R"
proof (rule le_ASSERT_defI1[OF find_path0_restr_spec_def], clarify)
  assume "fb_graph G" 
  interpret a: fb_graph G by fact
  interpret fb_graph "graph_restrict G R" by (rule a.fb_graph_restrict)

  assume I: "restr_invar (g_E G) R P"

  define reachable where "reachable = graph_defs.reachable (graph_restrict G R)"

  interpret fp0 "graph_restrict G R" by unfold_locales
  
  show ?thesis unfolding find_path0_restr_def find_path0_restr_spec_def
    apply (refine_rcg refine_vcg le_ASSERTI order_trans[OF it_dfs_correct])
    apply unfold_locales
    apply (clarsimp_all)
  proof -
    fix s
    assume "fp0_invar (graph_restrict G R) P s"
      and NC[simp]: "\<not>fp0.cond TYPE('b) (graph_restrict G R) P s"
    then interpret fp0_invar "graph_restrict G R" P s by simp

    {
      assume [simp]: "ppath s = None"

      from nc_discovered_eq_finished 
      show "dom (discovered s) = dom (finished s)" by simp

      from nc_finished_eq_reachable 
      have DFR[simp]: "dom (finished s) = reachable"
        by (simp add: reachable_def)

      from I have "g_E G `` R \<subseteq> R" unfolding restr_invar_def by auto

      have "reachable \<subseteq> (g_E G)\<^sup>* `` g_V0 G" 
        unfolding reachable_def
        by (rule Image_mono, rule rtrancl_mono) (auto simp: rel_restrict_def)

      hence "R \<union> dom (finished s) = R \<union> (g_E G)\<^sup>* `` g_V0 G"
        apply -
        apply (rule equalityI)
        apply auto []
        unfolding DFR reachable_def
        apply (auto elim: E_closed_restr_reach_cases[OF _ \<open>g_E G `` R \<subseteq> R\<close>]) []
        done
      moreover from nc_fin_closed I 
      have "g_E G `` (R \<union> dom (finished s)) \<subseteq> R \<union> dom (finished s)"
        unfolding restr_invar_def by (simp add: rel_restrict_def) blast
      moreover from no_path_no_P_discovered nc_discovered_eq_finished I
      have "(R \<union> dom (finished s)) \<inter> Collect P = {}"
        unfolding restr_invar_def by auto
      ultimately 
      show "find_path0_restr_pred G P R (Inl (R \<union> dom (finished s)))"
        unfolding restr_invar_def find_path0_restr_pred_def by auto
    }

    {
      fix v vs
      assume [simp]: "ppath s = Some (vs,v)"
      from fp0_correct 
      show "find_path0_restr_pred G P R (Inr (vs, v))"
        unfolding find_path0_restr_pred_def by auto
    }
  qed
qed

subsection \<open>Path of Minimal Length One, with Restriction\<close>
definition "find_path1_restr_pred G P R \<equiv> \<lambda>r. 
      case r of 
        Inl R' \<Rightarrow> R' = R \<union> (g_E G)\<^sup>+ `` g_V0 G \<and> restr_invar (g_E G) R' P
      | Inr (vs,v) \<Rightarrow> P v \<and> vs \<noteq> [] \<and> (\<exists> v0 \<in> g_V0 G. path (g_E G \<inter> UNIV \<times> -R) v0 vs v)"

definition find_path1_restr_spec 
  \<comment> \<open>Find a path of length at least one to a target node that satisfies P.
    Takes an initial node restriction, and returns an extended node restriction.\<close>
  where "find_path1_restr_spec G P R \<equiv> do {
    ASSERT (fb_graph G \<and> restr_invar (g_E G) R P);
    SPEC (find_path1_restr_pred G P R)}"

lemmas find_path1_restr_spec_rule[refine_vcg] = 
  ASSERT_le_defI[OF find_path1_restr_spec_def]
  ASSERT_leof_defI[OF find_path1_restr_spec_def]

definition find_path1_restr
  :: "('v, 'more) graph_rec_scheme \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> 'v set \<Rightarrow> 'v fpr_result nres"
  where "find_path1_restr G P R \<equiv> 
  FOREACHc (g_V0 G) is_Inl (\<lambda>v0 s. do {
    ASSERT (is_Inl s); \<comment> \<open>TODO: Add FOREACH-condition as precondition in autoref!\<close>
    let R = projl s;
    f0 \<leftarrow> find_path0_restr_spec (G \<lparr> g_V0 := g_E G `` {v0} \<rparr>) P R;
    case f0 of 
      Inl _ \<Rightarrow> RETURN f0
    | Inr (vs,v) \<Rightarrow> RETURN (Inr (v0#vs,v))
  }) (Inl R)"

definition "find_path1_tailrec_invar G P R0 it s \<equiv> 
  case s of
    Inl R \<Rightarrow> R = R0 \<union> (g_E G)\<^sup>+ `` (g_V0 G - it) \<and> restr_invar (g_E G) R P
  | Inr (vs, v) \<Rightarrow> P v \<and> vs \<noteq> [] \<and> (\<exists> v0 \<in> g_V0 G - it. path (g_E G \<inter> UNIV \<times> -R0) v0 vs v)"


lemma find_path1_restr_correct:
  shows "find_path1_restr G P R \<le> find_path1_restr_spec G P R"
proof (rule le_ASSERT_defI1[OF find_path1_restr_spec_def], clarify)
  assume "fb_graph G"
  interpret a: fb_graph G by fact
  interpret fb0: fb_graph "G \<lparr> g_E := g_E G \<inter> UNIV \<times> -R \<rparr>"
    by (rule a.fb_graph_subset, auto)

  assume I: "restr_invar (g_E G) R P"

  have aux2: "\<And>v0. v0 \<in> g_V0 G \<Longrightarrow> fb_graph (G \<lparr> g_V0 := g_E G `` {v0} \<rparr>)"
    by (rule a.fb_graph_subset, auto)

  {
    fix v0 it s
    assume IT: "it \<subseteq> g_V0 G" "v0 \<in> it"
    and "is_Inl s"
    and FPI: "find_path1_tailrec_invar G P R it s"
    and RI: "restr_invar (g_E G) (projl s \<union> (g_E G)\<^sup>+ `` {v0}) P"

    then obtain R' where [simp]: "s = Inl R'" by (cases s) auto

    from FPI have [simp]: "R' = R \<union> (g_E G)\<^sup>+ `` (g_V0 G - it)" 
      unfolding find_path1_tailrec_invar_def by simp

    have "find_path1_tailrec_invar G P R (it - {v0})
            (Inl (projl s \<union> (g_E G)\<^sup>+ `` {v0}))"
      using RI
      by (auto simp: find_path1_tailrec_invar_def it_step_insert_iff[OF IT])
  } note aux4 = this      

  {
    fix v0 u it s v p
    assume IT: "it \<subseteq> g_V0 G" "v0 \<in> it"
    and "is_Inl s"
    and FPI: "find_path1_tailrec_invar G P R it s"
    and PV: "P v"
    and PATH: "path (rel_restrict (g_E G) (projl s)) u p v" "(v0,u)\<in>(g_E G)"
    and PR: "u \<notin> projl s"

    then obtain R' where [simp]: "s = Inl R'" by (cases s) auto

    from FPI have [simp]: "R' = R \<union> (g_E G)\<^sup>+ `` (g_V0 G - it)" 
      unfolding find_path1_tailrec_invar_def by simp

    have "find_path1_tailrec_invar G P R (it - {v0}) (Inr (v0 # p, v))"
      apply (simp add: find_path1_tailrec_invar_def PV)
      apply (rule bexI[where x=v0])
        using PR PATH(2) path_mono[OF rel_restrict_mono2[of R] PATH(1)]
        apply (auto simp: path1_restr_conv) []

        using IT apply blast
      done
  } note aux5 = this

  show ?thesis
    unfolding find_path1_restr_def find_path1_restr_spec_def find_path1_restr_pred_def
    apply (refine_rcg le_ASSERTI
      refine_vcg FOREACHc_rule[where I="find_path1_tailrec_invar G P R"]
      (*order_trans[OF find_path0_restr_correct]*)
      )
    apply simp
    using I apply (auto simp add: find_path1_tailrec_invar_def restr_invar_def) []

    apply (blast intro: aux2)
    apply (auto simp add: find_path1_tailrec_invar_def split: sum.splits) []
    apply (auto 
      simp: find_path0_restr_pred_def aux4 aux5
      simp: trancl_Image_unfold_left[symmetric]
      split: sum.splits) []

    apply (auto simp add: find_path1_tailrec_invar_def split: sum.splits) [2]
    done
qed

definition "find_path1_pred G P \<equiv> \<lambda>r. 
      case r of 
        None \<Rightarrow> (g_E G)\<^sup>+ `` g_V0 G \<inter> Collect P = {}
      | Some (vs, v) \<Rightarrow> P v \<and> vs \<noteq> [] \<and> (\<exists> v0 \<in> g_V0 G. path (g_E G) v0 vs v)"
definition find_path1_spec 
  \<comment> \<open>Find a path of length at least one to a target node that satisfies 
      a given predicate.\<close>
  where "find_path1_spec G P \<equiv> do {
    ASSERT (fb_graph G);
    SPEC (find_path1_pred G P)}"

lemmas find_path1_spec_rule[refine_vcg] = 
  ASSERT_le_defI[OF find_path1_spec_def]
  ASSERT_leof_defI[OF find_path1_spec_def]

subsection \<open>Path of Minimal Length One, without Restriction\<close>
definition find_path1 
  :: "('v, 'more) graph_rec_scheme \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> 'v fp_result nres"
  where "find_path1 G P \<equiv> do {
  r \<leftarrow> find_path1_restr_spec G P {};
  case r of 
    Inl _ \<Rightarrow> RETURN None
  | Inr vsv \<Rightarrow> RETURN (Some vsv)
}"

lemma find_path1_correct: 
  shows "find_path1 G P \<le> find_path1_spec G P"
  unfolding find_path1_def find_path1_spec_def find_path1_pred_def
  apply (refine_rcg refine_vcg le_ASSERTI order_trans[OF find_path1_restr_correct])
  apply simp
  apply (fastforce 
    simp: find_path1_restr_spec_def find_path1_restr_pred_def
    split: sum.splits 
    dest!: restr_invar_imp_not_reachable tranclD)
  done

end

section \<open>Specification\<close>
theory Specification
  imports
    Koenigsberg_Friendship.KoenigsbergBridge
    Graph_Definition_Impl
begin

lemma sum_of_parts(*rm*): \<open>\<lparr>nodes= nodes G, edges=edges G\<rparr> = G\<close>
  by simp

lemma triple_of_parts: \<open>(fst e, fst (snd e), snd (snd e)) = e\<close>
  by auto

lemma (in linorder) finite_ranking_induct'[consumes 1, case_names empty insert]:
  \<comment> \<open>copied from \<^theory>\<open>HOL.Lattices_Big\<close> and mirrored\<close>
  fixes f :: \<open>'b \<Rightarrow> 'a\<close>
  assumes \<open>finite S\<close>
  assumes \<open>P {}\<close>
  assumes \<open>\<And>x S. finite S \<Longrightarrow> (\<And>y. y \<in> S \<Longrightarrow> f x \<le> f y) \<Longrightarrow> P S \<Longrightarrow> P (insert x S)\<close>
  shows \<open>P S\<close>
  using \<open>finite S\<close>
proof (induction rule: finite_psubset_induct)
  case (psubset A)
  {
    assume \<open>A \<noteq> {}\<close>
    hence \<open>f ` A \<noteq> {}\<close> and \<open>finite (f ` A)\<close>
      using psubset finite_image_iff by simp+
    then obtain a where \<open>f a = Min (f ` A)\<close> and \<open>a \<in> A\<close>
      by (metis Min_in[of \<open>f ` A\<close>] imageE)
    then have \<open>P (A - {a})\<close>
      using psubset member_remove by blast
    moreover
    have \<open>\<And>y. y \<in> A \<Longrightarrow> f a \<le> f y\<close>
      using \<open>f a = Min (f ` A)\<close> \<open>finite (f ` A)\<close> by simp
    ultimately
    have ?case
      by (metis \<open>a \<in> A\<close> DiffD1 insert_Diff assms(3) finite_Diff psubset.hyps)
  }
  thus ?case
    using assms(2) by blast
qed

lemma finite_linorder_arg_min_is_least:
  assumes \<open>finite {x. Q x}\<close>
  assumes \<open>\<exists>x. Q x\<close>
  fixes f :: \<open>_ \<Rightarrow> _ ::linorder\<close>
  shows \<open>f (ARG_MIN f x. Q x) = (LEAST y. \<exists>x. Q x \<and> f x = y)\<close>
proof -
  let ?C = \<open>{x. Q x}\<close>
  from assms(2) have *: \<open>?C \<noteq> {}\<close>
    by blast
  have \<open>f (ARG_MIN f x. x \<in> ?C) = (LEAST y. \<exists>x. x \<in> ?C \<and> f x = y)\<close>
    using assms(1)
  proof (induction ?C rule: finite_ranking_induct'[where f = f])
    case empty
    then show ?case
      using * by blast
  next
    case (insert x S)
    from insert(2,4) \<comment> \<open>no IH!\<close> show ?case
      by (smt Least_equality arg_min_equality insert_iff order_refl)
  qed
  then show ?thesis
  unfolding arg_min_def is_arg_min_def Least_def
    by force
qed

lemma [intro]:
  assumes \<open>\<And>x. P x \<Longrightarrow> f x = g x\<close>
  shows is_arg_min_eqI: \<open>is_arg_min f P = is_arg_min g P\<close>
    and arg_min_eqI: \<open>arg_min f P = arg_min g P\<close>
proof
  from assms show \<open>is_arg_min f P x = is_arg_min g P x\<close> for x
    unfolding is_arg_min_def by metis
  then show \<open>arg_min f P = arg_min g P\<close>
    unfolding arg_min_def by presburger
qed

lemma forest_empty: \<open>forest \<lparr>nodes = V, edges = {}\<rparr>\<close>
  by unfold_locales simp_all

subsection \<open>Spanning Forests for Graphs of Type @{locale valid_unMultigraph}\<close>

subsubsection \<open>Undirected Hull\<close> \<comment> \<open>or rather: symmetric hull\<close>

lemma is_path_undir_mono:
  \<open>is_path_undir \<lparr>nodes=V, edges=E\<rparr> v p v' \<Longrightarrow> E \<subseteq> E' \<Longrightarrow> is_path_undir \<lparr>nodes=V, edges=E'\<rparr> v p v'\<close>
  by (induction \<open>\<lparr>nodes=V, edges=E'\<rparr>\<close> v p v' rule: is_path_undir.induct) auto
corollary nodes_connected_mono:
  \<open>nodes_connected \<lparr>nodes=V, edges=E\<rparr> v v' \<Longrightarrow> E \<subseteq> E' \<Longrightarrow> nodes_connected \<lparr>nodes=V, edges=E'\<rparr> v v'\<close>
  using is_path_undir_mono by metis

lemma maximally_connected_antimono:
  \<open>maximally_connected H \<lparr>nodes=V, edges=E'\<rparr> \<Longrightarrow> E \<subseteq> E' \<Longrightarrow> maximally_connected H \<lparr>nodes=V, edges=E\<rparr>\<close>
  by (simp add: maximally_connected_def nodes_connected_mono)

definition symhull where
  \<open>symhull E = {(v1,w,v2) | v1 w v2. (v1,w,v2) \<in> E \<or> (v2,w,v1) \<in> E}\<close>

lemma subset_eq_symhull: \<open>E \<subseteq> symhull E\<close>
  by (auto simp: symhull_def)
corollary supergraph_symhull: \<open>subgraph \<lparr>nodes=V, edges=E\<rparr> \<lparr>nodes=V, edges= symhull E\<rparr>\<close>
  by (simp add: subgraph_def subset_eq_symhull)

lemma (in valid_graph) valid_graph_symhull: \<open>valid_graph \<lparr>nodes = V, edges = symhull E\<rparr>\<close>
  apply unfold_locales apply auto using E_valid by (auto simp: symhull_def)

lemma (in valid_graph) valid_unMultigraph_symhull:
  assumes no_id[simp]:\<open>\<And>v w.(v,w,v) \<notin> E\<close>
  shows \<open>valid_unMultigraph \<lparr>nodes = V, edges = symhull E\<rparr>\<close>
  apply unfold_locales
     apply (auto simp: symhull_def)
  using E_validD by blast+

lemma (in valid_graph) symhull_hull:
  assumes no_id:\<open>\<And>v w.(v,w,v) \<notin> E\<close>
  shows \<open>symhull E = (\<lambda>E'. valid_unMultigraph \<lparr>nodes=V, edges=E'\<rparr>) hull E\<close>
  apply (simp add: symhull_def)
  apply (rule hull_unique[symmetric])
    apply auto
   apply (metis no_id symhull_def valid_unMultigraph_symhull)
  proof goal_cases
    case (1 t' v1 w v2)
    then have \<open>(v2, w, v1) \<in> t'\<close>
      by blast
    with 1(2) have \<open>(v1, w, v2) \<in> t'\<close>
      using valid_unMultigraph.corres by fastforce
    then show ?case.
  qed

lemma symhull_altdef: \<open>symhull E = E \<union> (\<lambda>(v1, w, v2). (v2, w, v1)) ` E\<close>
  unfolding symhull_def by force

lemma finite_weighted_graph_symhull_iff:
    \<open>finite_weighted_graph G \<longleftrightarrow> finite_weighted_graph \<lparr>nodes = nodes G, edges = symhull (edges G)\<rparr>\<close>
  unfolding finite_weighted_graph_def finite_graph_def finite_graph_axioms_def apply auto
  using valid_graph.valid_graph_symhull apply blast
  apply (simp add: symhull_altdef)
    using subgraph_def subset_eq_symhull valid_graph.valid_subgraph apply fastforce
    using infinite_super subset_eq_symhull by blast
lemma (in finite_weighted_graph) finite_weighted_graph_symhull:
  \<open>finite_weighted_graph\<lparr>nodes = V, edges = symhull E\<rparr>\<close>
  using finite_weighted_graph_axioms finite_weighted_graph_symhull_iff by blast

lemma is_path_undir_symhull:
  \<open>is_path_undir \<lparr>nodes=V, edges=symhull E\<rparr> v p v' \<Longrightarrow> is_path_undir \<lparr>nodes=V, edges=E\<rparr> v p v'\<close>
  apply (induction \<open>\<lparr>nodes=V, edges=symhull E\<rparr>\<close> v p v' rule: is_path_undir.induct)
   apply (simp_all add: symhull_def) by fast
corollary nodes_connected_symhull:
  \<open>nodes_connected \<lparr>nodes=V, edges=symhull E\<rparr> v v' \<Longrightarrow> nodes_connected \<lparr>nodes=V, edges=E\<rparr> v v'\<close>
  by (meson is_path_undir_symhull)

lemma maximally_connected_symhull:
  \<open>maximally_connected H G \<Longrightarrow> maximally_connected H (G\<lparr>edges:=symhull (edges G)\<rparr>)\<close>
  apply (simp add: maximally_connected_def)
  using nodes_connected_symhull
  by (metis graph.cases graph.select_convs(2) graph.update_convs(2))

lemma subgraph_trans: \<open>subgraph G H \<Longrightarrow> subgraph H I \<Longrightarrow> subgraph G I\<close>
  by (auto simp: subgraph_def) \<comment> \<open>Maybe interpret \<^class>\<open>order_bot\<close>?\<close>

lemma spanning_forest_symhull:
  \<open>spanning_forest F \<lparr>nodes=V, edges = E\<rparr> \<Longrightarrow> spanning_forest F \<lparr>nodes=V, edges = symhull E\<rparr>\<close>
  unfolding spanning_forest_def
  using maximally_connected_symhull subgraph_trans supergraph_symhull by fastforce

lemma infinite_edge_weight: \<open>infinite (edges G) \<Longrightarrow> edge_weight G = 0\<close>
  by (simp add: edge_weight_def)


subsection \<open>Relation To The Digraph's Spanning Forest\<close>

abbreviation \<open>mirror_edge u w v G \<equiv> add_edge v w u (delete_edge u w v G)\<close>

lemma mirror_single_edge_weight:
  assumes \<open>(u,w,v) \<in> E\<close> \<open>(v,w,u) \<notin> E\<close>
  shows \<open>edge_weight (mirror_edge u w v \<lparr>nodes=V, edges=E\<rparr>) = edge_weight \<lparr>nodes=V', edges=E\<rparr>\<close>
  using assms unfolding edge_weight_def apply simp
  by (smt Diff_idemp Diff_insert0 Diff_insert2 finite_insert fst_conv insertCI insert_Diff snd_conv sum.infinite sum.insert_remove)

lemma (in valid_graph) valid_graph_delete_edge: \<open>valid_graph (delete_edge v e v' G)\<close>
  by (simp add: valid_graph_axioms) \<comment> \<open>uses the oddly formed @{thm delete_edge_valid}\<close>

lemma (in forest) no_dups: \<open>(u,w,v) \<in> E \<Longrightarrow> (v,w,u) \<notin> E\<close>
  by (smt E_validD(2) Pair_inject add_delete_edge case_prodE delete_edge_valid forest.cycle_free forest_axioms nodes_delete_edge swap_delete_add_edge valid_graph.add_edge_is_connected(2) valid_graph.is_path_undir_simps(1) valid_graph_axioms)
corollary (in forest) no_loops: \<open>(u,w,u) \<notin> E\<close>
  using no_dups by blast

lemma (in valid_graph) delete_mirrored[simp]:
  \<open>u\<in>V \<Longrightarrow> v\<in>V \<Longrightarrow> delete_edge v w u (mirror_edge u w v G) = delete_edge v w u (delete_edge u w v G)\<close>
  by (simp add: insert_absorb)

lemma (in valid_graph) is_path_undir_mirror_single_iff:
  assumes \<open>(u,w,v) \<in> E\<close>
  shows \<open>(v1,w',v2)\<in>edges (mirror_edge u w v G) \<or> (v2,w',v1)\<in>edges (mirror_edge u w v G)
    \<longleftrightarrow> (v1,w',v2)\<in>edges G \<or> (v2,w',v1)\<in>edges G\<close>
  using assms by auto

lemma (in valid_graph) nodes_connected_mirror_singe_iff[simp]:
  assumes \<open>(u,w,v)\<in>E\<close>
  shows \<open>nodes_connected (mirror_edge u w v G) n n' \<longleftrightarrow> nodes_connected G n n'\<close>
proof -
  {
    assume e: \<open>(u, w, v) \<in> E\<close>
    have *: \<open>nodes_connected G n n'\<close> if \<open>is_path_undir (mirror_edge u w v G) n p n'\<close> for p
      using that
    proof (induction \<open>mirror_edge u w v G\<close> n p n' rule: is_path_undir.induct)
      case (1 v v')
      then show ?case
        by (metis e insert_absorb is_path_undir.simps(1) nodes_add_edge nodes_delete_edge valid_graph.E_validD valid_graph_axioms)
    next
      case (2 v v1 w' v2 p v')
      then show ?case
        apply simp
        by (meson e is_path_undir_simps(2) valid_graph.is_path_undir_append valid_graph_axioms)
    qed
    have \<open>nodes_connected (mirror_edge u w v G) n n'\<close> if \<open>is_path_undir G n p n'\<close> for p
      using that
    proof (induction \<open>mirror_edge u w v G\<close> n p n' rule: is_path_undir.induct)
      case (1 v v')
      then show ?case
        by (metis insert_iff is_path_undir.simps(1) nodes_add_edge nodes_delete_edge)
    next
      case (2 v v1 w' v2 p v')
      then show ?case
        apply simp
        by (meson e is_path_undir.simps(2) valid_graph.is_path_undir_mirror_single_iff valid_graph_axioms)
    qed
    note * this
  }
  then show ?thesis
    using assms
    by blast
qed

lemma (in forest) mirror_single_forest:
  assumes \<open>(u,w,v) \<in> E\<close>
  shows \<open>forest (mirror_edge u w v G)\<close>
proof unfold_locales
  interpret m: valid_graph \<open>mirror_edge u w v G\<close>
    by (simp add: delete_edge_valid')
  show \<open>fst ` edges (mirror_edge u w v G) \<subseteq> nodes (mirror_edge u w v G)\<close>
    using E_valid(1) image_eqI by auto
  show \<open>snd ` snd ` edges (mirror_edge u w v G) \<subseteq> nodes (mirror_edge u w v G)\<close>
    using E_valid(2) by auto
  {
    fix v1 w' v2
    assume mE: \<open>(v1,w',v2) \<in> m.E\<close>
    have V: \<open>v1\<in>V\<close> \<open>v2\<in>V\<close>
      using assms is_path_undir_simps(2) mE by auto
    have \<open>\<not>nodes_connected (delete_edge v1 w' v2 (mirror_edge u w v G)) v1 v2\<close>
    proof (cases \<open>(v1,w',v2) = (v,w,u)\<close>)
      case True
      then have E: \<open>(v2,w',v1) \<in> E\<close>
        using assms by blast
      then have *: \<open>delete_edge v1 w' v2 (mirror_edge u w v G) = delete_edge v2 w' v1 G\<close>
        using True V no_dups by fastforce
      from cycle_free E True have \<open>\<not>nodes_connected \<dots> v2 v1\<close>
        by fast
      then show ?thesis
        by (metis * delete_edge_valid m.valid_graph_axioms valid_graph.is_path_undir_sym)
    next
      case False
      then have *: \<open>valid_graph (delete_edge v1 w' v2 G)\<close> and **: \<open>(u, w, v) \<in> edges (delete_edge v1 w' v2 G)\<close>
        using delete_edge_valid' apply blast using False assms mE by auto
      have \<open>(v1,w',v2) \<in> E\<close>
        using False mE by auto
      with cycle_free have ***: \<open>\<not>nodes_connected (delete_edge v1 w' v2 G) v1 v2\<close>
        by fast
      from False have \<open>delete_edge v1 w' v2 (mirror_edge u w v G) = mirror_edge u w v (delete_edge v1 w' v2 G)\<close>
        by (simp add: swap_delete_add_edge swap_delete_edges)
      moreover have \<open>\<not>nodes_connected \<dots> v1 v2\<close>
        using valid_graph.nodes_connected_mirror_singe_iff[OF * **] *** by blast
      ultimately show ?thesis
        by presburger
    qed
  }
  then show \<open>\<forall>(v1, w', v2) \<in>edges (mirror_edge u w v G). \<not>nodes_connected (delete_edge v1 w' v2 (mirror_edge u w v G)) v1 v2\<close>
    by blast
qed

lemma (in valid_unMultigraph) spanning_forest_mirror_single:
  assumes \<open>spanning_forest \<lparr>nodes=V, edges=F\<rparr> G\<close> and \<open>(u,w,v)\<in>F\<close>
  shows \<open>spanning_forest (mirror_edge u w v \<lparr>nodes=V, edges=F\<rparr>) G\<close>
  using assms apply (simp add: spanning_forest_def)
  apply auto
  proof -
  show forest: \<open>forest (mirror_edge u w v \<lparr>nodes = V, edges = F\<rparr>)\<close>
    if \<open>(u, w, v) \<in> F\<close> and \<open>forest \<lparr>nodes = V, edges = F\<rparr>\<close>
    using that by (simp add: forest.mirror_single_forest)
  show \<open>maximally_connected (mirror_edge u w v \<lparr>nodes = V, edges = F\<rparr>) G\<close>
    if \<open>(u, w, v) \<in> F\<close>
      and \<open>forest \<lparr>nodes = V, edges = F\<rparr>\<close>
      and \<open>maximally_connected \<lparr>nodes = V, edges = F\<rparr> G\<close>
      and \<open>subgraph \<lparr>nodes = V, edges = F\<rparr> G\<close>
    using that
    by (smt forest add_edge_maximally_connected add_edge_preserve_subgraph corres edges_add_edge forest.forest_add_edge forest.no_dups graph.select_convs(2) insert_iff insert_subset nodes_delete_edge subgraph_def swap_delete_add_edge valid_graph.E_validD(1) valid_graph.add_delete_edge valid_graph.delete_edge_maximally_connected valid_graph.valid_subgraph valid_graph_axioms)
  show \<open>subgraph (mirror_edge u w v \<lparr>nodes = V, edges = F\<rparr>) G\<close>
    if \<open>(u, w, v) \<in> F\<close>
      and \<open>forest \<lparr>nodes = V, edges = F\<rparr>\<close>
      and \<open>maximally_connected \<lparr>nodes = V, edges = F\<rparr> G\<close>
      and \<open>subgraph \<lparr>nodes = V, edges = F\<rparr> G\<close>
    using that by (metis (no_types, lifting) corres delete_edge_preserve_subgraph graph.select_convs(2) insert_Diff insert_subset subgraph_def valid_graph.add_edge_preserve_subgraph valid_graph_axioms)
qed

lemma (in finite_weighted_graph) spanning_forest_symhull_preimage:
  assumes no_id[simp]:\<open>\<And>v w.(v,w,v) \<notin> E\<close>
  assumes \<open>spanning_forest \<lparr>nodes=V, edges=F\<rparr> \<lparr>nodes=V, edges=symhull E\<rparr>\<close>
  shows \<open>\<exists>F'. spanning_forest \<lparr>nodes=V, edges=F'\<rparr> \<lparr>nodes=V, edges=E\<rparr>
    \<and> edge_weight \<lparr>nodes=V, edges=F'\<rparr> = edge_weight \<lparr>nodes=V, edges=F\<rparr>\<close>
  using assms
proof (induction \<open>F - E\<close> arbitrary: F rule: infinite_finite_induct) \<comment> \<open>maybe use @{thm diff_induct}?\<close>
  case infinite
  have \<open>finite F\<close>
    by (metis finite_weighted_graph_symhull finite_graph.finite_E finite_weighted_graph.axioms graph.select_convs(2) infinite.prems(2) infinite_super spanning_forest_def subgraph_def)
  with infinite show ?case
    by blast
next
  case empty
  then have \<open>subgraph \<lparr>nodes=V, edges=F\<rparr> \<lparr>nodes=V, edges=E\<rparr>\<close>
    using subgraph_def by fastforce
  then have \<open>spanning_forest \<lparr>nodes=V, edges=F\<rparr> \<lparr>nodes=V, edges=E\<rparr>\<close>
    by (meson empty.prems maximally_connected_antimono spanning_forest_def subset_eq_symhull)
  then show ?case
    by blast
next
  case (insert e I)
  then obtain u w v where x: \<open>e=(u,w,v)\<close>
    by (cases e) blast
  have F_in_symhull: \<open>F \<subseteq> symhull E\<close>
    by (metis graph.select_convs(2) insert.prems(2) spanning_forest_def subgraph_def)
  have f1: \<open>(u, w, v) \<notin> E\<close>
    using insert.hyps(4) x by blast
  have \<open>(u, w, v) \<in> symhull E\<close>
    by (metis Diff_subset \<open>F \<subseteq> symhull E\<close> insert.hyps(4) insertI1 subset_eq x)
  then have \<open>\<exists>a b aa. (u, w, v) = (a, b, aa) \<and> ((a, b, aa) \<in> E \<or> (aa, b, a) \<in> E)\<close>
    by (simp add: symhull_def)
  then have *: \<open>(v,w,u)\<in>E\<close> and **: \<open>e\<notin>E\<close> and ***: \<open>e\<in>F\<close>
      apply (simp add: f1)
    apply (simp add: f1 x)
    using insert.hyps(4) by auto
  with \<open>e \<in> F\<close> have \<open>(v,w,u) \<notin> F\<close>
    using forest.no_dups insert.prems spanning_forest_def x by fastforce
  then have I: \<open>I = edges (mirror_edge u w v \<lparr>nodes=V, edges=F\<rparr>) - E\<close>
    by (metis (no_types, lifting) Diff_insert Diff_insert2 Diff_insert_absorb * edges_add_edge edges_delete_edge graph.select_convs(2) insert.hyps(2) insert.hyps(4) insert_Diff1 x)
  have \<open>forest \<lparr>nodes=V, edges=F\<rparr>\<close>
    using insert.prems spanning_forest_def by blast
  have \<open>valid_unMultigraph \<lparr>nodes = V, edges = symhull E\<rparr>\<close>
    by (simp add: valid_unMultigraph_symhull)
  then have \<open>spanning_forest (mirror_edge u w v \<lparr>nodes = V, edges = F\<rparr>) \<lparr>nodes = V, edges = symhull E\<rparr>\<close>
    using *** insert.prems(2) valid_unMultigraph.spanning_forest_mirror_single x by fastforce
  then obtain F' where
    \<open>spanning_forest \<lparr>nodes = V, edges = F'\<rparr> \<lparr>nodes = V, edges = E\<rparr> \<and>
     edge_weight \<lparr>nodes = V, edges = F'\<rparr> = edge_weight (mirror_edge u w v \<lparr>nodes = V, edges = F\<rparr>)\<close>
    by (metis (no_types, lifting) * insert.hyps(3)[OF I] add_edge_ind delete_edge_def edges_add_edge edges_delete_edge graph.select_convs(1) no_id)
  then show ?case apply(intro exI[where x=\<open>F'\<close>])
     apply safe
      apply simp+ unfolding x apply (rule mirror_single_edge_weight)
    using *** x apply blast
    using \<open>(v, w, u) \<notin> F\<close> by blast
qed

lemma edge_weight_same: \<open>edge_weight \<lparr>nodes=V,edges=E\<rparr> = edge_weight \<lparr>nodes=V',edges=E\<rparr>\<close>
  unfolding edge_weight_def by fastforce

lemma (in finite_weighted_graph) optimal_forest_symhull:
  assumes \<open>\<And>v w.(v,w,v) \<notin> E\<close>
  assumes \<open>optimal_forest F \<lparr>nodes=V, edges=E\<rparr>\<close>
  shows \<open>optimal_forest F \<lparr>nodes=V, edges = symhull E\<rparr>\<close>
  using assms unfolding optimal_forest_def
  by (smt graph.cases graph.select_convs(1) spanning_forest_def spanning_forest_symhull_preimage subgraph_def subgraph_node subgraph_trans subsetI)

lemma (in finite_weighted_graph) minimum_spanning_forest_symhull:
  assumes \<open>\<And>v w.(v,w,v) \<notin> E\<close>
  assumes \<open>minimum_spanning_forest F \<lparr>nodes=V, edges=E\<rparr>\<close>
  shows \<open>minimum_spanning_forest F \<lparr>nodes=V, edges = symhull E\<rparr>\<close>
  using assms by (simp add: minimum_spanning_forest_def optimal_forest_symhull spanning_forest_symhull)

lemma (in finite_weighted_graph) optimal_forest_symhull_preimage:
  assumes \<open>optimal_forest F \<lparr>nodes=V, edges = symhull E\<rparr>\<close>
  shows \<open>optimal_forest F \<lparr>nodes=V, edges=E\<rparr>\<close>
  using assms by (simp add: optimal_forest_def spanning_forest_symhull)

lemma (in finite_weighted_graph) minimum_spanning_forest_symhull_edge_weight:
  assumes \<open>\<And>v w.(v,w,v) \<notin> E\<close>
  assumes \<open>minimum_spanning_forest F \<lparr>nodes=V, edges=E\<rparr>\<close> \<open>minimum_spanning_forest F' \<lparr>nodes=V, edges = symhull E\<rparr>\<close>
  shows \<open>edge_weight F = edge_weight F'\<close>
  using assms
  by (meson antisym minimum_spanning_forest_def optimal_forest_def optimal_forest_symhull optimal_forest_symhull_preimage)

lemma (in finite_weighted_graph) minimum_spanning_tree_symhull_edge_weight:
  assumes \<open>\<And>v w.(v,w,v) \<notin> E\<close>
  assumes \<open>minimum_spanning_tree T \<lparr>nodes=V, edges=E\<rparr>\<close> \<open>minimum_spanning_tree T' \<lparr>nodes=V, edges = symhull E\<rparr>\<close>
  shows \<open>edge_weight T = edge_weight T'\<close>
  using assms minimum_spanning_forest_symhull_edge_weight[unfolded minimum_spanning_forest_def]
  unfolding minimum_spanning_tree_def spanning_tree_def spanning_forest_def tree_def forest_def
  optimal_tree_def apply auto
  by (meson connected_graph.maximally_connected_impl_connected forest.axioms(2) optimal_forest_def spanning_forest_def vE valid_graph.connected_impl_maximally_connected valid_graph.subgraph_impl_connected valid_graph.valid_subgraph valid_graph_symhull)

lemma (in finite_weighted_graph) spanning_tree_impl_connected:
  assumes \<open>spanning_tree F G\<close>
  shows \<open>connected_graph G\<close>
  using assms spanning_tree_def subgraph_impl_connected tree_def by blast

lemma (in finite_weighted_graph) minimum_spanning_tree_symhull:
  assumes \<open>\<And>v w.(v,w,v) \<notin> E\<close>
  assumes \<open>minimum_spanning_tree F G\<close>
  shows \<open>minimum_spanning_tree F \<lparr>nodes=V, edges = symhull E\<rparr>\<close>
  using assms unfolding minimum_spanning_tree_def minimum_spanning_forest_def
  by (metis connected_graph.maximally_connected_impl_connected minimum_spanning_forest_def
      minimum_spanning_forest_symhull optimal_forest_def optimal_tree_def spanning_forest_def
      spanning_tree_def sum_of_parts tree_def valid_graph.connected_impl_maximally_connected
      subgraph_impl_connected valid_graph_axioms valid_graph_symhull)


subsection \<open>Matroid Interpretation\<close>

context finite_weighted_graph \<comment> \<open>first usage in the AFP\<close>
begin \<comment> \<open>@{class weight} might be too special, and @{thm valid_graph_axioms} unneeded\<close>

interpretation m?: weighted_matroid E subforest \<open>\<lambda>(_,w,_). w\<close>
  by (simp add: s.weighted_matroid_axioms)

end

context Kruskal_interface
begin
lemmas k0 = kruskal0_refine minWeightBasis_refine
lemma k0_spec: \<open>kruskal0 \<le> SPEC MSF\<close>
  using k0 unfolding nres_rel_def by auto
end
thm Kruskal_interface.kruskal0_def
context finite_weighted_graph
begin

find_theorems name: MSF_eq
thm s.k0_spec[unfolded MSF_eq]
thm s.kruskal0_def
thm s.kruskal0_def[simplified]
thm spanning_forest_eq
thm MSF_eq

end

locale finite_weighted_connected_graph = finite_weighted_graph + connected_graph
begin

lemma kruskal0_MST: \<open>s.kruskal0 \<le> SPEC (\<lambda>E'. minimum_spanning_tree (ind E') G)\<close>
proof -
  have \<open>minimum_spanning_tree F G\<close> if \<open>minimum_spanning_forest F G\<close> for F
    by (simp add: connected_graph_axioms minimum_spanning_forest_impl_tree2 that)
  with SPEC_cons_rule[OF s.k0_spec[unfolded MSF_eq] this] show ?thesis
    by (simp add: sum_of_parts)
qed

end

locale finite_weighted_connected_loopfree_graph = finite_weighted_connected_graph +
  assumes no_loops: \<open>\<And>v w.(v,w,v) \<notin> E\<close>
begin

lemma kruskal0_MST': \<open>s.kruskal0 \<le> SPEC (\<lambda>E'. minimum_spanning_tree (ind E') \<lparr>nodes=V, edges = symhull E\<rparr>)\<close>
  using kruskal0_MST
proof -
  have \<open>SPEC (\<lambda>E'. minimum_spanning_tree (ind E') G) \<le> SPEC (\<lambda>E'. minimum_spanning_tree (ind E') \<lparr>nodes=V, edges = symhull E\<rparr>)\<close>
    using minimum_spanning_tree_symhull no_loops by force
  with SPEC_trans kruskal0_MST show ?thesis
    by blast
qed

sublocale symhull: valid_unMultigraph \<open>ind (symhull E)\<close>
  by (simp add: no_loops valid_unMultigraph_symhull)

end

subsection \<open>Hamiltonian Circuits\<close>

fun adj_vertices where
  \<open>adj_vertices [] = {}\<close> | \<comment> \<open>maybe better \<^const>\<open>undefined\<close>\<close>
  \<open>adj_vertices ps = insert (snd(snd(last ps))) (set (map fst ps))\<close>

lemma adj_vertices_int_vertices:
  \<open>adj_vertices ps = (case ps of
    [] \<Rightarrow> {} |
    ps \<Rightarrow> insert (snd(snd(last ps))) (int_vertices ps))\<close>
  by (cases ps) (auto simp: int_vertices_def)

lemma adj_vertices_simps[simp]:
    \<open>ps \<noteq> [] \<Longrightarrow> adj_vertices (e#ps) = insert (fst e) (adj_vertices ps)\<close>
    \<open>ps \<noteq> [] \<Longrightarrow> snd(snd(last ps)) = fst e \<Longrightarrow> adj_vertices (ps@[e]) = insert (snd(snd e)) (adj_vertices ps)\<close>
  apply (cases ps) apply auto
    apply (smt Un_iff adj_vertices.elims empty_iff insertCI insertE int_vertices_def int_vertices_simps(1) int_vertices_simps(2) int_vertices_simps(3) last_snoc)
  apply (metis adj_vertices.simps(2) insertCI int_vertices_def list.exhaust op_list_append_elem_def snoc_eq_iff_butlast)
  by (metis (no_types, lifting) Un_iff adj_vertices.elims insertCI insertE int_vertices_def int_vertices_simps(2) int_vertices_simps(3) snoc_eq_iff_butlast)

fun (in valid_graph) is_cycle :: \<open>(_,_) path \<Rightarrow> bool\<close> where \<comment> \<open>to-do: connect to the cycle basis\<close>
  \<open>is_cycle [] \<longleftrightarrow> True\<close> |
  \<open>is_cycle ((v,e)#es) \<longleftrightarrow> is_path_undir G v ((v,e)#es) v \<and> distinct (v # map fst es)\<close>

lemma (in valid_graph) is_cycle_distinct:
  \<open>is_cycle es \<Longrightarrow> distinct (map fst es)\<close> by (cases es) auto

lemma (in valid_graph)
  assumes \<open>x\<noteq>y\<close> \<open>{x,y} \<subseteq> V\<close>
  assumes \<open>{(x,w1,y),(y,w2,y)} \<subseteq> E\<close>
  shows \<open>is_cycle [(x,w1,y),(y,w2,y)]\<close>
  oops
txt \<open>To-do: merge the two definitions below, maybe using @{const Let}?\<close>
fun (in valid_graph) is_simple_undir :: \<open>(_,_) path \<Rightarrow> bool\<close> where
  \<open>is_simple_undir [] \<longleftrightarrow> True\<close> |
  \<open>is_simple_undir ((v,e)#es) \<longleftrightarrow> is_path_undir G v ((v,e)#es) (snd (snd (last ((v,e)#es)))) \<and> distinct (map fst ((v,e)#es))\<close>
definition (in valid_graph) is_simple_undir2 where
  \<open>is_simple_undir2 ps \<longleftrightarrow> is_simple_undir ps \<and> snd (snd (last ps)) \<notin> int_vertices ps\<close>

definition (in valid_graph) is_trace :: \<open>('v,'w) path \<Rightarrow> bool\<close> where \<comment> \<open>non-standard definition.\<close>
  \<open>is_trace ps \<longleftrightarrow> (if ps=[] then V={} else adj_vertices ps = V)\<close>

lemma (in valid_graph) conversion:
  \<open>card V \<noteq> 1 \<Longrightarrow> is_trace ps \<longleftrightarrow> (if ps=[] then V={} \<or> card V = 1 else adj_vertices ps = V)\<close>
  by (simp add: is_trace_def)

lemma (in valid_graph) is_trace_snoc:
  \<open>is_trace (ps @ [p]) \<longleftrightarrow> insert (snd(snd p)) (int_vertices (ps@[p])) = V\<close>
  by (cases ps) (simp_all add: adj_vertices_int_vertices is_trace_def)

definition (in valid_graph) is_hamiltonian_path where \<comment> \<open>or \<open>simple trace\<close>\<close>
  \<open>is_hamiltonian_path ps \<longleftrightarrow> is_trace ps \<and> is_simple_undir2 ps\<close>

definition (in valid_graph) is_hamiltonian_circuit where
  \<open>is_hamiltonian_circuit ps \<longleftrightarrow> int_vertices ps = V \<and> is_cycle ps\<close>

lemma (in valid_graph) is_hamiltonian_circuit_int_vertices:
  \<open>is_hamiltonian_circuit ps \<Longrightarrow> int_vertices ps = V\<close>
  by (simp add: is_hamiltonian_circuit_def)

lemma (in valid_graph) is_hamiltonian_circuit_is_cycle:
  \<open>is_hamiltonian_circuit ps \<Longrightarrow> is_cycle ps\<close>
  by (simp add: is_hamiltonian_circuit_def)

lemma (in valid_graph) is_path_undir_snd_snd_last: \<open>ps \<noteq> [] \<Longrightarrow> is_path_undir G v ps v' \<Longrightarrow> snd (snd (last ps)) = v'\<close>
  by (induction ps arbitrary: v) auto

lemma (in valid_graph) is_cycle_last_eq_first:
  \<open>is_cycle ((v,e)#ps) \<Longrightarrow> snd (snd (last ((v,e)#ps))) = v\<close>
  using is_path_undir_snd_snd_last by fastforce

lemma (in valid_graph) is_cycle_is_simple_undir:
  \<open>is_cycle ps \<Longrightarrow> is_simple_undir ps\<close>
proof (cases ps)
  case Nil
  then show ?thesis
    by force
next
  case (Cons a list)
  moreover assume \<open>is_cycle ps\<close>
  ultimately show ?thesis
    by (smt is_cycle.simps(2) is_simple_undir.elims(3) list.distinct(1) is_cycle_distinct is_path_undir_snd_snd_last)
qed

lemma (in valid_graph) is_simple_undir_is_cycle:
  assumes \<open>is_simple_undir ps\<close>
  assumes \<open>fst (hd ps) = snd (snd (last ps))\<close>
  shows \<open>is_cycle ps\<close>
  using assms by (smt fst_conv is_cycle.elims(3) is_simple_undir.simps(2) list.sel(1) list.simps(9))

lemma (in valid_graph) is_hamiltonian_circuit_length:
  \<open>is_hamiltonian_circuit ps \<Longrightarrow> length ps = card V\<close>
  unfolding is_hamiltonian_circuit_def int_vertices_def by (metis distinct_card length_map is_cycle_distinct)

lemma (in valid_graph) is_hamiltonian_circuit_singleton:
  \<open>V = {v} \<Longrightarrow> is_hamiltonian_circuit ps \<Longrightarrow> \<exists>w. ps=[(v,w,v)]\<close>
proof goal_cases
  case 1
  then have \<open>length ps = 1\<close>
    using is_hamiltonian_circuit_length by auto
  then obtain v1 v2 where v1v2: \<open>\<exists>w. ps = [(v1, w, v2)]\<close>
    using list_decomp_1 by fastforce
  with 1 show ?case
    using is_hamiltonian_circuit_def by auto
qed

lemma (in valid_graph) is_hamiltonian_circuit_empty: \<open>is_hamiltonian_circuit [] \<longleftrightarrow> V = {}\<close>
  unfolding is_hamiltonian_circuit_def by fastforce

term \<open>valid_graph.is_path\<close>
find_theorems \<open>valid_graph.is_path\<close>

text \<open>Reuse @{const kon_graph}, but interpreted differently: Between to-do and to-do, there are
  four edges, two of which have the same label.\<close>

definition \<open>kon_path = [(a,ab1,b),(b,bd1,d),(d,cd1,c)]\<close>

lemma is_simple_path_kon_path: \<open>kon_graph.is_simple_undir2 kon_path\<close>
  unfolding kon_graph.is_simple_undir2_def by (simp add: kon_path_def) (simp add: kon_graph_def)

lemma is_hamiltonian_path_kon_path: \<open>kon_graph.is_hamiltonian_path kon_path\<close>
  apply (simp add: kon_graph.is_hamiltonian_path_def is_simple_path_kon_path)
  apply (simp add: kon_path_def kon_graph.is_trace_def)
  apply eval
  done

definition \<open>kon_circuit = kon_path @ [(c,ac2,a)]\<close>

lemma is_simple_path_kon_circuit: \<open>kon_graph.is_simple_undir kon_circuit\<close>
  by (simp add: kon_circuit_def kon_path_def) (simp add: kon_graph_def)

lemma is_hamiltonian_circuit_kon_circuit: \<open>kon_graph.is_hamiltonian_circuit kon_circuit\<close>
  unfolding kon_graph.is_hamiltonian_circuit_def
  apply (auto simp: kon_circuit_def kon_path_def)
           apply (auto simp: kon_graph_def)
  done

text \<open>to-do: Complete notes on the DFS phase without the notion \<open>Eulerian\<close>.\<close>

subsection \<open>Tours and Costs\<close>

context finite_weighted_graph
begin

abbreviation cost where
  \<open>cost \<equiv> sum_list \<circ> (map (fst \<circ> snd))\<close>

abbreviation set_cost where
  \<open>set_cost E' \<equiv> edge_weight (ind E')\<close>

lemma edge_weight_sum_list: \<open>distinct ps \<Longrightarrow> edge_weight \<lparr>nodes=ARBITRARY, edges= set ps\<rparr> = sum_list (map (fst \<circ> snd) ps)\<close>
  unfolding edge_weight_def by (auto simp: sum_list_distinct_conv_sum_set)

lemma is_hamiltonian_circuit_distinct_vertices:
  \<open>is_hamiltonian_circuit ps \<Longrightarrow> distinct (map fst ps)\<close>
  by (cases ps) (auto simp: is_hamiltonian_circuit_def)

lemma is_hamiltonian_circuit_distinct_edges:
  \<open>is_hamiltonian_circuit ps \<Longrightarrow> distinct ps\<close>
  using is_hamiltonian_circuit_distinct_vertices distinct_mapI by blast

lemma tour_edge_weight:
  \<open>is_hamiltonian_circuit ps \<and> cost ps = w \<longleftrightarrow>
   is_hamiltonian_circuit ps \<and> edge_weight \<lparr>nodes=V, edges= set ps\<rparr> = w\<close>
  by (auto simp: edge_weight_sum_list is_hamiltonian_circuit_distinct_edges)

definition OPT_alt where
  \<open>OPT_alt = (ARG_MIN (edge_weight \<circ> ind \<circ> set) ps . is_hamiltonian_circuit ps)\<close>

definition OPT where
  \<open>OPT = (ARG_MIN (sum_list \<circ> (map (fst \<circ> snd))) ps . is_hamiltonian_circuit ps)\<close>

lemma OPT_sanity: \<open>OPT = OPT_alt\<close> unfolding OPT_def OPT_alt_def
  using is_hamiltonian_circuit_distinct_edges[THEN edge_weight_sum_list] by fastforce

definition OPTWEIGHT where
  \<open>OPTWEIGHT = Min {w. (\<exists>ps. is_hamiltonian_circuit ps \<and> cost ps = w)}\<close>

end

subsection \<open>Complete Graphs\<close>

text \<open>The definition below is non-standard: It allows for additional edges, e.g. loops.\<close>
locale complete_finite_weighted_graph = finite_weighted_graph +
  assumes complete: \<open>v1\<in>V \<Longrightarrow> v2\<in>V \<Longrightarrow> v1\<noteq>v2 \<Longrightarrow> \<exists>w. (v1,w,v2)\<in>E \<or> (v2,w,v1)\<in>E\<close>
    \<comment> \<open>maybe use \<^const>\<open>Ex1\<close>?\<close>

context finite_weighted_graph
begin

lemma complete_finite_weighted_graph_sanity_check:
  \<open>complete_finite_weighted_graph G \<longleftrightarrow> (\<forall>v1\<in>V. \<forall>v2\<in>V. v1\<noteq>v2 \<longrightarrow> (\<exists>w. (v1,w,v2) \<in> E) \<or> (\<exists>w. (v2,w,v1) \<in> E))\<close>
  by (meson complete_finite_weighted_graph_axioms_def complete_finite_weighted_graph_def finite_weighted_graph_axioms)

lemma complete_finite_weighted_graph_intro:
  assumes \<open>\<And>v1 v2. v1\<in>V \<Longrightarrow> v2\<in>V \<Longrightarrow> (\<exists>w. (v1,w,v2) \<in> E) \<or> (\<exists>w. (v2,w,v1) \<in> E)\<close>
  shows \<open>complete_finite_weighted_graph G\<close>
  using assms complete_finite_weighted_graph_sanity_check by blast

end

lemma (in valid_graph) delete_node_was_simple_undir:
  \<open>valid_graph.is_simple_undir (delete_node v G) ps \<Longrightarrow> is_simple_undir ps\<close>
  by (smt delete_node_valid is_simple_undir.simps delete_node_was_path
    valid_graph.is_simple_undir.elims(2) valid_graph_axioms)

lemma (in valid_graph) is_simple_undir_Cons[intro]:
  assumes \<open>fst (hd ps) = v'\<close>
  assumes \<open>(v,w,v') \<in> E \<or> (v',w,v) \<in> E\<close>
  assumes \<open>v \<notin> int_vertices ps\<close>
  assumes \<open>is_simple_undir ps\<close>
  shows \<open>is_simple_undir ((v,w,v')#ps)\<close>
  using assms by (cases ps) (auto simp: int_vertices_def E_validD)

lemma (in valid_graph) is_simple_undir_step:
  assumes \<open>is_simple_undir ((x,w,y) # ps)\<close>
  shows \<open>(x,w,y) \<in> E \<or> (y,w,x) \<in> E\<close> \<open>x \<notin> int_vertices ps\<close> \<open>is_simple_undir ps\<close> \<open>ps \<noteq> [] \<Longrightarrow> fst (hd ps) = y\<close>
  using assms by (auto simp: int_vertices_def) (cases ps, auto)+

lemma (in valid_graph) is_path_undir_last: \<comment> \<open>duplicates @{thm is_path_undir_snd_snd_last}\<close>
  \<open>ps \<noteq> [] \<Longrightarrow> is_path_undir G v ps v' \<Longrightarrow> v' = snd (snd (last ps))\<close>
  by (induction ps arbitrary: v) auto

lemma (in valid_graph) is_simple_undir2_step:
  \<open>is_simple_undir2 ((x,w,y) # ps) \<Longrightarrow>
    ((x,w,y) \<in> E \<or> (y,w,x) \<in> E) \<and> x \<notin> adj_vertices ps \<and> is_simple_undir2 ps\<close>
  by (cases ps) (auto simp: is_simple_undir2_def is_path_undir_last)

lemma (in valid_graph) finite_adj_vertices:
  \<open>finite (adj_vertices ps)\<close>
  by (cases ps) simp_all

lemma (in valid_graph) hamiltonian_impl_finiteV:
  \<open>is_hamiltonian_path ps \<Longrightarrow> finite V\<close>
  unfolding is_hamiltonian_path_def is_trace_def
  by (metis finite.emptyI kon_graph.finite_adj_vertices)

lemma (in valid_graph) is_cycle_rotate1:
  assumes \<open>is_cycle (e#ps)\<close>
  shows \<open>is_cycle (ps@[e])\<close>
  using assms apply (cases e) apply (induction ps)
  by (auto simp: E_validD)

lemma (in valid_graph) is_hamiltonian_circuit_rotate1':
  assumes \<open>is_hamiltonian_circuit (e#ps)\<close>
  shows \<open>is_hamiltonian_circuit (ps@[e])\<close>
  using assms unfolding is_hamiltonian_circuit_def by (simp add: is_cycle_rotate1)

lemma (in valid_graph) is_hamiltonian_circuit_rotate1:
  assumes \<open>is_hamiltonian_circuit ps\<close>
  shows \<open>is_hamiltonian_circuit (rotate1 ps)\<close>
  using assms by (cases ps) (auto simp: assms is_hamiltonian_circuit_rotate1')

lemma (in finite_graph) finitely_many_hamiltonian_circuits:
  \<open>finite {ps. is_hamiltonian_circuit ps}\<close>
proof -
  have \<open>set ps \<subseteq> E \<union> (\<lambda>(v1,w,v2). (v2,w,v1)) ` E\<close> if \<open>is_hamiltonian_circuit ps\<close> for ps
    using that unfolding is_hamiltonian_circuit_def
    apply (cases ps) apply (auto simp: rev_image_eqI) using is_path_undir_memb_edges
    by (metis (mono_tags, lifting) old.prod.case rev_image_eqI)+
  moreover have \<open>finite \<dots>\<close>
    by (simp add: finite_E)
  moreover have \<open>length ps = card V\<close> if \<open>is_hamiltonian_circuit ps\<close> for ps
    using is_hamiltonian_circuit_length that by blast
  ultimately show ?thesis
    using finite_lists_length_eq[of \<open>E \<union> (\<lambda>(v1,w,v2). (v2,w,v1)) ` E\<close> \<open>card V\<close>]
    by (smt Collect_cong finite_Collect_conjI)
qed

context complete_finite_weighted_graph
begin

sublocale finite_weighted_connected_graph \<comment> \<open>rm?\<close>
  by unfold_locales (metis complete is_path_undir.simps(1) is_path_undir_simps(2))

lemma complete': \<open>v1\<in>V \<Longrightarrow> v2\<in>V \<Longrightarrow> v1\<noteq>v2 \<Longrightarrow> (\<exists>w. (v1,w,v2)\<in>E) \<or> (\<exists>w. (v2,w,v1)\<in>E)\<close>
  using complete by blast

lemma complete_finite_weighted_graph_delete_node:
  \<open>complete_finite_weighted_graph (delete_node v G)\<close>
  apply intro_locales
    apply (simp add: valid_graph_axioms)
   apply unfold_locales unfolding delete_node_def
    apply auto
  using complete by blast

lemma ex_hamiltonian_circuit:
  assumes \<open>2 \<le> card V\<close> \<open>v\<in>V\<close>
  shows \<open>\<exists>ps. is_hamiltonian_circuit ps \<and> fst (hd ps) = v\<close>
  using assms complete_finite_weighted_graph_axioms
proof (induction \<open>card V\<close> arbitrary: v G rule: nat_induct_at_least[of 2])
  case base
  then interpret G: complete_finite_weighted_graph G
    by simp
  from base(1-2) obtain v' where GV: \<open>G.V = {v,v'}\<close> \<open>v \<noteq> v'\<close>
    by (metis card2_get2 doubleton_eq_iff insertE singletonD)
  then have v': \<open>v' \<in> G.V\<close>
    by blast+
  with GV base(2) obtain w where w: \<open>(v,w,v') \<in> G.E \<or> (v',w,v) \<in> G.E\<close>
    using G.complete by blast
  show ?case
    apply (rule exI[of _ \<open>[(v,w,v'),(v',w,v)]\<close>])
    apply (auto simp: G.is_hamiltonian_circuit_def base v' GV w)
    using w by blast
next
  case (Suc n)
  interpret G: complete_finite_weighted_graph G
    by (simp add: Suc.prems)
  let ?G = \<open>delete_node v G\<close>
  interpret G': complete_finite_weighted_graph ?G
    by (fact G.complete_finite_weighted_graph_delete_node)
  from Suc have nG': \<open>G'.V = G.V - {v}\<close> \<open>2 \<le> card G'.V\<close> and n: \<open>n = card G'.V\<close>
    unfolding delete_node_def by force+
  from nG'(2) obtain v' where v: \<open>v'\<in>G'.V\<close>
    using Suc.hyps(1) by fastforce
  with \<open>v \<in> G.V\<close> obtain w where w: \<open>(v,w,v') \<in> G.E \<or> (v',w,v) \<in> G.E\<close>
    unfolding nG' using G.complete by fast
  from Suc.hyps(2)[OF n v G'.complete_finite_weighted_graph_axioms]
  obtain ps' where ps': \<open>G'.is_hamiltonian_circuit ps' \<and> fst (hd ps') = v'\<close> by blast
  have G': \<open>int_vertices ps' = G'.V\<close> \<open>G'.is_simple_undir ps'\<close> \<open>fst (hd ps') = v'\<close> \<open>snd (snd (last ps')) = v'\<close>
   apply (auto simp: ps'[unfolded G'.is_hamiltonian_circuit_def])
    apply (simp add: G'.is_cycle_is_simple_undir G'.is_hamiltonian_circuit_is_cycle ps')
    by (metis (no_types, hide_lams) G'.is_cycle_last_eq_first G'.valid_graph_axioms empty_iff int_vertices_simps(1) list.sel(1) neq_NilE ps' triple_of_parts v valid_graph.is_hamiltonian_circuit_def)
  then have *: \<open>int_vertices ps' = G'.V\<close> \<open>G.is_simple_undir ps'\<close>
    using G.delete_node_was_simple_undir by auto
  then have \<open>v \<notin> int_vertices ps'\<close>
    using nG' by blast
  from * G'(2) obtain w_discard v1 ps'' where ps'': \<open>ps' = (v',w_discard,v1)#ps''\<close>
    by (metis empty_iff hd_Cons_tl int_vertices_simps(1) ps' triple_of_parts v)
  then have \<open>v1 \<in> G.V\<close> \<open>v \<notin> int_vertices ps''\<close>
    using *(2) G.valid_graph_axioms apply fastforce
    using \<open>v \<notin> int_vertices ps'\<close> ps'' by auto
  with *(1) obtain w1 where **: \<open>(v,w1,v1) \<in> G.E \<or> (v1,w1,v) \<in> G.E\<close>
    by (metis G'(2) G'.E_validD(1) G'.E_validD(2) G'.is_simple_undir_step(1) G.complete Suc.prems(1) \<open>v \<notin> int_vertices ps'\<close> ps'')
  let ?ps = \<open>(v',w,v)#(v,w1,v1)#ps''\<close>
  from Suc have non_empty: \<open>ps'' \<noteq> []\<close>
    by (metis G'.valid_graph_axioms Nitpick.size_list_simp(2) One_nat_def Suc_1 Suc_n_not_le_n n neq_Nil_conv ps' ps'' tl_Nil valid_graph.is_hamiltonian_circuit_length)
  from *(2)[unfolded ps''] have \<open>G.is_simple_undir ps''\<close>
    using G.is_simple_undir_step(3) by blast
  with ** have \<open>G.is_simple_undir ((v,w1,v1)#ps'')\<close>
    apply (intro G.is_simple_undir_Cons)
    using \<open>v \<notin> int_vertices ps''\<close> \<open>v \<in> G.V\<close> apply (auto simp add: int_vertices_def)
    using *(2)[unfolded ps''] G.is_simple_undir_step(3-4)
    using non_empty apply blast+
    done
  moreover have \<open>v' \<notin> int_vertices ((v,w1,v1)#ps'')\<close>
    using G.is_simple_undir_step(2) \<open>G.is_simple_undir ((v', w_discard, v1) # ps'')\<close> \<open>v \<notin> int_vertices ps'\<close> ps'' by auto
  ultimately have \<open>G.is_hamiltonian_circuit ?ps\<close>
    unfolding G.is_hamiltonian_circuit_def
    apply safe
      defer defer
    apply (rule G.is_simple_undir_is_cycle)
    apply (metis G.is_simple_undir_Cons Pair_inject \<open>v' \<notin> int_vertices ((v, w1, v1) # ps'')\<close> list.sel(1) prod.collapse w)
    using G'(4) ps'' apply auto[1]
    apply (metis G'(1) G.delete_node_was_path Suc.prems(1) fst_conv insert_iff int_vertices_simps(2)
        is_path_undir.simps(1) ps'') using nG' G' ps'' by auto
  then show ?case
    using G.is_hamiltonian_circuit_rotate1 by fastforce
qed

lemma ex_hamiltonian_circuit':
  assumes \<open>2 \<le> card V\<close>
  shows \<open>\<exists>ps. is_hamiltonian_circuit ps\<close>
proof -
  from assms obtain v where v: \<open>v \<in> V\<close>
    by fastforce
  from ex_hamiltonian_circuit[OF assms this] obtain ps where \<open>is_hamiltonian_circuit ps \<and> fst (hd ps) = v\<close>
    by fast
  then show ?thesis
    by blast
qed

lemma is_arg_min_OPT:
  assumes \<open>2 \<le> card V\<close>
  shows \<open>is_arg_min (sum_list \<circ> (map (fst \<circ> snd))) (\<lambda>ps. is_hamiltonian_circuit ps) OPT\<close>
proof -
  note finitely_many_hamiltonian_circuits
  note ex_is_arg_min_if_finite[OF this, of \<open>sum_list \<circ> (map (fst \<circ> snd))\<close>]
  with ex_hamiltonian_circuit'[OF assms]
  show ?thesis
    unfolding OPT_def unfolding arg_min_def apply simp
    by (meson exE_some)
qed

lemma OPT_sanity:
  assumes \<open>2 \<le> card V\<close>
  shows \<open>cost OPT = OPTWEIGHT\<close>
proof -
  note finitely_many_hamiltonian_circuits
  have ***: \<open>OPTWEIGHT = (LEAST w. \<exists>ps. is_hamiltonian_circuit ps \<and> cost ps = w)\<close>
    unfolding OPTWEIGHT_def apply (rule Least_Min[symmetric])
     apply auto using finitely_many_hamiltonian_circuits apply force
    by (simp add: assms ex_hamiltonian_circuit')
  show ?thesis unfolding OPT_def ***
    using finite_linorder_arg_min_is_least[of \<open>\<lambda>ps. is_hamiltonian_circuit ps\<close> cost] assms
      ex_hamiltonian_circuit' finitely_many_hamiltonian_circuits by fastforce
qed

subsection \<open>SPEC\<close>

abbreviation twoApprox where
  \<open>twoApprox \<equiv> SPEC (\<lambda>T. is_hamiltonian_circuit T \<and> cost T \<le> OPTWEIGHT + OPTWEIGHT)\<close>

definition algo_sketch where \<open>algo_sketch =
do {
  MST \<leftarrow> SPEC (\<lambda>E'. minimum_spanning_tree (ind E') G);
  pretour \<leftarrow> SPEC (\<lambda>pT. int_vertices pT = V \<and> cost pT \<le> set_cost MST + set_cost MST);
  Tour \<leftarrow> SPEC (\<lambda>T. is_hamiltonian_circuit T \<and> cost T \<le> cost pretour);
  RETURN Tour
}\<close>

lemma (in valid_graph) neuland: \<open>is_simple_undir2 ((x,w,y)#ps) \<Longrightarrow> x\<noteq>y\<close>
  unfolding is_simple_undir2_def by (cases ps) auto

lemma (in valid_graph) neuland': \<open>is_simple_undir2 ((x,w,y)#ps) \<Longrightarrow> x \<notin> adj_vertices ps\<close>
  using is_simple_undir2_step by blast

lemma (in valid_graph) is_simple_undir2_adj_vertices_Cons:
  \<open>is_simple_undir2 ((x,w,y) # ps) \<Longrightarrow> ps\<noteq>[] \<Longrightarrow> adj_vertices ((x,w,y) # ps) = insert x (adj_vertices ps)\<close>
  unfolding is_simple_undir2_def using adj_vertices_simps(1) by fastforce

lemma (in valid_graph) is_path_undir_adj_vertices:
  \<open>is_path_undir G v ps v' \<Longrightarrow> (x,w,y) \<in> set ps \<Longrightarrow> x \<in> adj_vertices ps\<close>
  \<open>is_path_undir G v ps v' \<Longrightarrow> (x,w,y) \<in> set ps \<Longrightarrow> y \<in> adj_vertices ps\<close>
   apply (metis adj_vertices.elims empty_iff empty_set img_fst insert_iff list.set_map)
proof (induction ps arbitrary: v)
  case (Cons _ ps)
  then show ?case
    apply (cases ps) by auto (metis is_path_undir.simps(2) prod.collapse)+
qed simp

lemma (in valid_graph) tmp':
  assumes \<open>v \<noteq> y\<close> \<open>nodes_connected \<lparr>nodes = V, edges = set ps\<rparr> v y\<close> \<open>is_simple_undir2 ps\<close>
  shows \<open>v \<in> adj_vertices ps\<close>
proof -
  from assms(1-2) obtain w y where \<open>(v,w,y) \<in> set ps \<or> (y,w,v) \<in> set ps\<close>
    apply auto apply (case_tac p) by auto blast+
  with assms(3) show ?thesis
    by (metis empty_iff empty_set is_simple_undir.elims(2) is_simple_undir2_def is_path_undir_adj_vertices)
qed

lemma (in -) is_path_undir_supset: \<open>is_path_undir \<lparr>nodes=V, edges=E\<rparr> v ps v' \<Longrightarrow> V \<subseteq> V' \<Longrightarrow> is_path_undir \<lparr>nodes=V', edges=E\<rparr> v ps v'\<close>
  by (induction ps arbitrary: v) auto

lemma (in -) delte_edge_supset: \<open>nodes (delete_edge x w y G) \<subseteq> nodes (delete_edge x w y (add_node v G))\<close>
  by (simp add: subset_insertI)

lemma (in valid_graph) rm: \<open>connected_graph G \<longleftrightarrow> (\<forall>v \<in> V. \<forall>v' \<in> V. nodes_connected G v v')\<close>
  by (simp add: connected_graph_axioms_def connected_graph_def valid_graph_axioms)

lemma (in valid_graph) nodes_connected_add_edge:
  assumes \<open>nodes_connected G v' v''\<close>
  shows \<open>nodes_connected (add_edge v w v' G) v v''\<close>
proof -
  from assms obtain ps where \<open>is_path_undir G v' ps v''\<close>
    by blast
  then have \<open>is_path_undir (add_edge v w v' G) v' ps v''\<close>
    by (simp add: add_edge_is_path)
  then have \<open>is_path_undir (add_edge v w v' G) v ((v,w,v')#ps) v''\<close>
    by simp
  then show ?thesis
    by blast
qed

lemma (in valid_graph) is_simple_undir2_forest:
  assumes \<open>is_simple_undir2 ps\<close>
  shows \<open>forest \<lparr>nodes = V, edges = set ps\<rparr>
 \<and> (\<forall>v \<in> adj_vertices ps. \<forall>v' \<in> adj_vertices ps. nodes_connected \<lparr>nodes = V, edges = set ps\<rparr> v v')\<close>
  using assms
proof (induction ps)
  case (Cons e ps)
  then obtain v w v' where e[simp]: \<open>e=(v,w,v')\<close>
    by (cases e) (simp add: is_simple_undir2_def)
  have ne: \<open>v \<noteq> v'\<close>
    using Cons.prems neuland by auto
  have ne': \<open>v \<notin> adj_vertices ps\<close> \<comment> \<open>fixme: unused. also @{thm neuland'}\<close>
    using Cons.prems neuland' by auto
  from Cons interpret grove: forest \<open>\<lparr>nodes = V, edges = set ps\<rparr>\<close>
    using is_simple_undir2_step by force
  have \<open>\<lparr>nodes = V, edges = set (e#ps)\<rparr> = add_edge v w v' \<lparr>nodes = V, edges = set ps\<rparr>\<close>
    apply auto
    by (smt Cons.prems e edges_add_edge graph.select_convs(1) graph.select_convs(2) insert_absorb nodes_add_edge sum_of_parts valid_graph.E_validD(1) valid_graph.E_validD(2) valid_graph.is_simple_undir2_step valid_graph_axioms)
  also have \<open>forest \<dots> \<and> (\<forall>v\<in>adj_vertices (e#ps). \<forall>v'\<in>adj_vertices (e#ps). nodes_connected \<dots> v v')\<close>
    apply rule
    apply (rule grove.forest_add_edge)
    apply (metis add_edge_valid calculation graph.select_convs(1) grove.valid_graph_axioms valid_graph.add_edge_is_connected(1) valid_graph.is_path_undir_memb)
      apply (metis add_edge_valid calculation graph.select_convs(1) grove.add_edge_is_connected(1) grove.valid_graph_axioms valid_graph.is_path_undir_memb)
    subgoal
  proof (cases \<open>ps = []\<close>)
    case True
    then show ?thesis
      using is_path_undir.elims(2) ne by fastforce
  next
    case False
    then show ?thesis
      by (metis Cons.prems e is_simple_undir2_step neuland tmp')
  qed subgoal
  proof (cases \<open>ps = []\<close>)
    case True
    then show ?thesis apply auto
      apply (metis add_edge_valid empty_set grove.add_edge_is_connected(2) grove.valid_graph_axioms is_path_undir.simps(1) valid_graph.is_path_undir_memb)
      using grove.add_edge_is_connected(2) apply auto[1]
      using grove.add_edge_is_connected(1) apply auto[1]
      by (meson add_edge_valid forest.axioms(1) forest_empty is_path_undir.simps(1) valid_graph.add_edge_is_connected(1) valid_graph.is_path_undir_memb)
  next
    case False
    have *: \<open>adj_vertices (e#ps) = insert v (adj_vertices ps)\<close>
      by (metis Cons.prems False e is_simple_undir2_adj_vertices_Cons)
    have \<open>v' \<in> adj_vertices ps\<close>
      by (metis * Cons.prems calculation finite_list grove.add_edge_is_connected(2) finite_adj_vertices list.simps(15) ne set_ConsD tmp')
    then have \<open>nodes_connected \<lparr>nodes = V, edges = set ps\<rparr> v' v''\<close> if \<open>v'' \<in> adj_vertices ps\<close> for v''
      by (metis Cons.IH Cons.prems e that valid_graph.is_simple_undir2_step valid_graph_axioms)
    then have ***: \<open>nodes_connected (add_edge v w v' \<lparr>nodes = V, edges = set ps\<rparr>) v v''\<close> if \<open>v'' \<in> adj_vertices ps\<close> for v''
      by (simp add: grove.nodes_connected_add_edge that)
    from * show ?thesis apply (auto simp: False)
         apply (meson add_edge_valid grove.add_edge_is_connected(2) grove.valid_graph_axioms valid_graph.is_path_undir_memb valid_graph.is_path_undir_simps(1))
      prefer 3
      apply (meson \<open>\<And>v''. v'' \<in> adj_vertices ps \<Longrightarrow> nodes_connected \<lparr>nodes = V, edges = set ps\<rparr> v' v''\<close> grove.add_edge_is_path grove.is_path_undir_append grove.nodes_connected_sym)
       apply (rule ***)
      apply blast
      by (meson *** add_edge_valid grove.valid_graph_axioms valid_graph.is_path_undir_sym)
  qed done
  finally show ?case .
qed (simp add: forest_empty)

corollary (in valid_graph) hamiltonian_path_is_tree:
  assumes \<open>is_hamiltonian_path ps\<close>
  shows \<open>tree \<lparr>nodes=V, edges = set ps\<rparr>\<close>
  using assms unfolding is_hamiltonian_path_def is_trace_def tree_def
  by (metis empty_iff forest.axioms(1) graph.select_convs(1) is_simple_undir2_forest valid_graph.rm)

lemma (in connected_graph) spanning_tree_eq: \<open>spanning_tree \<lparr>nodes=V, edges=F\<rparr> G \<longleftrightarrow> spanning_forest \<lparr>nodes=V, edges=F\<rparr> G\<close>
  by (meson maximally_connected_impl_connected spanning_forest_def spanning_tree_def tree_def connected_impl_maximally_connected)

lemma (in valid_graph) is_path_undir_edges_symhull:
  \<open>is_path_undir G v ps v' \<Longrightarrow> set ps \<subseteq> symhull E\<close>
  unfolding symhull_def using is_path_undir_memb_edges by fast

lemma is_hamiltonian_circuit_OPT:
  \<open>2 \<le> card V \<Longrightarrow> is_hamiltonian_circuit OPT\<close>
  using is_arg_min_OPT by (simp add: is_arg_min_def)

end

locale complete_finite_metric_graph = complete_finite_weighted_graph G for G :: \<open>(_,_::canonically_ordered_monoid_add) graph\<close>
\<comment> \<open>to-do: replace constraint with actual metricity.\<close>
begin

lemma minimum_spanning_tree_le_OPTWEIGHT:
  assumes \<open>minimum_spanning_tree (ind F) G\<close>
  assumes \<open>2 \<le> card V\<close>
  assumes no_id:\<open>\<And>v w.(v,w,v) \<notin> E\<close> \<comment> \<open>removable\<close>
  shows \<open>set_cost F \<le> OPTWEIGHT\<close>
proof -
  have \<open>2 \<le> length OPT\<close>
    using assms(2) is_hamiltonian_circuit_OPT is_hamiltonian_circuit_length by presburger
  moreover have \<open>snd (snd (last OPT)) = fst (hd OPT)\<close>
    by (metis (no_types, hide_lams) Nitpick.size_list_simp(2) Suc_1 assms(2) is_hamiltonian_circuit_OPT list.sel(1) neq_Nil_conv not_less_eq_eq prod.collapse is_cycle_last_eq_first is_hamiltonian_circuit_def is_hamiltonian_circuit_length zero_order(1))
  moreover have \<open>tl OPT \<noteq> []\<close>
    by (metis Nitpick.size_list_simp(2) One_nat_def Suc_1 Suc_leD Suc_n_not_le_n calculation(1))
  ultimately have \<open>is_hamiltonian_path (tl OPT)\<close>
    using is_hamiltonian_circuit_OPT[OF assms(2)]
    unfolding is_hamiltonian_circuit_def is_hamiltonian_path_def is_trace_def
    apply safe apply simp
    apply (metis (no_types, hide_lams) adj_vertices.simps(2) int_vertices_def int_vertices_simps(2)
        list.exhaust_sel tl_Nil tl_last)
    by (smt distinct_tl fst_conv is_cycle.elims(2) is_cycle_last_eq_first is_path_undir.simps(2) is_simple_undir2_def is_simple_undir_step(2) list.sel(3) tl_Nil tl_last triple_of_parts is_cycle_distinct is_simple_undir.elims(3))
  then have *: \<open>spanning_tree (ind (set (tl OPT))) (ind (symhull E))\<close>
    unfolding spanning_tree_def apply auto
     apply (simp add: assms(2) hamiltonian_path_is_tree)
    unfolding subgraph_def apply auto
    by (metis Nitpick.size_list_simp(2) One_nat_def Suc_1 Suc_leD Suc_n_not_le_n \<open>2 \<le> length OPT\<close> assms(2) is_hamiltonian_circuit_OPT in_set_tlD is_cycle.elims(2) is_path_undir_edges_symhull subsetD is_hamiltonian_circuit_def)
  have **: \<open>set_cost F \<le> set_cost F'\<close> if \<open>spanning_tree (ind F') (ind (symhull E))\<close> for F'
    using that assms(1) minimum_spanning_tree_def minimum_spanning_tree_symhull no_id optimal_tree_def by blast
  have \<open>cost (tl OPT) \<le> cost OPT\<close>
    by (cases OPT) simp_all
  also have \<open>\<dots> \<le> OPTWEIGHT\<close>
    using OPT_sanity assms(2) by auto
  finally show ?thesis
    by (smt * ** assms(2) comp_def distinct_tl edge_weight_sum_list is_hamiltonian_circuit_OPT is_hamiltonian_circuit_distinct_edges order_trans)
qed

proposition
  assumes \<open>2 \<le> card V\<close>
  assumes \<open>\<And>v w.(v,w,v) \<notin> E\<close> \<comment> \<open>removable\<close>
  shows \<open>algo_sketch \<le> twoApprox\<close>
  unfolding algo_sketch_def apply refine_vcg apply auto
proof goal_cases
  case (1 MST pretour Tour)
  note 1(5)
  also have \<open>sum_list (map (fst \<circ> snd) pretour) \<le> set_cost MST + set_cost MST\<close>
    by (fact 1(3))
  also have \<open>\<dots> \<le> OPTWEIGHT + OPTWEIGHT\<close>
    by (simp add: 1(1) add_mono assms minimum_spanning_tree_le_OPTWEIGHT)
  finally show ?case .
qed

end

subsection \<open>Symmetric TSP\<close>

section \<open>Generating Example Input\<close>

subsection \<open>Manhattan Distance\<close>

text \<open>1d-coordinates:\<close>

lemma manhattan: \<open>nat\<bar>c-a\<bar> \<le> nat\<bar>b-a\<bar> + nat\<bar>c-b\<bar>\<close> for a b c :: int
  by (simp add: nat_le_iff)

subsection \<open>Euclidean Distance, Rounded Up\<close>
  \<comment> \<open>attempt only if too much time at the end\<close>

text \<open>dummy citation: @{cite lawler}.\<close>

end

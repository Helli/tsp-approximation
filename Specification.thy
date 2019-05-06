section \<open>Specification\<close>
theory Specification
  imports
    Koenigsberg_Friendship.KoenigsbergBridge
    Graph_Definition_Impl
    "HOL-ex.Sketch_and_Explore"
begin

lemma sum_of_parts(*rm*): \<open>\<lparr>nodes= nodes G, edges=edges G\<rparr> = G\<close>
  by simp

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
  case (insert x I)
  then obtain u w v where x: \<open>x=(u,w,v)\<close>
    by (meson prod_cases3)
  have F_in_symhull: \<open>F \<subseteq> symhull E\<close>
    by (metis graph.select_convs(2) insert.prems(2) spanning_forest_def subgraph_def)
  have f1: \<open>(u, w, v) \<notin> E\<close>
    using insert.hyps(4) x by blast
  have \<open>(u, w, v) \<in> symhull E\<close>
    by (metis Diff_subset \<open>F \<subseteq> symhull E\<close> insert.hyps(4) insertI1 subset_eq x)
  then have \<open>\<exists>a b aa. (u, w, v) = (a, b, aa) \<and> ((a, b, aa) \<in> E \<or> (aa, b, a) \<in> E)\<close>
    by (simp add: symhull_def)
  then have *: \<open>(v,w,u)\<in>E\<close> and **: \<open>x\<notin>E\<close> and ***: \<open>x\<in>F\<close>
      apply (simp add: f1)
    apply (simp add: f1 x)
    using insert.hyps(4) by auto
  with \<open>x \<in> F\<close> have \<open>(v,w,u) \<notin> F\<close>
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
thm s.k0_spec[unfolded MSF_eq, simplified]
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

definition (in valid_graph) is_simple_undir :: \<open>_ \<Rightarrow> (_,_) path \<Rightarrow> _ \<Rightarrow> bool\<close> where
  \<open>is_simple_undir v ps v' \<longleftrightarrow> is_path_undir G v ps v' \<and> distinct (map fst ps)\<close>
find_theorems \<open>int_vertices\<close>

definition (in valid_graph) is_trace :: \<open>('v,'w) path \<Rightarrow> bool\<close> where \<comment> \<open>non-standard definition. Also not thoroughly thought through.\<close>
  \<open>is_trace ps \<longleftrightarrow> (if ps=[] then V={} \<or> card V = 1 else insert (snd(snd(last ps))) (int_vertices ps) = V)\<close>

lemma (in valid_graph) is_trace_snoc:
  \<open>is_trace (ps @ [p]) \<longleftrightarrow> insert (snd(snd p)) (int_vertices (ps@[p])) = V\<close>
  by (simp add: is_trace_def)

definition (in valid_graph) is_hamiltonian_path where \<comment> \<open>or \<open>simple trace\<close>\<close>
  \<open>is_hamiltonian_path v ps v' \<longleftrightarrow> is_trace ps \<and> is_simple_undir v ps v'\<close>

definition (in valid_graph) is_hamiltonian :: \<open>('v,'w) path \<Rightarrow> bool\<close> where \<comment> \<open>to-do: unconventional intermediate definition, only for experimentation\<close>
  \<open>is_hamiltonian ps \<longleftrightarrow> (if ps=[] then V={} \<or> card V = 1 else int_vertices ps = V)\<close>

definition (in valid_graph) is_hamiltonian_circuit where
  \<open>is_hamiltonian_circuit v ps \<longleftrightarrow> is_hamiltonian ps \<and> is_simple_undir v ps v\<close>

lemma (in valid_graph) is_hamiltonian_iff: \<open>is_hamiltonian_path v ps v \<longleftrightarrow> is_hamiltonian_circuit v ps\<close>
  apply (cases ps rule: rev_cases)
   apply (simp_all add: is_hamiltonian_path_def is_hamiltonian_circuit_def is_trace_def is_hamiltonian_def is_simple_undir_def)
  by auto (smt fst_conv insert_iff int_vertices_simps(2) is_path_undir.elims(1))+

term \<open>valid_graph.is_path\<close>
find_theorems \<open>valid_graph.is_path\<close>

text \<open>Reuse @{const kon_graph}, but interpreted differently: Between to-do and to-do, there are
  four edges, two of which have the same label.\<close>

definition \<open>kon_path = [(a,ab1,b),(b,bd1,d),(d,cd1,c)]\<close>

lemma is_simple_path_kon_path: \<open>kon_graph.is_simple_undir a kon_path c\<close>
  unfolding kon_graph.is_simple_undir_def by (simp add: kon_path_def) (simp add: kon_graph_def)

lemma is_hamiltonian_path_kon_path: \<open>kon_graph.is_hamiltonian_path a kon_path c\<close>
  apply (simp add: kon_graph.is_hamiltonian_path_def is_simple_path_kon_path)
  apply (simp add: kon_path_def kon_graph.is_trace_def)
  apply eval
  done

definition \<open>kon_circuit = kon_path @ [(c,ac2,a)]\<close>

lemma is_simple_path_kon_circuit: \<open>kon_graph.is_simple_undir a kon_circuit a\<close>
  unfolding kon_graph.is_simple_undir_def by (simp add: kon_circuit_def kon_path_def) (simp add: kon_graph_def)

lemma is_hamiltonian_circuit_kon_circuit: \<open>kon_graph.is_hamiltonian_circuit a kon_circuit\<close>
  unfolding kon_graph.is_hamiltonian_circuit_def kon_graph.is_hamiltonian_def
  apply (auto simp: is_simple_path_kon_circuit)
   by (auto simp: kon_circuit_def kon_path_def kon_graph_def)

text \<open>to-do: Complete notes on the DFS phase without the notion \<open>Eulerian\<close>.\<close>

subsection \<open>Tours\<close>

context finite_weighted_graph
begin

abbreviation
  \<open>tour ps w \<equiv> is_hamiltonian_circuit (fst (hd ps)) ps \<and> sum_list (map (fst o snd) ps) = w\<close>

lemma edge_weight_sum_list: \<open>distinct ps \<Longrightarrow> edge_weight \<lparr>nodes=ARBITRARY, edges= set ps\<rparr> = sum_list (map (fst o snd) ps)\<close>
  unfolding edge_weight_def by (auto simp: sum_list_distinct_conv_sum_set)

lemma is_simple_undir_distinct: \<open>is_simple_undir v ps v' \<Longrightarrow> distinct ps\<close>
  by (induction ps arbitrary: v) (auto simp: is_simple_undir_def)

lemma is_hamiltonian_circuit_distinct:
  \<open>is_hamiltonian_circuit v ps \<Longrightarrow> distinct ps\<close>
  by (auto simp: is_hamiltonian_circuit_def is_simple_undir_distinct)

lemma tour_edge_weight:
  \<open>tour ps w \<longleftrightarrow> is_hamiltonian_circuit (fst (hd ps)) ps \<and> edge_weight \<lparr>nodes=V, edges= set ps\<rparr> = w\<close>
  by (auto simp: edge_weight_sum_list is_hamiltonian_circuit_distinct)

definition OPT_alt where
  \<open>OPT_alt = (ARG_MIN (edge_weight \<circ> ind \<circ> set) ps . is_hamiltonian_circuit (fst (hd ps)) ps)\<close>

definition OPT where
  \<open>OPT = (ARG_MIN (sum_list \<circ> (map (fst \<circ> snd))) ps . is_hamiltonian_circuit (fst (hd ps)) ps)\<close>

lemma sanity: \<open>OPT = OPT_alt\<close> unfolding OPT_def OPT_alt_def
  using is_hamiltonian_circuit_distinct[THEN edge_weight_sum_list] by fastforce

definition OPTWEIGHT where
  \<open>OPTWEIGHT = Min {w. (\<exists>ps. tour ps w)}\<close>

lemma
  assumes \<open>is_hamiltonian_circuit v ps\<close>
  shows \<open>sum_list (map (fst \<circ> snd) OPT) = OPTWEIGHT\<close>
proof -
  from assms have True
    unfolding OPT_def OPTWEIGHT_def
    oops

end

locale complete_finite_weighted_graph = finite_weighted_graph +
  assumes complete: \<open>v1\<in>V \<Longrightarrow> v2\<in>V \<Longrightarrow> \<exists>w. (v1,w,v2) \<in> E \<or> (v2,w,v1) \<in> E\<close>

lemma (in finite_weighted_graph) complete_finite_weighted_graph_sanity_check:
  \<open>complete_finite_weighted_graph G \<longleftrightarrow> (\<forall>v1\<in>V. \<forall>v2\<in>V. (\<exists>w. (v1,w,v2) \<in> E) \<or> (\<exists>w. (v2,w,v1) \<in> E))\<close>
  by (meson complete_finite_weighted_graph_axioms_def complete_finite_weighted_graph_def finite_weighted_graph_axioms)

lemma (in finite_weighted_graph) complete_finite_weighted_graph_intro:
  assumes \<open>\<And>v1 v2. v1\<in>V \<Longrightarrow> v2\<in>V \<Longrightarrow> (\<exists>w. (v1,w,v2) \<in> E) \<or> (\<exists>w. (v2,w,v1) \<in> E)\<close>
  shows \<open>complete_finite_weighted_graph G\<close>
  using assms complete_finite_weighted_graph_sanity_check by blast

thm finite_weighted_graph.complete_finite_weighted_graph_intro
  complete_finite_weighted_graph.intro[unfolded complete_finite_weighted_graph_axioms_def]

context complete_finite_weighted_graph
begin

lemma complete': \<open>v1\<in>V \<Longrightarrow> v2\<in>V \<Longrightarrow> (\<exists>w. (v1,w,v2) \<in> E) \<or> (\<exists>w. (v2,w,v1) \<in> E)\<close>
  using complete by blast

lemma ex_hamiltonian_circuit:
  assumes \<open>v\<in>V\<close>
  shows \<open>\<exists>ps. is_hamiltonian_circuit v ps\<close>
proof -
  from assms s.finiteV have \<open>card V > 0\<close>
    using card_0_eq by blast
  then show ?thesis
    apply (induction \<open>card V\<close> rule: nat_induct_non_zero)
  oops

end

subsection \<open>Symmetric TSP\<close>

section \<open>Generating Example Input\<close>

subsection \<open>Manhattan Distance\<close>

text \<open>1d-coordinates:\<close>

lemma manhattan: \<open>nat\<bar>c-a\<bar> \<le> nat\<bar>b-a\<bar> + nat\<bar>c-b\<bar>\<close> for a b c :: int
  by (simp add: nat_le_iff)

subsection \<open>Euclidean Distance, Rounded Up\<close>
  \<comment> \<open>attempt only if too much time at the end\<close>

section \<open>Junk\<close>

context valid_graph begin
context assumes
  finE: \<open>finite E\<close>
begin

definition dg where \<open>dg v R = card {(w,v'). (v,w,v')\<in>R} + card {(v',w).(v',w,v)\<in>R}\<close>

lemma assumes \<open>finite R'\<close> \<open>R \<subseteq> R'\<close> shows dg_mono: \<open>dg v R \<le> dg v R'\<close>
proof -
  from assms(1) have \<open>finite {(w,v').(v,w,v')\<in>R'}\<close> (is \<open>finite ?A\<close>)
  proof -
    from \<open>finite R'\<close> have \<open>finite ((fst o snd) ` R')\<close> \<open>finite ((snd o snd) ` R')\<close>
      by blast+
    then have f: \<open>finite {(w,v'). w \<in> (fst o snd) ` R' \<and> v' \<in> ((snd o snd) ` R')}\<close>
      by simp
    have \<open>?A = {(w,v'). (v,w,v')\<in>R' \<and> w \<in> (fst o snd) ` R' \<and> v' \<in> ((snd o snd) ` R')}\<close>
      by (auto simp: rev_image_eqI)
    also have \<open>\<dots> \<subseteq> {(w,v'). w \<in> (fst o snd) ` R' \<and> v' \<in> ((snd o snd) ` R')}\<close>
      by blast
    finally show ?thesis
      using f finite_subset by blast
  qed
  with assms(2) have l: \<open>card {(w,v').(v,w,v')\<in>R} \<le> card {(w,v').(v,w,v')\<in>R'}\<close>
    by (smt Collect_mono_iff card_mono case_prodE case_prodI2 subsetD)
  from assms(1) have \<open>finite {(v',w).(v',w,v)\<in>R'}\<close> (is \<open>finite ?B\<close>)
  proof -
    from \<open>finite R'\<close> have \<open>finite (fst ` R')\<close> \<open>finite ((fst o snd) ` R')\<close>
      by blast+
    then have f: \<open>finite {(w,v'). w \<in> fst ` R' \<and> v' \<in> ((fst o snd) ` R')}\<close>
      by simp
    have \<open>?B = {(v',w). (v',w,v)\<in>R' \<and> v' \<in> fst ` R' \<and> w \<in> ((fst o snd) ` R')}\<close>
      by (auto simp: rev_image_eqI)
    also have \<open>\<dots> \<subseteq> {(v',w). v' \<in> fst ` R' \<and> w \<in> ((fst o snd) ` R')}\<close>
      by blast
    finally show ?thesis
      using f finite_subset by blast
  qed
  with assms(2) have r: \<open>card {(v',w).(v',w,v)\<in>R} \<le> card {(v',w).(v',w,v)\<in>R'}\<close>
    by (smt Collect_mono_iff card_mono case_prodD case_prodI2 subsetD)
  from l r show ?thesis
    by (simp add: dg_def)
qed

lemma \<open>indep_system E (\<lambda>E'. E'\<subseteq>E \<and> (\<forall>v\<in>V. dg v E' \<le> 1))\<close>
  apply standard
     apply (simp add: finE)
    apply blast
   apply (rule exI[of _ \<open>{}\<close>])
   apply (simp add: dg_def)
  apply auto
  by (meson dg_mono finE finite_subset le_trans)

end
end

text \<open>dummy citation: @{cite lawler}.\<close>

end

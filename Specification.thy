section \<open>Specification\<close>
theory Specification
  imports
    Koenigsberg_Friendship.KoenigsbergBridge
    Graph_Definition_Impl
    "HOL-ex.Sketch_and_Explore"
begin

lemma sum_of_parts(*rm*): "\<lparr>nodes= nodes G, edges=edges G\<rparr> = G"
  by simp

subsection \<open>Spanning Forests for Graphs of Type @{locale valid_unMultigraph}\<close>

subsubsection \<open>Undirected Hull\<close> \<comment> \<open>or rather: symmetric hull\<close>

lemma is_path_undir_mono:
  "is_path_undir \<lparr>nodes=V, edges=E\<rparr> v p v' \<Longrightarrow> E \<subseteq> E' \<Longrightarrow> is_path_undir \<lparr>nodes=V, edges=E'\<rparr> v p v'"
  by (induction "\<lparr>nodes=V, edges=E'\<rparr>" v p v' rule: is_path_undir.induct) auto
corollary nodes_connected_mono:
  "nodes_connected \<lparr>nodes=V, edges=E\<rparr> v v' \<Longrightarrow> E \<subseteq> E' \<Longrightarrow> nodes_connected \<lparr>nodes=V, edges=E'\<rparr> v v'"
  using is_path_undir_mono by metis

lemma maximally_connected_antimono:
  "maximally_connected H \<lparr>nodes=V, edges=E'\<rparr> \<Longrightarrow> E \<subseteq> E' \<Longrightarrow> maximally_connected H \<lparr>nodes=V, edges=E\<rparr>"
  by (simp add: maximally_connected_def nodes_connected_mono)

definition symhull where
  "symhull E = {(v1,w,v2) | v1 w v2. (v1,w,v2) \<in> E \<or> (v2,w,v1) \<in> E}"

lemma subset_eq_symhull: "E \<subseteq> symhull E"
  by (auto simp: symhull_def)
corollary supergraph_symhull: "subgraph \<lparr>nodes=V, edges=E\<rparr> \<lparr>nodes=V, edges= symhull E\<rparr>"
  by (simp add: subgraph_def subset_eq_symhull)

lemma (in valid_graph) valid_graph_symhull: "valid_graph \<lparr>nodes = V, edges = symhull E\<rparr>"
  apply unfold_locales apply auto using E_valid by (auto simp: symhull_def)

lemma (in valid_graph) valid_unMultigraph_symhull:
  assumes no_id[simp]:"\<And>v w.(v,w,v) \<notin> E"
  shows "valid_unMultigraph \<lparr>nodes = V, edges = symhull E\<rparr>"
  apply unfold_locales
     apply (auto simp: symhull_def)
  using E_validD by blast+

lemma (in valid_graph) symhull_hull:
  assumes no_id:"\<And>v w.(v,w,v) \<notin> E"
  shows "symhull E = (\<lambda>E'. valid_unMultigraph \<lparr>nodes=V, edges=E'\<rparr>) hull E"
  apply (simp add: symhull_def)
  apply (rule hull_unique[symmetric])
    apply auto
   apply (metis no_id symhull_def valid_unMultigraph_symhull)
  proof goal_cases
    case (1 t' v1 w v2)
    then have "(v2, w, v1) \<in> t'"
      by blast
    with "1"(2) have "(v1, w, v2) \<in> t'"
      using valid_unMultigraph.corres by fastforce
    then show ?case.
  qed

lemma symhull_altdef: \<open>symhull E = E \<union> (\<lambda>(v1, w, v2). (v2, w, v1)) ` E\<close>
  unfolding symhull_def by force

lemma finite_weighted_graph_symhull_iff:
    "finite_weighted_graph G \<longleftrightarrow> finite_weighted_graph \<lparr>nodes = nodes G, edges = symhull (edges G)\<rparr>"
  unfolding finite_weighted_graph_def finite_graph_def finite_graph_axioms_def apply auto
  using valid_graph.valid_graph_symhull apply blast
  apply (simp add: symhull_altdef)
    using subgraph_def subset_eq_symhull valid_graph.valid_subgraph apply fastforce
    using infinite_super subset_eq_symhull by blast
lemma (in finite_weighted_graph) finite_weighted_graph_symhull:
  "finite_weighted_graph\<lparr>nodes = V, edges = symhull E\<rparr>"
  using finite_weighted_graph_axioms finite_weighted_graph_symhull_iff by blast

lemma is_path_undir_symhull:
  "is_path_undir \<lparr>nodes=V, edges=symhull E\<rparr> v p v' \<Longrightarrow> is_path_undir \<lparr>nodes=V, edges=E\<rparr> v p v'"
  apply (induction "\<lparr>nodes=V, edges=symhull E\<rparr>" v p v' rule: is_path_undir.induct)
   apply (simp_all add: symhull_def) by fast
corollary nodes_connected_symhull:
  "nodes_connected \<lparr>nodes=V, edges=symhull E\<rparr> v v' \<Longrightarrow> nodes_connected \<lparr>nodes=V, edges=E\<rparr> v v'"
  by (meson is_path_undir_symhull)

lemma maximally_connected_symhull:
  "maximally_connected H G \<Longrightarrow> maximally_connected H (G\<lparr>edges:=symhull (edges G)\<rparr>)"
  apply (simp add: maximally_connected_def)
  using nodes_connected_symhull
  by (metis graph.cases graph.select_convs(2) graph.update_convs(2))

lemma subgraph_trans: "subgraph G H \<Longrightarrow> subgraph H I \<Longrightarrow> subgraph G I"
  by (auto simp: subgraph_def) \<comment> \<open>Maybe interpret \<^class>\<open>order_bot\<close>?\<close>

lemma spanning_forest_symhull:
  "spanning_forest F \<lparr>nodes=V, edges = E\<rparr> \<Longrightarrow> spanning_forest F \<lparr>nodes=V, edges = symhull E\<rparr>"
  unfolding spanning_forest_def
  using maximally_connected_symhull subgraph_trans supergraph_symhull by fastforce

lemma infinite_edge_weight: "infinite (edges G) \<Longrightarrow> edge_weight G = 0"
  by (simp add: edge_weight_def)


subsection \<open>Relation To The Digraph's Spanning Forest\<close>

abbreviation "mirror_edge u w v G \<equiv> add_edge v w u (delete_edge u w v G)"

lemma mirror_single_edge_weight:
  assumes "(u,w,v) \<in> E" "(v,w,u) \<notin> E"
  shows "edge_weight (mirror_edge u w v \<lparr>nodes=V, edges=E\<rparr>) = edge_weight \<lparr>nodes=V', edges=E\<rparr>"
  using assms unfolding edge_weight_def apply simp
  by (smt Diff_idemp Diff_insert0 Diff_insert2 finite_insert fst_conv insertCI insert_Diff snd_conv sum.infinite sum.insert_remove)

lemma (in valid_graph) valid_graph_delete_edge: \<open>valid_graph (delete_edge v e v' G)\<close>
  by (simp add: valid_graph_axioms) \<comment> \<open>uses the oddly formed @{thm delete_edge_valid}\<close>

lemma (in forest) no_dups: "(u,w,v) \<in> E \<Longrightarrow> (v,w,u) \<notin> E"
  by (smt E_validD(2) Pair_inject add_delete_edge case_prodE delete_edge_valid forest.cycle_free forest_axioms nodes_delete_edge swap_delete_add_edge valid_graph.add_edge_is_connected(2) valid_graph.is_path_undir_simps(1) valid_graph_axioms)
corollary (in forest) no_loops: "(u,w,u) \<notin> E"
  using no_dups by blast

lemma (in valid_graph) delete_mirrored[simp]:
  "u\<in>V \<Longrightarrow> v\<in>V \<Longrightarrow> delete_edge v w u (mirror_edge u w v G) = delete_edge v w u (delete_edge u w v G)"
  by (simp add: insert_absorb)

lemma (in valid_graph) is_path_undir_mirror_single_iff:
  assumes \<open>(u,w,v) \<in> E\<close>
  shows "(v1,w',v2)\<in>edges (mirror_edge u w v G) \<or> (v2,w',v1)\<in>edges (mirror_edge u w v G)
    \<longleftrightarrow> (v1,w',v2)\<in>edges G \<or> (v2,w',v1)\<in>edges G"
  using assms by auto

lemma (in valid_graph) nodes_connected_mirror_singe_iff[simp]:
  assumes \<open>(u,w,v)\<in>E\<close>
  shows "nodes_connected (mirror_edge u w v G) n n' \<longleftrightarrow> nodes_connected G n n'"
proof -
  {
    assume e: "(u, w, v) \<in> E"
    have *: "nodes_connected G n n'" if "is_path_undir (mirror_edge u w v G) n p n'" for p
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
    have "nodes_connected (mirror_edge u w v G) n n'" if "is_path_undir G n p n'" for p
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
  assumes "(u,w,v) \<in> E"
  shows "forest (mirror_edge u w v G)"
proof unfold_locales
  interpret m: valid_graph \<open>mirror_edge u w v G\<close>
    by (simp add: delete_edge_valid')
  show "fst ` edges (mirror_edge u w v G) \<subseteq> nodes (mirror_edge u w v G)"
    using E_valid(1) image_eqI by auto
  show "snd ` snd ` edges (mirror_edge u w v G) \<subseteq> nodes (mirror_edge u w v G)"
    using E_valid(2) by auto
  {
    fix v1 w' v2
    assume mE: \<open>(v1,w',v2) \<in> m.E\<close>
    have V: \<open>v1\<in>V\<close> \<open>v2\<in>V\<close>
      using assms is_path_undir_simps(2) mE by auto
    have "\<not>nodes_connected (delete_edge v1 w' v2 (mirror_edge u w v G)) v1 v2"
    proof (cases "(v1,w',v2) = (v,w,u)")
      case True
      then have E: \<open>(v2,w',v1) \<in> E\<close>
        using assms by blast
      then have *: "delete_edge v1 w' v2 (mirror_edge u w v G) = delete_edge v2 w' v1 G"
        using True V no_dups by fastforce
      from cycle_free E True have "\<not>nodes_connected \<dots> v2 v1"
        by fast
      then show ?thesis
        by (metis * delete_edge_valid m.valid_graph_axioms valid_graph.is_path_undir_sym)
    next
      case False
      then have *: "valid_graph (delete_edge v1 w' v2 G)" and **: "(u, w, v) \<in> edges (delete_edge v1 w' v2 G)"
        using delete_edge_valid' apply blast using False assms mE by auto
      have \<open>(v1,w',v2) \<in> E\<close>
        using False mE by auto
      with cycle_free have ***: "\<not>nodes_connected (delete_edge v1 w' v2 G) v1 v2"
        by fast
      from False have "delete_edge v1 w' v2 (mirror_edge u w v G) = mirror_edge u w v (delete_edge v1 w' v2 G)"
        by (simp add: swap_delete_add_edge swap_delete_edges)
      moreover have "\<not>nodes_connected \<dots> v1 v2"
        using valid_graph.nodes_connected_mirror_singe_iff[OF * **] *** by blast
      ultimately show ?thesis
        by presburger
    qed
  }
  then show "\<forall>(v1, w', v2) \<in>edges (mirror_edge u w v G). \<not>nodes_connected (delete_edge v1 w' v2 (mirror_edge u w v G)) v1 v2"
    by blast
qed

lemma (in valid_unMultigraph) spanning_forest_mirror_single:
  assumes "spanning_forest \<lparr>nodes=V, edges=F\<rparr> G" and "(u,w,v)\<in>F"
  shows "spanning_forest (mirror_edge u w v \<lparr>nodes=V, edges=F\<rparr>) G"
  using assms apply (simp add: spanning_forest_def)
  apply auto
  proof -
  show forest: "forest (mirror_edge u w v \<lparr>nodes = V, edges = F\<rparr>)"
    if "(u, w, v) \<in> F" and "forest \<lparr>nodes = V, edges = F\<rparr>"
    using that by (simp add: forest.mirror_single_forest)
  show "maximally_connected (mirror_edge u w v \<lparr>nodes = V, edges = F\<rparr>) G"
    if "(u, w, v) \<in> F"
      and "forest \<lparr>nodes = V, edges = F\<rparr>"
      and "maximally_connected \<lparr>nodes = V, edges = F\<rparr> G"
      and "subgraph \<lparr>nodes = V, edges = F\<rparr> G"
    using that
    by (smt forest add_edge_maximally_connected add_edge_preserve_subgraph corres edges_add_edge forest.forest_add_edge forest.no_dups graph.select_convs(2) insert_iff insert_subset nodes_delete_edge subgraph_def swap_delete_add_edge valid_graph.E_validD(1) valid_graph.add_delete_edge valid_graph.delete_edge_maximally_connected valid_graph.valid_subgraph valid_graph_axioms)
  show "subgraph (mirror_edge u w v \<lparr>nodes = V, edges = F\<rparr>) G"
    if "(u, w, v) \<in> F"
      and "forest \<lparr>nodes = V, edges = F\<rparr>"
      and "maximally_connected \<lparr>nodes = V, edges = F\<rparr> G"
      and "subgraph \<lparr>nodes = V, edges = F\<rparr> G"
    using that by (metis (no_types, lifting) corres delete_edge_preserve_subgraph graph.select_convs(2) insert_Diff insert_subset subgraph_def valid_graph.add_edge_preserve_subgraph valid_graph_axioms)
qed

lemma (in finite_weighted_graph) spanning_forest_symhull_preimage:
  assumes no_id[simp]:"\<And>v w.(v,w,v) \<notin> E"
  assumes "spanning_forest \<lparr>nodes=V, edges=F\<rparr> \<lparr>nodes=V, edges=symhull E\<rparr>"
  shows "\<exists>F'. spanning_forest \<lparr>nodes=V, edges=F'\<rparr> \<lparr>nodes=V, edges=E\<rparr>
    \<and> edge_weight \<lparr>nodes=V, edges=F'\<rparr> = edge_weight \<lparr>nodes=V, edges=F\<rparr>"
  using assms
proof (induction "F - E" arbitrary: F rule: infinite_finite_induct)
  case infinite
  have "finite F"
    by (metis finite_weighted_graph_symhull finite_graph.finite_E finite_weighted_graph.axioms graph.select_convs(2) infinite.prems(2) infinite_super spanning_forest_def subgraph_def)
  with infinite show ?case
    by blast
next
  case empty
  then have "subgraph \<lparr>nodes=V, edges=F\<rparr> \<lparr>nodes=V, edges=E\<rparr>"
    using subgraph_def by fastforce
  then have "spanning_forest \<lparr>nodes=V, edges=F\<rparr> \<lparr>nodes=V, edges=E\<rparr>"
    by (meson empty.prems maximally_connected_antimono spanning_forest_def subset_eq_symhull)
  then show ?case
    by blast
next
  case (insert x I)
  then obtain u w v where x: "x=(u,w,v)"
    by (meson prod_cases3)
  have F_in_symhull: "F \<subseteq> symhull E"
    by (metis graph.select_convs(2) insert.prems(2) spanning_forest_def subgraph_def)
  have f1: "(u, w, v) \<notin> E"
    using insert.hyps(4) x by blast
  have "(u, w, v) \<in> symhull E"
    by (metis Diff_subset \<open>F \<subseteq> symhull E\<close> insert.hyps(4) insertI1 subset_eq x)
  then have "\<exists>a b aa. (u, w, v) = (a, b, aa) \<and> ((a, b, aa) \<in> E \<or> (aa, b, a) \<in> E)"
    by (simp add: symhull_def)
  then have *: "(v,w,u)\<in>E" and **: "x\<notin>E" and ***: "x\<in>F"
      apply (simp add: f1)
    apply (simp add: f1 x)
    using insert.hyps(4) by auto
  with \<open>x \<in> F\<close> have "(v,w,u) \<notin> F"
    using forest.no_dups insert.prems spanning_forest_def x by fastforce
  then have I: "I = edges (mirror_edge u w v \<lparr>nodes=V, edges=F\<rparr>) - E"
    by (metis (no_types, lifting) Diff_insert Diff_insert2 Diff_insert_absorb * edges_add_edge edges_delete_edge graph.select_convs(2) insert.hyps(2) insert.hyps(4) insert_Diff1 x)
  have "forest \<lparr>nodes=V, edges=F\<rparr>"
    using insert.prems spanning_forest_def by blast
  have \<open>valid_unMultigraph \<lparr>nodes = V, edges = symhull E\<rparr>\<close>
    by (simp add: valid_unMultigraph_symhull)
  then have "spanning_forest (mirror_edge u w v \<lparr>nodes = V, edges = F\<rparr>) \<lparr>nodes = V, edges = symhull E\<rparr>"
    using *** insert.prems(2) valid_unMultigraph.spanning_forest_mirror_single x by fastforce
  then obtain F' where
    "spanning_forest \<lparr>nodes = V, edges = F'\<rparr> \<lparr>nodes = V, edges = E\<rparr> \<and>
     edge_weight \<lparr>nodes = V, edges = F'\<rparr> = edge_weight (mirror_edge u w v \<lparr>nodes = V, edges = F\<rparr>)"
    by (metis (no_types, lifting) * insert.hyps(3)[OF I] add_edge_ind delete_edge_def edges_add_edge edges_delete_edge graph.select_convs(1) no_id)
  then show ?case apply(intro exI[where x="F'"])
     apply safe
      apply simp+ unfolding x apply (rule mirror_single_edge_weight)
    using "***" x apply blast
    using \<open>(v, w, u) \<notin> F\<close> by blast
qed

lemma edge_weight_same: "edge_weight \<lparr>nodes=V,edges=E\<rparr> = edge_weight \<lparr>nodes=V',edges=E\<rparr>"
  unfolding edge_weight_def by fastforce

lemma (in finite_weighted_graph) optimal_forest_symhull:
  assumes "\<And>v w.(v,w,v) \<notin> E"
  assumes "optimal_forest F \<lparr>nodes=V, edges=E\<rparr>"
  shows "optimal_forest F \<lparr>nodes=V, edges = symhull E\<rparr>"
  using assms unfolding optimal_forest_def
  by (smt graph.cases graph.select_convs(1) spanning_forest_def spanning_forest_symhull_preimage subgraph_def subgraph_node subgraph_trans subsetI)

lemma (in finite_weighted_graph) minimum_spanning_forest_symhull:
  assumes "\<And>v w.(v,w,v) \<notin> E"
  assumes "minimum_spanning_forest F \<lparr>nodes=V, edges=E\<rparr>"
  shows "minimum_spanning_forest F \<lparr>nodes=V, edges = symhull E\<rparr>"
  using assms by (simp add: minimum_spanning_forest_def optimal_forest_symhull spanning_forest_symhull)

lemma (in finite_weighted_graph) optimal_forest_symhull_preimage:
  assumes "optimal_forest F \<lparr>nodes=V, edges = symhull E\<rparr>"
  shows "optimal_forest F \<lparr>nodes=V, edges=E\<rparr>"
  using assms by (simp add: optimal_forest_def spanning_forest_symhull)

lemma (in finite_weighted_graph) minimum_spanning_forest_symhull_edge_weight:
  assumes "\<And>v w.(v,w,v) \<notin> E"
  assumes "minimum_spanning_forest F \<lparr>nodes=V, edges=E\<rparr>" "minimum_spanning_forest F' \<lparr>nodes=V, edges = symhull E\<rparr>"
  shows "edge_weight F = edge_weight F'"
  using assms
  by (meson antisym minimum_spanning_forest_def optimal_forest_def optimal_forest_symhull optimal_forest_symhull_preimage)

lemma (in finite_weighted_graph) minimum_spanning_tree_symhull_edge_weight:
  assumes \<open>\<And>v w.(v,w,v) \<notin> E\<close>
  assumes "minimum_spanning_tree T \<lparr>nodes=V, edges=E\<rparr>" "minimum_spanning_tree T' \<lparr>nodes=V, edges = symhull E\<rparr>"
  shows "edge_weight T = edge_weight T'"
  using assms minimum_spanning_forest_symhull_edge_weight[unfolded minimum_spanning_forest_def]
  unfolding minimum_spanning_tree_def spanning_tree_def spanning_forest_def tree_def forest_def
  optimal_tree_def apply auto
  by (meson connected_graph.maximally_connected_impl_connected forest.axioms(2) optimal_forest_def spanning_forest_def vE valid_graph.connected_impl_maximally_connected valid_graph.subgraph_impl_connected valid_graph.valid_subgraph valid_graph_symhull)

lemma (in finite_weighted_graph) spanning_tree_impl_connected:
  assumes "spanning_tree F G"
  shows "connected_graph G"
  using assms spanning_tree_def subgraph_impl_connected tree_def by blast

lemma (in finite_weighted_graph) minimum_spanning_tree_symhull:
  assumes "\<And>v w.(v,w,v) \<notin> E"
  assumes "minimum_spanning_tree F G"
  shows "minimum_spanning_tree F \<lparr>nodes=V, edges = symhull E\<rparr>"
  using assms unfolding minimum_spanning_tree_def minimum_spanning_forest_def
  by (metis connected_graph.maximally_connected_impl_connected minimum_spanning_forest_def
      minimum_spanning_forest_symhull optimal_forest_def optimal_tree_def spanning_forest_def
      spanning_tree_def sum_of_parts tree_def valid_graph.connected_impl_maximally_connected
      subgraph_impl_connected valid_graph_axioms valid_graph_symhull)


subsection \<open>Matroid Interpretation\<close>

context finite_weighted_graph \<comment> \<open>first usage in the AFP\<close>
begin \<comment> \<open>@{class weight} might be too special, and @{thm valid_graph_axioms} unneeded\<close>

interpretation m?: weighted_matroid E subforest "\<lambda>(_,w,_). w"
  by (simp add: s.weighted_matroid_axioms)

end

context Kruskal_interface
begin
lemmas k0 = kruskal0_refine minWeightBasis_refine
lemma k0_spec: "kruskal0 \<le> SPEC MSF"
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
  have "SPEC (\<lambda>E'. minimum_spanning_tree (ind E') G) \<le> SPEC (\<lambda>E'. minimum_spanning_tree (ind E') \<lparr>nodes=V, edges = symhull E\<rparr>)"
    using minimum_spanning_tree_symhull no_loops by force
  with SPEC_trans kruskal0_MST show ?thesis
    by blast
qed

sublocale symhull: valid_unMultigraph \<open>ind (symhull E)\<close>
  by (simp add: no_loops valid_unMultigraph_symhull)

term \<open>symhull.is_Eulerian_trail\<close>
definition "phase2 = undefined"

end

subsection \<open>Hamiltonian Circuits\<close>

term \<open>valid_unMultigraph.is_Eulerian_trail\<close>

definition (in valid_graph) is_simple_path :: \<open>_ \<Rightarrow> (_,_) path \<Rightarrow> _ \<Rightarrow> bool\<close> where
  \<open>is_simple_path v ps v' \<longleftrightarrow> is_path v ps v' \<and> distinct (map fst ps)\<close>
find_theorems "int_vertices"

fun (in valid_graph) is_trace :: \<open>('v,'w) path \<Rightarrow> bool\<close>where \<comment> \<open>non-standard definition. Also not thoroughly thought through.\<close>
  \<open>is_trace [] \<longleftrightarrow> V={} \<or> card V = 1\<close> |
  \<open>is_trace ps \<longleftrightarrow> insert (snd(snd(last ps))) (int_vertices ps) = V\<close>

lemma (in valid_graph) is_trace_snoc:
  "is_trace (ps @ [p]) \<longleftrightarrow> insert (snd(snd p)) (int_vertices (ps@[p])) = V"
  by (metis (no_types, lifting) append_is_Nil_conv is_trace.elims(2) is_trace.elims(3) last_snoc not_Cons_self2)

definition (in valid_graph) is_hamiltonian_path where \<comment> \<open>or "simple trace"\<close>
  \<open>is_hamiltonian_path v ps v' \<longleftrightarrow> is_trace ps \<and> is_simple_path v ps v'\<close>

fun (in valid_graph) is_hamiltonian :: \<open>('v,'w) path \<Rightarrow> bool\<close> where \<comment> \<open>to-do: unconventional intermediate definition, only for experimentation\<close>
  \<open>is_hamiltonian [] \<longleftrightarrow> V={} \<or> card V = 1\<close> |
  \<open>is_hamiltonian ps \<longleftrightarrow> int_vertices ps = V\<close>

definition (in valid_graph) is_hamiltonian_circuit where
  \<open>is_hamiltonian_circuit v ps \<longleftrightarrow> is_hamiltonian ps \<and> is_simple_path v ps v\<close>

lemma (in valid_graph) is_hamiltonian_iff: "is_hamiltonian_path v ps v \<longleftrightarrow> is_hamiltonian_circuit v ps"
  apply (cases ps rule: rev_cases)
   apply (simp_all add: is_hamiltonian_path_def is_hamiltonian_circuit_def)
proof auto
  fix ys :: "('v \<times> 'w \<times> 'v) list" and a :: 'v and aa :: 'w and b :: 'v
  assume a1: "is_simple_path v (ys @ [(a, aa, b)]) v"
  assume a2: "ps = ys @ [(a, aa, b)]"
  assume a3: "is_trace (ys @ [(a, aa, b)])"
  have f4: "is_path b ps b"
    using a2 a1 by (metis (no_types) is_path.simps(1) is_path_split' is_simple_path_def)
  have "is_trace ps"
    using a3 a2 by meson
  then have f5: "insert (snd (snd (last ps))) (int_vertices ps) = V \<or> ps = []"
    using f4 is_path.elims(2) is_trace.simps(2) by blast
  have f6: "\<forall>v ps va. ((ps = [] \<or> is_hamiltonian ps) \<or> int_vertices ps \<noteq> V) \<or> \<not> is_path va ps v"
    using is_hamiltonian.simps(2) is_path.elims(2) by blast
  have "ps = [] \<longrightarrow> is_hamiltonian ps"
    using a2 by force
  then have "is_hamiltonian ps"
    using f6 f5 f4 by (metis fst_conv insertCI insert_absorb int_vertices_simps(2) is_path.elims(2) valid_graph.path_end valid_graph_axioms)
  then show "is_hamiltonian (ys @ [(a, aa, b)])"
    using a2 by meson
qed (metis (no_types, lifting) E_validD(2) Nil_is_append_conv insert_absorb is_hamiltonian.elims(2)
      is_path_split' is_simple_path_def last_snoc not_Cons_self2 snd_conv
      valid_graph.is_trace.elims(3) valid_graph_axioms)


term "valid_graph.is_path"
find_theorems \<open>valid_graph.is_path\<close>
find_theorems valid_unMultigraph.connected

text \<open>Reuse @{const kon_graph}, but interpreted, differently: Between to-do and to-do, there are
  four edges, two of which have the same label.\<close>

definition \<open>kon_path = [(a,ab1,b),(b,bd1,d),(d,cd1,c)]\<close>

lemma is_simple_path_kon_path: \<open>kon_graph.is_simple_path a kon_path c\<close>
  unfolding kon_graph.is_simple_path_def by (simp add: kon_path_def) (simp add: kon_graph_def)

lemma is_hamiltonian_path_kon_path: \<open>kon_graph.is_hamiltonian_path a kon_path c\<close>
  apply (simp add: kon_graph.is_hamiltonian_path_def is_simple_path_kon_path)
  apply (simp add: kon_path_def)
  apply eval
  done

definition \<open>kon_circuit = kon_path @ [(c,ac2,a)]\<close>

lemma is_simple_path_kon_circuit: \<open>kon_graph.is_simple_path a kon_circuit a\<close>
  unfolding kon_graph.is_simple_path_def by (simp add: kon_circuit_def kon_path_def) (simp add: kon_graph_def)

section \<open>Generating Example Input\<close>

subsection \<open>Manhattan Distance\<close>

text \<open>1d-coordinates:\<close>

lemma manhattan: "nat\<bar>c-a\<bar> \<le> nat\<bar>b-a\<bar> + nat\<bar>c-b\<bar>" for a b c :: int
  by (simp add: nat_le_iff)

subsection \<open>Euclidean Distance, Rounded Up\<close>
  \<comment> \<open>attempt only if too much time at the end\<close>

section \<open>Junk\<close>

context valid_graph begin
context assumes
  finE: "finite E"
begin

definition dg where "dg v R = card {(w,v'). (v,w,v')\<in>R} + card {(v',w).(v',w,v)\<in>R}"

lemma assumes "finite R'" "R \<subseteq> R'" shows dg_mono: "dg v R \<le> dg v R'"
proof -
  from assms(1) have "finite {(w,v').(v,w,v')\<in>R'}" (is "finite ?A")
  proof -
    from \<open>finite R'\<close> have "finite ((fst o snd) ` R')" "finite ((snd o snd) ` R')"
      by blast+
    then have f: "finite {(w,v'). w \<in> (fst o snd) ` R' \<and> v' \<in> ((snd o snd) ` R')}"
      by simp
    have "?A = {(w,v'). (v,w,v')\<in>R' \<and> w \<in> (fst o snd) ` R' \<and> v' \<in> ((snd o snd) ` R')}"
      by (auto simp: rev_image_eqI)
    also have "\<dots> \<subseteq> {(w,v'). w \<in> (fst o snd) ` R' \<and> v' \<in> ((snd o snd) ` R')}"
      by blast
    finally show ?thesis
      using f finite_subset by blast
  qed
  with assms(2) have l: "card {(w,v').(v,w,v')\<in>R} \<le> card {(w,v').(v,w,v')\<in>R'}"
    by (smt Collect_mono_iff card_mono case_prodE case_prodI2 subsetD)
  from assms(1) have "finite {(v',w).(v',w,v)\<in>R'}" (is "finite ?B")
  proof -
    from \<open>finite R'\<close> have "finite (fst ` R')" "finite ((fst o snd) ` R')"
      by blast+
    then have f: "finite {(w,v'). w \<in> fst ` R' \<and> v' \<in> ((fst o snd) ` R')}"
      by simp
    have "?B = {(v',w). (v',w,v)\<in>R' \<and> v' \<in> fst ` R' \<and> w \<in> ((fst o snd) ` R')}"
      by (auto simp: rev_image_eqI)
    also have "\<dots> \<subseteq> {(v',w). v' \<in> fst ` R' \<and> w \<in> ((fst o snd) ` R')}"
      by blast
    finally show ?thesis
      using f finite_subset by blast
  qed
  with assms(2) have r: "card {(v',w).(v',w,v)\<in>R} \<le> card {(v',w).(v',w,v)\<in>R'}"
    by (smt Collect_mono_iff card_mono case_prodD case_prodI2 subsetD)
  from l r show ?thesis
    by (simp add: dg_def)
qed

lemma "indep_system E (\<lambda>E'. E'\<subseteq>E \<and> (\<forall>v\<in>V. dg v E' \<le> 1))"
  apply standard
     apply (simp add: finE)
    apply blast
   apply (rule exI[of _ "{}"])
   apply (simp add: dg_def)
  apply auto
  by (meson dg_mono finE finite_subset le_trans)

end
end

text \<open>dummy citation: @{cite lawler}.\<close>

end

section \<open>Specification\<close>
theory Specification
  imports
    Koenigsberg_Friendship.KoenigsbergBridge
    Kruskal.Graph_Definition_Impl
    "HOL-ex.Sketch_and_Explore"
begin hide_const a b c d

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
corollary supergraph_symhull: "subgraph G (G\<lparr>edges := symhull (edges G)\<rparr>)"
  by (simp add: subgraph_def subset_eq_symhull)

lemma (in valid_graph) valid_graph_symhull: "valid_graph \<lparr>nodes = V, edges = symhull E\<rparr>"
  apply unfold_locales apply auto using E_valid by (auto simp: symhull_def)

lemma (in valid_graph) valid_unMultigraph_symhull:
  assumes no_id[simp]:"\<And>v w.(v,w,v) \<notin> E"
  shows "valid_unMultigraph (G\<lparr>edges := symhull E\<rparr>)"
  apply unfold_locales
     apply (auto simp: symhull_def)
  using E_validD by blast+

lemma (in valid_graph) symhull_hull:
  assumes no_id:"\<And>v w.(v,w,v) \<notin> E"
  shows "symhull E = (\<lambda>E'. valid_unMultigraph (G\<lparr>edges := E'\<rparr>)) hull E"
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
  "spanning_forest F G \<Longrightarrow> spanning_forest F (G\<lparr>edges := symhull (edges G)\<rparr>)"
  unfolding spanning_forest_def
  using maximally_connected_symhull subgraph_trans supergraph_symhull by blast

lemma infinite_edge_weight: "infinite (edges G) \<Longrightarrow> edge_weight G = 0"
  by (simp add: edge_weight_def)

find_theorems name: "SpanningForest"
thm "indep_system.basis_def"
thm "spanning_forest_def"
thm fromlist.spanning_forest_eq

thm indep_system.basis_in_supI

section \<open>Matroid Interpretation\<close>

context finite_weighted_graph \<comment> \<open>first usage in the AFP\<close>
begin \<comment> \<open>@{class weight} might be too special, and @{thm valid_graph_axioms} unneeded\<close>

interpretation m?: weighted_matroid E subforest "\<lambda>(_,w,_). w"
  by (simp add: s.weighted_matroid_axioms)

lemma a: "finite_weighted_graph\<lparr>nodes = V, edges = symhull E\<rparr>"
  using finite_weighted_graph_axioms finite_weighted_graph_symhull_iff by blast

end

abbreviation "mirror_edge u w v G \<equiv> add_edge v w u (delete_edge u w v G)"

lemma mirror_single_edge_weight:
  assumes "(u,w,v) \<in> E" "(v,w,u) \<notin> E"
  shows "edge_weight (mirror_edge u w v \<lparr>nodes=V, edges=E\<rparr>) = edge_weight \<lparr>nodes=V', edges=E\<rparr>"
  using assms unfolding edge_weight_def apply simp
  by (smt Diff_idemp Diff_insert0 Diff_insert2 finite_insert fst_conv insertCI insert_Diff snd_conv sum.infinite sum.insert_remove)

lemma forest_no_dups: "forest F \<Longrightarrow> (u,w,v) \<in> edges F \<Longrightarrow> (v,w,u) \<notin> edges F"
  unfolding forest_def forest_axioms_def
proof auto
  assume a1: "\<forall>x\<in>edges F. case x of (a, w, b) \<Rightarrow> \<forall>p. \<not> is_path_undir (delete_edge a w b F) a p b"
  assume a2: "(v, w, u) \<in> edges F"
  assume a3: "valid_graph F"
  assume a4: "(u, w, v) \<in> edges F"
  have "\<forall>ps. \<not> is_path_undir (delete_edge v w u F) v ps u"
    using a2 a1 by fastforce
  then show False
    using a4 a3 a2 by (metis (no_types) delete_edge_valid edges_delete_edge insert_Diff insert_iff nodes_delete_edge prod.simps(1) valid_graph.E_validD(2) valid_graph.add_delete_edge valid_graph.add_edge_is_connected(2) valid_graph.is_path_undir_simps(1))
qed
corollary forest_no_loops: "forest F \<Longrightarrow> (u,w,u) \<notin> edges F"
  by (meson forest_no_dups)

lemma (in valid_graph) delete_mirrored[simp]:
  "u\<in>V \<Longrightarrow> v\<in>V \<Longrightarrow> delete_edge v w u (mirror_edge u w v G) = delete_edge v w u (delete_edge u w v G)"
  by (simp add: insert_absorb)

lemma (in valid_graph) is_path_undir_mirror_single_iff:
  assumes \<open>(u,w,v) \<in> E\<close>
  shows "(v1,w',v2)\<in>edges (mirror_edge u w v G) \<or> (v2,w',v1)\<in>edges (mirror_edge u w v G)
    \<longleftrightarrow> (v1,w',v2)\<in>edges G \<or> (v2,w',v1)\<in>edges G"
  using assms by auto

lemma (in valid_graph) [simp]:
  assumes \<open>(u,w,v)\<in>E\<close>
  shows "nodes_connected (mirror_edge u w v G) a b \<longleftrightarrow> nodes_connected G a b"
proof -
  assume e: "(u, w, v) \<in> E"
  have "nodes_connected G a b" if "is_path_undir (mirror_edge u w v G) a p b" for p
    using that
  proof (induction \<open>mirror_edge u w v G\<close> a p b rule: is_path_undir.induct)
    case (1 v v')
    then show ?case
      by (metis e insert_absorb is_path_undir.simps(1) nodes_add_edge nodes_delete_edge valid_graph.E_validD(1) valid_graph.E_validD(2) valid_graph_axioms)
  next
    case (2 v v1 w' v2 p v')
    then show ?case (*
    proof (cases "=")
    then have \<open>nodes_connected G v2 v'\<close> and \<open>(v1, w, v2) \<in> edges (mirror_edge u w v G)\<close>
      apply simp sledgehamme
    then show ?case sorry
  qed
  next
    case (Cons a p)
    then show ?case
    proof (cases "a = (u,w,v)")
      case True
      then have "(v,w,u) \<in> edges (mirror_edge u w v G)"
        by auto
      then show ?thesis
    next
      case False
      then show ?thesis sorry
    qed
  qed
  moreover have "nodes_connected (mirror_edge u w v G) a b"
    if "(u, w, v) \<in> E"
      and "is_path_undir G a p b"
    for p :: "('v \<times> 'w \<times> 'v) list"
    using that sorry
  ultimately show ?thesis
    using assms by auto
qed*)
      oops

lemma (in forest) mirror_single_forest:
  assumes "(u,w,v) \<in> E"
  shows "forest (mirror_edge u w v G)"
  find_theorems intro
proof unfold_locales
  show "fst ` edges (mirror_edge u w v G) \<subseteq> nodes (mirror_edge u w v G)"
    using E_valid(1) image_eqI by auto
  show "snd ` snd ` edges (mirror_edge u w v G) \<subseteq> nodes (mirror_edge u w v G)"
    using E_valid(2) by auto
  have "u\<in>V" "v\<in>V" if \<open>(u,w,v) \<in> E\<close> for u v w
    using that E_validD by blast+
  then show "\<forall>(a, wa, b) \<in>edges (mirror_edge u w v G). \<not>nodes_connected (delete_edge a wa b (mirror_edge u w v G)) a b"
    apply simp
    sorry
qed

lemma (in finite_weighted_graph (*?*)) spanning_forest_mirror_single:
  assumes "spanning_forest \<lparr>nodes=V, edges=F\<rparr> G" and "(u,w,v)\<in>F"
  shows "spanning_forest \<lparr>nodes=V, edges=insert (v,w,u) (F-{(u,w,v)})\<rparr> G"
  using assms apply (simp add: spanning_forest_def)
  apply auto
  proof -
  show "forest (ind (insert (v, w, u) (F - {(u, w, v)})))"
    if "(u, w, v) \<in> F"
      and "forest (ind F)"
      and "maximally_connected (ind F) G"
      and "subgraph (ind F) G"
    using that sorry
  show "maximally_connected (ind (insert (v, w, u) (F - {(u, w, v)}))) G"
    if "(u, w, v) \<in> F"
      and "forest (ind F)"
      and "maximally_connected (ind F) G"
      and "subgraph (ind F) G"
    using that sorry
  show "subgraph (ind (insert (v, w, u) (F - {(u, w, v)}))) G"
    if "(u, w, v) \<in> F"
      and "forest (ind F)"
      and "maximally_connected (ind F) G"
      and "subgraph (ind F) G"
    using that sorry
qed

lemma spanning_forest_symhull_preimage:
  assumes "finite_weighted_graph \<lparr>nodes=V, edges=E\<rparr>"
  assumes "spanning_forest \<lparr>nodes=V, edges=F\<rparr> \<lparr>nodes=V, edges=symhull E\<rparr>"
  shows "\<exists>F'. spanning_forest \<lparr>nodes=V, edges=F'\<rparr> \<lparr>nodes=V, edges=E\<rparr>
    \<and> edge_weight \<lparr>nodes=V, edges=F'\<rparr> = edge_weight \<lparr>nodes=V, edges=F\<rparr>"
  using assms
proof (induction "F - E" arbitrary: F rule: infinite_finite_induct)
  case infinite
  have "finite F"
    by (metis finite_graph.finite_E finite_weighted_graph.a finite_weighted_graph.axioms graph.select_convs(2) infinite.prems(1) infinite.prems(2) infinite_super spanning_forest_def subgraph_def)
  with infinite show ?case
    by blast
next
  case empty
  then have "subgraph \<lparr>nodes=V, edges=F\<rparr> \<lparr>nodes=V, edges=E\<rparr>"
    using subgraph_def by fastforce
  then have "spanning_forest \<lparr>nodes=V, edges=F\<rparr> \<lparr>nodes=V, edges=E\<rparr>"
    by (meson empty.prems(2) maximally_connected_antimono spanning_forest_def subset_eq_symhull)
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
  then have "(v,w,u)\<in>E" and **: "x\<notin>E" and ***: "x\<in>F"
      apply (simp add: f1)
    apply (simp add: f1 x)
    using insert.hyps(4) by auto
  with \<open>x \<in> F\<close> have "(v,w,u) \<notin> F"
    using forest_no_dups x local.insert(6) spanning_forest_def by fastforce
  then have *: "I = edges (mirror_edge u w v \<lparr>nodes=V, edges=F\<rparr>) - E"
    by (smt DiffD2 Diff_insert_absorb Diff_subset \<open>(v, w, u) \<in> E\<close> edges_add_edge edges_delete_edge graph.select_convs(2) in_mono insert.hyps(2) insert.hyps(4) insert_Diff insert_Diff_if set_minus_singleton_eq x)
  have "forest \<lparr>nodes=V, edges=F\<rparr>"
    using insert.prems(2) spanning_forest_def by blast
  from \<open>spanning_forest \<lparr>nodes = V, edges = F\<rparr> \<lparr>nodes = V, edges = symhull E\<rparr>\<close>
  have "spanning_forest \<lparr>nodes = V, edges = F - {x} \<union> {(v, w, u)}\<rparr> \<lparr>nodes = V, edges = symhull E\<rparr>"
    apply (simp add: spanning_forest_def)
    apply auto sorry
  from "insert.hyps"(3)[OF *] obtain F' where
    "spanning_forest \<lparr>nodes = V, edges = F'\<rparr> \<lparr>nodes = V, edges = E\<rparr> \<and>
     edge_weight \<lparr>nodes = V, edges = F'\<rparr> = edge_weight (mirror_edge u w v \<lparr>nodes = V, edges = F\<rparr>)"
    apply simp sorry
  then show ?case apply(intro exI[where x="F'"])
     apply safe
      apply simp+ unfolding x apply (rule mirror_single_edge_weight)
    using "***" x apply blast
    using \<open>(v, w, u) \<notin> F\<close> by blast
qed

lemma edge_weight_same: "edge_weight \<lparr>nodes=V,edges=E\<rparr> = edge_weight \<lparr>nodes=V',edges=E\<rparr>"
  unfolding edge_weight_def by fastforce

lemma optimal_forest_mono:
  assumes "subgraph G G'"
  assumes "optimal_forest (G\<lparr>edges:=F\<rparr>) G" and "optimal_forest (G'\<lparr>edges:=F'\<rparr>) G'"
  shows "edge_weight (G\<lparr>edges:=F\<rparr>) \<le> edge_weight (G'\<lparr>edges:=F'\<rparr>)"
  oops

lemma optimal_forest_symhull:
  "optimal_forest F G \<Longrightarrow> optimal_forest F (G\<lparr>edges := symhull E\<rparr>)"
  unfolding optimal_forest_def oops

context Kruskal_Impl
begin

lemmas k0 = kruskal0_refine minWeightBasis_refine
lemma k0_spec: "kruskal0 \<le> SPEC MSF" using k0 unfolding nres_rel_def by auto
end
thm "Kruskal_Impl.k0_spec"

text \<open>Citation test: @{cite lawler}.\<close>

subsection \<open>Manhattan Distance\<close>

text \<open>1d-coordinates:\<close>

lemma "nat\<bar>c-a\<bar> \<le> nat\<bar>b-a\<bar> + nat\<bar>c-b\<bar>" for a :: int
  by (simp add: nat_le_iff)

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

end

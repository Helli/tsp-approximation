section \<open>Specification\<close>
theory Specification
  imports
    Koenigsberg_Friendship.KoenigsbergBridge
    Kruskal.Graph_Definition_Impl
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

lemma matroid_forest:
  (* V=fst ` E \<union> (snd \<circ> snd) ` E*)
  assumes "finite E" \<comment> \<open>need a proper locale with the correct assumptions\<close>
  shows "matroid E (\<lambda>E'. forest \<lparr>nodes = V, edges = E'\<rparr> \<and>
     subgraph \<lparr>nodes = V, edges = E'\<rparr> \<lparr>nodes = V, edges = E\<rparr>)" (is "matroid E ?forest")
\<comment> \<open>should be derived from \<^session>\<open>Kruskal\<close>, but needs refactoring there (maybe make
    \<^locale>\<open>weighted_matroid\<close> an import of \<^locale>\<open>Kruskal_interface\<close>?\<close>
proof
  fix X
  assume "?forest X"
  then show "X \<subseteq> E"
    by (simp add: subgraph_def)
next
  have "?forest {}"
    unfolding subgraph_def apply auto apply unfold_locales apply auto done
  then show "\<exists>X. ?forest X"
    by blast
next
  fix X Y
  assume "?forest X" "Y \<subseteq> X"
  then show "?forest Y"
    apply auto
     apply (simp add: forest.subgraph_forest subgraph_def)
    by (metis graph.select_convs(1) graph.select_convs(2) subgraph_def subset_trans)
next
  fix X Y
  assume "?forest X" "?forest Y" "card X = Suc (card Y)"
  then show "\<exists>x\<in>X - Y. ?forest (insert x Y)"
    sorry
qed (simp add: assms)

context weight begin subclass ordered_comm_monoid_add.. end
\<comment> \<open>could replace @{class ordered_ab_semigroup_add} and @{class comm_monoid_add} in @{class weight}'s def\<close>
thm class.weight_def thm class.ordered_comm_monoid_add_def

context finite_weighted_graph \<comment> \<open>first usage in the AFP\<close>
begin \<comment> \<open>@{class weight} might be too special, and @{thm valid_graph_axioms} unneeded\<close>

interpretation m: weighted_matroid E "\<lambda>E'. forest \<lparr>nodes = V, edges = E'\<rparr> \<and> subgraph \<lparr>nodes = V,
  edges = E'\<rparr> \<lparr>nodes = V, edges = E\<rparr>" "\<lambda>(_,w,_). w"
  by (simp add: finite_E matroid_forest weighted_matroid_def)

lemma spanning_forest_symhull_preimage:
  assumes "finite E" "spanning_forest F \<lparr>nodes=V, edges=symhull E\<rparr>"
  shows "\<exists>F'. spanning_forest F' \<lparr>nodes=V, edges=E\<rparr> \<and> edge_weight F' = edge_weight F"
  using assms
proof (induction E set: finite)
  case empty
  show ?case
    oops

lemma optimal_forest_symhull:
  "optimal_forest F G \<Longrightarrow> optimal_forest F (G\<lparr>edges := symhull (edges G)\<rparr>)"
  unfolding optimal_forest_def
  apply auto
  apply (simp add: symhull_def)
  oops

end

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

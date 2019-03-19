section \<open>Specification\<close>
theory Specification
  imports
    Koenigsberg_Friendship.KoenigsbergBridge
    Kruskal.Graph_Definition_Aux
begin hide_const a b c d
hide_const "connected"

subsection \<open>Adapting Definitions\<close>

text \<open>see @{const is_path_undir}\<close>
fun is_path_undir' :: "('v, 'w) graph \<Rightarrow> 'v \<Rightarrow> ('v,'w) path \<Rightarrow> 'v \<Rightarrow> bool" where
    "is_path_undir' G v [] v' \<longleftrightarrow> v=v' \<and> v'\<in>nodes G" |
    "is_path_undir' G v ((v1,w,v2)#p) v'
       \<longleftrightarrow> v=v1 \<and> ((v1,w,v2)\<in>edges G
         \<and> (v2,w,v1)\<in>edges G \<comment> \<open>not yet sure if this is good\<close>
       ) \<and> is_path_undir' G v2 p v'"

abbreviation "nodes_connected' G a b \<equiv> \<exists>p. is_path_undir' G a p b"

subsubsection \<open>Undirected Hull\<close> \<comment> \<open>or rather: symmetric hull\<close>

definition symhull where
  "symhull E = {(v1,w,v2) | v1 w v2. (v1,w,v2) \<in> E \<or> (v2,w,v1) \<in> E}"

context valid_graph
begin

lemma valid_unMultigraph_symhull:
  assumes no_id[simp]:"\<And>v w.(v,w,v) \<notin> E"
  shows "valid_unMultigraph (G\<lparr>edges := symhull E\<rparr>)"
  apply unfold_locales
     apply (auto simp: symhull_def)
  using E_validD by blast+

lemma symhull_altdef:
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

end

lemma symhull_supset_eq: "symhull E \<supseteq> E"
  by (auto simp: symhull_def)

lemma maximally_connected_symhull:
  shows "maximally_connected H G \<Longrightarrow> maximally_connected (H\<lparr>edges:=symhull (edges H)\<rparr>) G"
  apply (simp add: maximally_connected_def) apply auto
  oops

text \<open>Citation test: @{cite lawler}.\<close>

subsection \<open>Manhattan Distance\<close>

text \<open>1d-coordinates:\<close>

lemma "nat\<bar>c-a\<bar> \<le> nat\<bar>b-a\<bar> + nat\<bar>c-b\<bar>" for a :: int
  by (simp add: nat_le_iff)

end

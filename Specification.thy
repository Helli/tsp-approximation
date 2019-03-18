section \<open>Specification\<close>
theory Specification
  imports
    Koenigsberg_Friendship.KoenigsbergBridge
    Kruskal.Graph_Definition_Aux
begin hide_const a b c d

subsection \<open>Adapting Definitions\<close>

fun is_path_undir' :: "('v, 'w) graph \<Rightarrow> 'v \<Rightarrow> ('v,'w) path \<Rightarrow> 'v \<Rightarrow> bool" where
    "is_path_undir' G v [] v' \<longleftrightarrow> v=v' \<and> v'\<in>nodes G" |
    "is_path_undir' G v ((v1,w,v2)#p) v'
       \<longleftrightarrow> v=v1 \<and> ((v1,w,v2)\<in>edges G
         \<and> (v2,w,v1)\<in>edges G \<comment> \<open>not yet sure if this is good\<close>
       ) \<and> is_path_undir' G v2 p v'"

abbreviation "nodes_connected' G a b \<equiv> \<exists>p. is_path_undir' G a p b"

term nodes

(*
definition tour
*) \<comment> \<open>see @{const is_path_undir}\<close>

text \<open>Citation test: @{cite lawler}.\<close>

subsection \<open>Manhattan Distance\<close>

text \<open>1d-coordinates:\<close>

lemma "nat\<bar>c-a\<bar> \<le> nat\<bar>b-a\<bar> + nat\<bar>c-b\<bar>" for a :: int
  by (simp add: nat_le_iff)

end

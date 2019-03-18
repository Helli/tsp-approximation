section \<open>Specification\<close>
theory Specification
  imports
    Koenigsberg_Friendship.KoenigsbergBridge
    Kruskal.Graph_Definition_Aux
begin

hide_const a b c d

term nodes

(*
definition tour
*) \<comment> \<open>see @{const is_path_undir}\<close>

text \<open>Citation test: @{cite lawler}.\<close>

subsection \<open>Manhattan Distance\<close>

text \<open>1d-coordinates:\<close>

lemma "\<bar>c-a\<bar> \<le> \<bar>b-a\<bar> + \<bar>c-b\<bar>" for a :: int
  by simp

end

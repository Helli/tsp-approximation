(*
Title: MoreGraph.thy
Author:Wenda Li, Fabian Hellauer removed valid_unMultigraph's second assumption and dependent results.
*)

theory MoreGraph_alt imports Complex_Main Dijkstra_Shortest_Path.Graph
begin
section \<open>Undirected Multigraph and undirected trails\<close>

locale valid_unMultigraph=valid_graph G for G::"('v,'w) graph"+
              assumes corres[simp]: "(v,w,u') \<in> edges G \<longleftrightarrow> (u',w,v) \<in> edges G"

fun (in valid_unMultigraph) is_trail :: "'v \<Rightarrow> ('v,'w) path \<Rightarrow> 'v \<Rightarrow> bool" where
      "is_trail v [] v' \<longleftrightarrow> v=v' \<and> v'\<in> V" |
      "is_trail v ((v1,w,v2)#ps) v' \<longleftrightarrow> v=v1 \<and> (v1,w,v2)\<in>E \<and> 
                (v1,w,v2)\<notin>set ps \<and>(v2,w,v1)\<notin>set ps \<and> is_trail v2 ps v'"

(*This section mainly includes lemmas related to degrees of nodes, especially when edges and paths 
are removed from an undirected graph*)
section \<open>Degrees and related properties\<close>

definition degree :: "'v \<Rightarrow> ('v,'w) graph \<Rightarrow> nat" where
    "degree v g\<equiv> card({e. e\<in>edges g \<and> fst e=v})"

definition odd_nodes_set :: "('v,'w) graph \<Rightarrow> 'v set" where
    "odd_nodes_set g \<equiv> {v. v\<in>nodes g \<and> odd(degree v g)}"

  (*return the number of nodes with an odd degree in the current valid multigraph*)
definition num_of_odd_nodes :: "('v, 'w) graph \<Rightarrow> nat" where
    "num_of_odd_nodes g\<equiv> card( odd_nodes_set g)"

definition num_of_even_nodes :: "('v, 'w) graph \<Rightarrow> nat" where
    "num_of_even_nodes g\<equiv> card( {v. v\<in>nodes g \<and> even(degree v g)})"

definition del_unEdge where "del_unEdge v e v' g \<equiv> \<lparr>
    nodes = nodes g, edges = edges g - {(v,e,v'),(v',e,v)} \<rparr>"

definition rev_path :: "('v,'w) path \<Rightarrow> ('v,'w) path" where
    "rev_path ps \<equiv> map (\<lambda>(a,b,c).(c,b,a)) (rev ps)"

fun rem_unPath:: "('v,'w) path \<Rightarrow> ('v,'w) graph \<Rightarrow> ('v,'w) graph" where
    "rem_unPath [] g= g"|
    "rem_unPath ((v,w,v')#ps) g= 
        rem_unPath ps (del_unEdge v w v' g)" 
    
lemma del_undirected: "del_unEdge v e v' g = delete_edge v' e v (delete_edge v e v' g)"
  unfolding del_unEdge_def delete_edge_def by auto

lemma delete_edge_sym: "del_unEdge v e v' g = del_unEdge v' e v g" 
  unfolding del_unEdge_def by auto

lemma del_unEdge_valid[simp]: assumes "valid_unMultigraph g" 
    shows "valid_unMultigraph (del_unEdge v e v' g)"
proof -
  interpret valid_unMultigraph g by fact
  show ?thesis 
    unfolding del_unEdge_def
    by unfold_locales (auto dest: E_validD) 
qed

 
lemma set_compre_diff:"{x \<in> A - B. P x}={x \<in> A. P x} - {x \<in> B . P x}" by blast
lemma set_compre_subset: "B \<subseteq> A \<Longrightarrow> {x \<in> B. P x} \<subseteq> {x \<in> A. P x}" by blast 

lemma del_edge_undirected_degree_plus: "finite (edges g) \<Longrightarrow> (v,e,v') \<in> edges g 
    \<Longrightarrow> (v',e,v) \<in> edges g  \<Longrightarrow> degree v (del_unEdge v e v' g) + 1=degree v g" 
proof -
  assume assms: "finite (edges g)" "(v,e,v') \<in> edges g" "(v',e,v) \<in> edges g "
  have "degree v (del_unEdge v e v' g) + 1
          = card ({ea \<in>  edges g - {(v, e, v'), (v', e, v)}. fst ea = v}) + 1"  
    unfolding del_unEdge_def degree_def by simp
  also have "...=card ({ea \<in>  edges g. fst ea = v} - {ea \<in> {(v, e, v'), (v', e, v)}. 
      fst ea = v})+1" 
    by (metis set_compre_diff) 
  also have "...=card ({ea \<in>  edges g. fst ea = v}) - card({ea \<in> {(v, e, v'), (v', e, v)}. 
      fst ea = v})+1" 
    proof -
      have "{(v, e, v'), (v', e, v)} \<subseteq> edges g" using \<open>(v,e,v') \<in> edges g\<close> \<open>(v',e,v) \<in> edges g\<close> 
        by auto
      hence "{ea \<in> {(v, e, v'), (v', e, v)}. fst ea = v} \<subseteq> {ea \<in>  edges g. fst ea = v}" by auto
      moreover have "finite {ea \<in> {(v, e, v'), (v', e, v)}. fst ea = v}" by auto
      ultimately have "card ({ea \<in> edges g. fst ea = v} - {ea \<in> {(v, e, v'), (v', e, v)}. 
          fst ea = v})=card {ea \<in> edges g. fst ea = v} - card {ea \<in> {(v, e, v'), (v', e, v)}.
          fst ea = v}"
        using card_Diff_subset by blast
      thus ?thesis by auto 
    qed
  also have "...=card ({ea \<in>  edges g. fst ea = v})" 
    proof -
      have "{ea \<in> {(v, e, v'), (v', e, v)}. fst ea = v}={(v,e,v')}" by auto
      hence "card {ea \<in> {(v, e, v'), (v', e, v)}. fst ea = v} = 1" by auto
      moreover have "card {ea \<in> edges g. fst ea = v}\<noteq>0" 
        by (metis (lifting, mono_tags) Collect_empty_eq assms(1) assms(2) 
          card_eq_0_iff fst_conv mem_Collect_eq rev_finite_subset subsetI)
      ultimately show ?thesis by arith
    qed
  finally have "degree v (del_unEdge v e v' g) + 1=card ({ea \<in>  edges g. fst ea = v})" .
  thus ?thesis unfolding degree_def .
qed

lemma del_edge_undirected_degree_plus': "finite (edges g) \<Longrightarrow> (v,e,v') \<in> edges g 
    \<Longrightarrow> (v',e,v) \<in> edges g \<Longrightarrow> degree v' (del_unEdge v e v' g) + 1=degree v' g"
  by (metis del_edge_undirected_degree_plus delete_edge_sym) 

lemma del_edge_undirected_degree_minus[simp]: "finite (edges g) \<Longrightarrow> (v,e,v') \<in> edges g 
    \<Longrightarrow> (v',e,v) \<in> edges g \<Longrightarrow> degree v (del_unEdge v e v' g) =degree v g- (1::nat)" 
  using del_edge_undirected_degree_plus by (metis add_diff_cancel_left' add.commute)

lemma del_edge_undirected_degree_minus'[simp]: "finite (edges g) \<Longrightarrow> (v,e,v') \<in> edges g 
    \<Longrightarrow> (v',e,v) \<in> edges g \<Longrightarrow> degree v' (del_unEdge v e v' g) =degree v' g- (1::nat)"
  by (metis del_edge_undirected_degree_minus delete_edge_sym) 


lemma del_unEdge_com: "del_unEdge v w v' (del_unEdge n e n' g)
          = del_unEdge n e n' (del_unEdge v w v' g)" 
  unfolding del_unEdge_def by auto

lemma rem_unPath_com: "rem_unPath ps (del_unEdge v w v' g) 
            = del_unEdge v w v' (rem_unPath ps g)" 
proof (induct ps arbitrary: g)
  case Nil
  thus ?case by (metis rem_unPath.simps(1))
next
  case (Cons a ps')
  thus ?case using del_unEdge_com 
    by (metis prod_cases3 rem_unPath.simps(1) rem_unPath.simps(2))
qed

lemma rem_unPath_valid[intro]: 
  "valid_unMultigraph g \<Longrightarrow> valid_unMultigraph (rem_unPath ps g)"
proof (induct ps )
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  thus ?case 
    proof -
    have "valid_unMultigraph (rem_unPath (x # xs) g) = valid_unMultigraph 
         (del_unEdge (fst x) (fst (snd x)) (snd (snd x)) (rem_unPath xs g))"
      using rem_unPath_com by (metis prod.collapse rem_unPath.simps(2))
    also have "...=valid_unMultigraph (rem_unPath xs g)" 
      by (metis Cons.hyps Cons.prems del_unEdge_valid)
    also have "...=True" 
      using Cons by auto
    finally have "?case=True" .
    thus ?case by simp
    qed
qed 


lemma (in valid_unMultigraph) degree_frame:
    assumes "finite (edges G)"  "x \<notin> {v, v'}" 
    shows "degree x (del_unEdge v w v' G) = degree x G" (is "?L=?R")
proof (cases "(v,w,v') \<in> edges G")
  case True
  have "?L=card({e. e\<in>edges G - {(v,w,v'),(v',w,v)} \<and> fst e=x})" 
    by (simp add:del_unEdge_def degree_def)
  also have "...=card({e. e\<in>edges G \<and> fst e=x}-{e. e\<in>{(v,w,v'),(v',w,v)} \<and> fst e=x})"
    by (metis  set_compre_diff)
  also have "...=card({e. e\<in>edges G \<and> fst e=x})" using \<open>x \<notin> {v, v'}\<close> 
    proof -
      have "x\<noteq>v \<and> x\<noteq> v'" using \<open>x\<notin>{v,v'}\<close>by simp
      hence "{e. e\<in>{(v,w,v'),(v',w,v)} \<and> fst e=x}={}" by auto
      thus ?thesis by (metis Diff_empty)
    qed
  also have "...=?R" by (simp add:degree_def)
  finally show ?thesis .
next
  case False
  moreover hence "(v',w,v)\<notin>E" using corres by auto
  ultimately have "E- {(v,w,v'),(v',w,v)}=E" by blast   
  hence "del_unEdge v w v' G=G" by (auto simp add:del_unEdge_def)
  thus ?thesis by auto
qed

lemma [simp]: "rev_path [] = []" unfolding rev_path_def by simp
lemma rev_path_append[simp]: "rev_path (xs@ys) = (rev_path ys) @ (rev_path xs)" 
  unfolding rev_path_def rev_append by auto
lemma rev_path_double[simp]: "rev_path(rev_path xs)=xs" 
  unfolding rev_path_def by (induct xs,auto)

lemma del_UnEdge_node[simp]: "v\<in>nodes (del_unEdge u e u' G) \<longleftrightarrow> v\<in>nodes G  " 
    by (metis del_unEdge_def select_convs(1))

lemma [intro!]: "finite (edges G) \<Longrightarrow> finite (edges (del_unEdge u e u' G))"
    by (metis del_unEdge_def finite_Diff select_convs(2))

lemma [intro!]: "finite (nodes G) \<Longrightarrow> finite (nodes (del_unEdge u e u' G))"
    by (metis del_unEdge_def select_convs(1))
 
lemma [intro!]: "finite (edges G) \<Longrightarrow> finite (edges (rem_unPath ps G))"
proof (induct ps arbitrary:G)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  hence "finite (edges (rem_unPath (x # xs) G)) = finite (edges (del_unEdge 
          (fst x) (fst (snd x)) (snd (snd x)) (rem_unPath xs G)))" 
    by (metis rem_unPath.simps(2) rem_unPath_com surjective_pairing)
  also have "...=finite (edges (rem_unPath xs G))" 
    using del_unEdge_def  
    by (metis  finite.emptyI finite_Diff2 finite_Diff_insert select_convs(2))
  also have "...=True" using Cons by auto
  finally have "?case = True" .
  thus ?case by simp
qed

lemma del_UnEdge_frame[intro]: 
  "x\<in>edges g \<Longrightarrow> x\<noteq>(v,e,v') \<Longrightarrow>x\<noteq>(v',e,v) \<Longrightarrow> x\<in>edges (del_unEdge v e v' g)"
  unfolding del_unEdge_def by auto

lemma [intro!]: "finite (nodes G) \<Longrightarrow> finite (odd_nodes_set G)"
    by (metis (lifting) mem_Collect_eq odd_nodes_set_def rev_finite_subset subsetI)

lemma [simp]: "nodes (del_unEdge u e u' G)=nodes G" 
    by (metis del_unEdge_def select_convs(1))

lemma [simp]: "nodes (rem_unPath ps G) = nodes G" 
proof (induct ps)
  case Nil
  show ?case by simp
next 
  case (Cons x xs)
  have "nodes (rem_unPath (x # xs) G)=nodes (del_unEdge 
        (fst x) (fst (snd x)) (snd (snd x)) (rem_unPath xs G))" 
    by (metis rem_unPath.simps(2) rem_unPath_com surjective_pairing)
  also have "...=nodes (rem_unPath xs G)" by auto
  also have "...=nodes G" using Cons by auto
  finally show ?case .
qed

lemma [intro!]: "finite (nodes G) \<Longrightarrow> finite (nodes (rem_unPath ps G))" by auto

lemma in_set_rev_path[simp]: "(v',w,v )\<in>set (rev_path ps) \<longleftrightarrow> (v,w,v')\<in>set ps " 
proof (induct ps)
  case Nil
  thus ?case unfolding rev_path_def by auto
next
  case (Cons x xs)
  obtain x1 x2 x3 where x:"x=(x1,x2,x3)" by (metis prod_cases3)
  have "set (rev_path (x # xs))=set ((rev_path xs)@[(x3,x2,x1)])" 
    unfolding rev_path_def 
    using x by auto
  also have "...=set (rev_path xs) \<union> {(x3,x2,x1)}" by auto
  finally have "set (rev_path (x # xs)) =set (rev_path xs) \<union> {(x3,x2,x1)}" .
  moreover have "set (x#xs)= set xs \<union> {(x1,x2,x3)}" 
    by (metis List.set_simps(2) insert_is_Un sup_commute x)
  ultimately show ?case using Cons by auto
qed

lemma rem_unPath_edges: 
    "edges(rem_unPath ps G) = edges G - (set ps \<union> set (rev_path ps))" 
proof (induct ps)
  case Nil
  show ?case unfolding rev_path_def by auto
next
  case (Cons x xs)
  obtain x1 x2 x3 where x: "x=(x1,x2,x3)" by (metis prod_cases3)
  hence "edges(rem_unPath (x#xs) G)= edges(del_unEdge x1 x2 x3 (rem_unPath xs G))"
    by (metis rem_unPath.simps(2) rem_unPath_com)
  also have "...=edges(rem_unPath xs G)-{(x1,x2,x3),(x3,x2,x1)}"
    by (metis del_unEdge_def select_convs(2))
  also have "...= edges G - (set xs \<union> set (rev_path xs))-{(x1,x2,x3),(x3,x2,x1)}"
    by (metis Cons.hyps)
  also have "...=edges G - (set (x#xs) \<union> set (rev_path (x#xs)))"  
    proof -
      have "set (rev_path xs) \<union> {(x3,x2,x1)}=set ((rev_path xs)@[(x3,x2,x1)])" 
        by (metis List.set_simps(2) empty_set set_append)
      also have "...=set (rev_path (x#xs))" unfolding rev_path_def using  x by auto
      finally have "set (rev_path xs) \<union> {(x3,x2,x1)}=set (rev_path (x#xs))" .
      moreover have "set xs \<union> {(x1,x2,x3)}=set (x#xs)" 
        by (metis List.set_simps(2) insert_is_Un sup_commute x)
      moreover have "edges G - (set xs \<union> set (rev_path xs))-{(x1,x2,x3),(x3,x2,x1)} =
                      edges G - ((set xs \<union> {(x1,x2,x3)}) \<union> (set (rev_path xs) \<union> {(x3,x2,x1)}))" 
        by auto 
      ultimately show ?thesis by auto
    qed
  finally show ?case .
qed  

lemma rem_unPath_graph [simp]: 
    "rem_unPath (rev_path ps) G=rem_unPath ps G"
proof -
  have "nodes(rem_unPath (rev_path ps) G)=nodes(rem_unPath ps G)" 
    by auto
  moreover have "edges(rem_unPath (rev_path ps) G)=edges(rem_unPath ps G)"  
    proof -
      have "set (rev_path ps) \<union> set (rev_path (rev_path ps)) = set ps \<union>  set (rev_path ps) " 
        by auto
      thus ?thesis by (metis rem_unPath_edges)
    qed
  ultimately show ?thesis by auto
qed 

lemma distinct_rev_path[simp]: "distinct (rev_path ps) \<longleftrightarrow>distinct ps" 
proof (induct ps)
  case Nil
  show ?case by auto
next 
  case (Cons x xs)
  obtain x1 x2 x3 where x: "x=(x1,x2,x3)" by (metis prod_cases3)
  hence "distinct (rev_path (x # xs))=distinct ((rev_path xs)@[(x3,x2,x1)])" 
    unfolding rev_path_def by auto
  also have "...= (distinct (rev_path xs) \<and> (x3,x2,x1)\<notin>set (rev_path xs))" 
    by (metis distinct.simps(2) distinct1_rotate rotate1.simps(2))
  also have "...=distinct (x#xs)" 
    by (metis Cons.hyps distinct.simps(2) in_set_rev_path x)
  finally have "distinct (rev_path (x # xs))=distinct (x#xs)" .
  thus ?case .
qed


lemma (in valid_unMultigraph) is_path_rev: "is_path v' (rev_path ps) v \<longleftrightarrow> is_path v ps v'" 
proof (induct ps arbitrary: v)
  case Nil
  show ?case by auto
next
  case (Cons x xs)
  obtain x1 x2 x3 where x: "x=(x1,x2,x3)" by (metis prod_cases3)
  hence "is_path v' (rev_path (x # xs)) v=is_path v' ((rev_path xs) @[(x3,x2,x1)]) v" 
    unfolding rev_path_def by auto
  also have "...=(is_path v' (rev_path xs) x3 \<and> (x3,x2,x1)\<in>E \<and> is_path x1 [] v)" by auto
  also have "...=(is_path x3 xs v' \<and> (x3,x2,x1)\<in>E \<and> is_path x1 [] v)" using Cons.hyps by auto
  also have "...=is_path v (x#xs) v'" 
    by (metis corres is_path.simps(1) is_path.simps(2) is_path_memb x)
  finally have "is_path v' (rev_path (x # xs)) v=is_path v (x#xs) v'" .
  thus ?case .
qed


lemma (in valid_unMultigraph) singleton_distinct_path [intro]:
   "(v,w,v')\<in>E \<Longrightarrow> is_trail v [(v,w,v')] v'" 
   by (metis E_validD(2) all_not_in_conv is_trail.simps set_empty) 

lemma (in valid_unMultigraph) is_trail_intro[intro]:
  "is_trail v' ps v \<Longrightarrow> is_path v' ps v" by (induct ps arbitrary:v',auto)   

lemma (in valid_unMultigraph) is_trail_split:
      "is_trail v (p1@p2) v' \<Longrightarrow> (\<exists>u. is_trail v p1 u \<and> is_trail u p2 v')"
apply (induct p1 arbitrary: v,auto) 
apply (metis is_trail_intro is_path_memb)
done

lemma (in valid_unMultigraph) is_trail_split':"is_trail v (p1@(u,w,u')#p2) v' 
    \<Longrightarrow> is_trail v p1 u \<and> (u,w,u')\<in>E \<and> is_trail u' p2 v'"
  by (metis is_trail.simps(2) is_trail_split)

lemma (in valid_unMultigraph) distinct_elim[simp]:
  assumes "is_trail v ((v1,w,v2)#ps) v'" 
  shows "(v1,w,v2)\<in>edges(rem_unPath ps G) \<longleftrightarrow> (v1,w,v2)\<in>E" 
proof 
  assume "(v1, w, v2) \<in> edges (rem_unPath ps G)"
  thus "(v1, w, v2) \<in> E" by (metis assms is_trail.simps(2))
next
  assume "(v1, w, v2) \<in> E"
  have "(v1,w,v2)\<notin>set ps \<and> (v2,w,v1)\<notin>set ps" by (metis assms is_trail.simps(2))
  hence "(v1,w,v2)\<notin>set ps \<and> (v1,w,v2)\<notin>set (rev_path ps)" by simp
  hence "(v1,w,v2)\<notin>set ps \<union> set (rev_path ps)" by simp
  hence "(v1,w,v2)\<in>edges G - (set ps \<union> set (rev_path ps))"
    using \<open>(v1, w, v2) \<in> E\<close> by auto
  thus "(v1,w,v2)\<in>edges(rem_unPath ps G)" 
    by (metis rem_unPath_edges)
qed

lemma distinct_path_subset:
  assumes "valid_unMultigraph G1" "valid_unMultigraph G2" "edges G1 \<subseteq>edges G2" "nodes G1 \<subseteq>nodes G2"
  assumes distinct_G1:"valid_unMultigraph.is_trail G1 v ps v'"
  shows "valid_unMultigraph.is_trail G2 v ps v'" using distinct_G1
proof (induct ps arbitrary:v)
  case Nil
  hence "v=v'\<and>v'\<in>nodes G1" 
    by (metis (full_types) assms(1) valid_unMultigraph.is_trail.simps(1))
  hence "v=v'\<and>v'\<in>nodes G2" using \<open>nodes G1 \<subseteq> nodes G2\<close> by auto
  thus ?case by (metis assms(2) valid_unMultigraph.is_trail.simps(1))
next
  case (Cons x xs)
  obtain x1 x2 x3 where x:"x=(x1,x2,x3)" by (metis prod_cases3)
  hence "valid_unMultigraph.is_trail G1 x3 xs v'"
    by (metis Cons.prems assms(1) valid_unMultigraph.is_trail.simps(2)) 
  hence "valid_unMultigraph.is_trail G2 x3 xs v'" using Cons by auto
  moreover have "x\<in>edges G1"
    by (metis Cons.prems assms(1) valid_unMultigraph.is_trail.simps(2) x)
  hence "x\<in>edges G2" using \<open>edges G1 \<subseteq> edges G2\<close> by auto
  moreover have "v=x1\<and>(x1,x2,x3)\<notin>set xs\<and>(x3,x2,x1)\<notin>set xs"
    by (metis Cons.prems assms(1) valid_unMultigraph.is_trail.simps(2) x)
  hence "v=x1" "(x1,x2,x3)\<notin>set xs" "(x3,x2,x1)\<notin>set xs" by auto
  ultimately show ?case by (metis assms(2) valid_unMultigraph.is_trail.simps(2) x)
qed

lemma (in valid_unMultigraph) distinct_path_intro':
  assumes "valid_unMultigraph.is_trail (rem_unPath p G) v ps v'"
  shows "is_trail  v ps v'" 
proof -
  have valid:"valid_unMultigraph (rem_unPath p G)"
    using rem_unPath_valid[OF valid_unMultigraph_axioms,of p] by auto
  moreover have "nodes (rem_unPath p G) \<subseteq> V" by auto
  moreover have "edges (rem_unPath p G) \<subseteq> E" 
    using rem_unPath_edges by auto
  ultimately show ?thesis 
    using distinct_path_subset[of "rem_unPath p G" G] valid_unMultigraph_axioms assms 
    by auto
qed

lemma (in valid_unMultigraph) distinct_path_intro:
  assumes "valid_unMultigraph.is_trail (del_unEdge x1 x2 x3 G) v ps v'"
  shows "is_trail  v ps v'" 
by (metis (full_types) assms distinct_path_intro' rem_unPath.simps(1) 
    rem_unPath.simps(2))

lemma (in valid_unMultigraph) distinct_elim_rev[simp]:
  assumes "is_trail v ((v1,w,v2)#ps) v'" 
  shows "(v2,w,v1)\<in>edges(rem_unPath ps G) \<longleftrightarrow> (v2,w,v1)\<in>E"
proof -
  have  "valid_unMultigraph (rem_unPath ps G)" using valid_unMultigraph_axioms by auto            
  hence "(v2,w,v1)\<in>edges(rem_unPath ps G)\<longleftrightarrow>(v1,w,v2)\<in>edges(rem_unPath ps G)"
    by (metis valid_unMultigraph.corres)
  moreover have "(v2,w,v1)\<in>E\<longleftrightarrow>(v1,w,v2)\<in>E" using corres by simp
  ultimately show ?thesis using distinct_elim by (metis assms)
qed
      
lemma (in valid_unMultigraph) del_UnEdge_even:
  assumes "(v,w,v') \<in> E" "finite E"
  shows "v\<in>odd_nodes_set(del_unEdge v w v' G) \<longleftrightarrow> even (degree v G)" 
proof -
  have "degree v (del_unEdge v w v' G) + 1=degree v G" 
    using del_edge_undirected_degree_plus corres by (metis assms)
  from this [symmetric] have "odd (degree v (del_unEdge v w v' G)) = even (degree v G)"
    by simp
  moreover have "v\<in>nodes (del_unEdge v w v' G)" by (metis E_validD(1) assms(1) del_UnEdge_node)
  ultimately show ?thesis unfolding odd_nodes_set_def by auto
qed

lemma (in valid_unMultigraph) del_UnEdge_even':
  assumes "(v,w,v') \<in> E" "finite E"
  shows "v'\<in>odd_nodes_set(del_unEdge v w v' G) \<longleftrightarrow> even (degree v' G)" 
proof -
  show ?thesis by (metis (full_types) assms corres del_UnEdge_even delete_edge_sym)          
qed

lemma del_UnEdge_even_odd:
    assumes "valid_unMultigraph G" "finite(edges G)" "finite(nodes G)" "(v, w, v')\<in>edges G"
    assumes parity_assms: "even (degree v G)" "odd (degree v' G)"
    shows "num_of_odd_nodes(del_unEdge v w v' G)=num_of_odd_nodes G"
proof -
  interpret G : valid_unMultigraph by fact
  have odd_v:"v\<in>odd_nodes_set(del_unEdge v w v' G)" 
    by (metis G.del_UnEdge_even assms(2) assms(4) parity_assms(1))
  have  not_odd_v':"v'\<notin>odd_nodes_set(del_unEdge v w v' G)"
    by (metis G.del_UnEdge_even' assms(2) assms(4) parity_assms(2))
  have "odd_nodes_set(del_unEdge v w v' G) \<union> {v'} \<subseteq>odd_nodes_set G \<union> {v}"
    proof 
      fix x 
      assume x_prems:" x \<in> odd_nodes_set (del_unEdge v w v' G) \<union> {v'}"
      have "x=v' \<Longrightarrow>x\<in>odd_nodes_set G \<union> {v}" 
        using parity_assms
        by (metis (lifting) G.E_validD(2) Un_def assms(4) mem_Collect_eq odd_nodes_set_def )
      moreover have "x=v \<Longrightarrow> x\<in>odd_nodes_set G \<union> {v}"  
        by (metis insertI1 insert_is_Un sup_commute)
      moreover have "x\<notin>{v,v'} \<Longrightarrow> x \<in> odd_nodes_set (del_unEdge v w v' G)" 
        using x_prems by auto
      hence "x\<notin>{v,v'} \<Longrightarrow> x \<in> odd_nodes_set G" unfolding odd_nodes_set_def
        using G.degree_frame \<open>finite (edges G)\<close> by auto
      hence "x\<notin>{v,v'} \<Longrightarrow> x\<in>odd_nodes_set G \<union> {v}" by simp 
      ultimately show "x \<in> odd_nodes_set G \<union> {v}" by auto
    qed
  moreover have "odd_nodes_set G \<union> {v} \<subseteq> odd_nodes_set(del_unEdge v w v' G) \<union> {v'}" 
    proof
      fix x
      assume x_prems: "x \<in> odd_nodes_set G \<union> {v}"
      have "x=v \<Longrightarrow> x \<in> odd_nodes_set (del_unEdge v w v' G) \<union> {v'}" 
        by (metis UnI1 odd_v)
      moreover have "x=v' \<Longrightarrow> x \<in> odd_nodes_set (del_unEdge v w v' G) \<union> {v'}" 
        by auto
      moreover have "x\<notin>{v,v'} \<Longrightarrow> x \<in> odd_nodes_set G \<union> {v}" using x_prems by auto
      hence "x\<notin>{v,v'} \<Longrightarrow>  x\<in>odd_nodes_set (del_unEdge v w v' G)" unfolding odd_nodes_set_def
        using G.degree_frame \<open>finite (edges G)\<close> by auto
      hence "x\<notin>{v,v'} \<Longrightarrow> x \<in> odd_nodes_set (del_unEdge v w v' G) \<union> {v'}" by simp
        ultimately show "x \<in> odd_nodes_set (del_unEdge v w v' G) \<union> {v'}" by auto
    qed
  ultimately have "odd_nodes_set(del_unEdge v w v' G) \<union> {v'} = odd_nodes_set G \<union> {v}"
    by auto
  moreover have " odd_nodes_set G \<inter> {v} = {}" 
    using parity_assms unfolding odd_nodes_set_def by auto
  moreover have " odd_nodes_set(del_unEdge v w v' G) \<inter> {v'}={}" 
    by (metis Int_insert_left_if0 inf_bot_left inf_commute not_odd_v')
  moreover have "finite (odd_nodes_set(del_unEdge v w v' G))" 
     using \<open>finite (nodes G)\<close> by auto
  moreover have "finite (odd_nodes_set G)" using \<open>finite (nodes G)\<close> by auto
  ultimately have "card(odd_nodes_set G) + card {v} = 
                   card(odd_nodes_set(del_unEdge v w v' G)) + card {v'}" 
    using card_Un_disjoint[of "odd_nodes_set (del_unEdge v w v' G)" "{v'}"] 
      card_Un_disjoint[of "odd_nodes_set G" "{v}"] 
    by auto 
  thus ?thesis unfolding num_of_odd_nodes_def by simp 
qed  
  
lemma del_UnEdge_odd_even:
    assumes "valid_unMultigraph G" "finite(edges G)" "finite(nodes G)" "(v, w, v')\<in>edges G"
    assumes parity_assms: "odd (degree v G)" "even (degree v' G)"
    shows "num_of_odd_nodes(del_unEdge v w v' G)=num_of_odd_nodes G"  
by (metis assms del_UnEdge_even_odd delete_edge_sym parity_assms valid_unMultigraph.corres)


section\<open>Connectivity\<close>

definition (in valid_unMultigraph) connected::bool where
  "connected \<equiv> \<forall> v\<in>V. \<forall>v'\<in>V. v\<noteq>v' \<longrightarrow> (\<exists>ps. is_path v ps v')"

lemma (in valid_unMultigraph) "connected \<Longrightarrow> \<forall>v\<in>V. \<forall>v'\<in>V. v\<noteq>v'\<longrightarrow>(\<exists>ps. is_trail v ps v')"
proof (rule,rule,rule)
  fix v v'
  assume "v\<in>V" "v'\<in>V" "v\<noteq>v'"
  assume connected
  obtain ps where "is_path v ps v'" by (metis \<open>connected\<close> \<open>v \<in> V\<close> \<open>v' \<in> V\<close> \<open>v\<noteq>v'\<close>  connected_def)
  then obtain ps' where "is_trail v ps' v'"
    proof (induct ps arbitrary:v )
      case Nil
      thus ?case by (metis is_trail.simps(1) is_path.simps(1))
    next
      case (Cons x xs)
      obtain x1 x2 x3 where x:"x=(x1,x2,x3)" by (metis prod_cases3)
      have "is_path x3 xs v'" by (metis Cons.prems(2) is_path.simps(2) x)
      moreover have "\<And>ps'. is_trail x3 ps' v' \<Longrightarrow> thesis" 
        proof -
          fix ps'
          assume "is_trail x3 ps' v'"
          hence "(x1,x2,x3)\<notin>set ps' \<and> (x3,x2,x1)\<notin>set ps' \<Longrightarrow>is_trail v (x#ps') v'"
            by (metis Cons.prems(2) is_trail.simps(2) is_path.simps(2) x)
          moreover have "(x1,x2,x3)\<in>set ps' \<Longrightarrow> \<exists>ps1. is_trail v ps1 v'" 
            proof -
              assume "(x1,x2,x3)\<in>set ps'"
              then obtain ps1 ps2 where "ps'=ps1@(x1,x2,x3)#ps2" by (metis split_list)
              hence "is_trail v (x#ps2) v'" 
                using \<open>is_trail x3 ps' v'\<close> x
                by (metis Cons.prems(2) is_trail.simps(2) 
                    is_trail_split is_path.simps(2))
              thus ?thesis by rule
            qed
          moreover have "(x3,x2,x1)\<in>set ps' \<Longrightarrow>  \<exists>ps1. is_trail v ps1 v'" 
             proof -
              assume "(x3,x2,x1)\<in>set ps'"
              then obtain ps1 ps2 where "ps'=ps1@(x3,x2,x1)#ps2" by (metis split_list)
              hence "is_trail v ps2 v'" 
                using \<open>is_trail x3 ps' v'\<close> x
                by (metis Cons.prems(2) is_trail.simps(2) 
                    is_trail_split is_path.simps(2))
              thus ?thesis by rule 
            qed
          ultimately show thesis using Cons by auto
        qed
      ultimately show ?case using Cons by auto
    qed
  thus "\<exists>ps. is_trail v ps v'" by rule
qed

lemma (in valid_unMultigraph) no_rep_length: "is_trail v ps v'\<Longrightarrow>length ps=card(set ps)" 
  by (induct ps arbitrary:v, auto)

lemma (in valid_unMultigraph) path_in_edges:"is_trail v ps v' \<Longrightarrow> set ps \<subseteq> E" 
proof (induct ps arbitrary:v)
  case Nil
  show ?case by auto
next
  case (Cons x xs)
  obtain x1 x2 x3 where x:"x=(x1,x2,x3)" by (metis prod_cases3)
  hence "is_trail x3 xs v'" using Cons by auto
  hence " set xs \<subseteq> E" using Cons by auto
  moreover have "x\<in>E" using Cons by (metis is_trail_intro is_path.simps(2) x)
  ultimately show ?case by auto
qed


lemma (in valid_unMultigraph) trail_bound: 
    assumes "finite E" " is_trail v ps v'"
    shows "length ps \<le>card E" 
by (metis (hide_lams, no_types) assms(1) assms(2) card_mono no_rep_length path_in_edges)

definition (in valid_unMultigraph) exist_path_length:: "'v \<Rightarrow> nat \<Rightarrow>bool" where
  "exist_path_length v l\<equiv>\<exists>v' ps. is_trail v' ps v \<and> length ps=l"   

lemma (in valid_unMultigraph) longest_path:
  assumes "finite E" "n \<in> V"
  shows "\<exists>v. \<exists>max_path. is_trail v max_path n \<and> 
        (\<forall>v'. \<forall>e\<in>E. \<not>is_trail v' (e#max_path) n)"
proof (rule ccontr)
  assume  contro:"\<not> (\<exists>v max_path. is_trail v max_path n 
           \<and> (\<forall>v'. \<forall>e\<in>E. \<not>is_trail v' (e#max_path) n))"
  hence  induct:"(\<forall>v max_path.  is_trail v max_path n 
           \<longrightarrow> (\<exists>v'. \<exists>e\<in>E. is_trail v' (e#max_path) n))" by auto
  have "is_trail n [] n" using \<open>n \<in> V\<close> by auto 
  hence "exist_path_length n 0" unfolding exist_path_length_def by auto
  moreover have "\<forall>y. exist_path_length n y \<longrightarrow> y \<le> card E" 
    using trail_bound[OF \<open>finite E\<close>] unfolding exist_path_length_def 
    by auto
  hence bound:"\<forall>y. exist_path_length n y \<longrightarrow> y \<le> card E" by auto
  ultimately have "exist_path_length n (GREATEST x. exist_path_length n x)"
    using GreatestI_nat by auto
  then obtain v max_path where 
    max_path:"is_trail v max_path n" "length max_path=(GREATEST x. exist_path_length n x)"
    by (metis exist_path_length_def)
  hence "\<exists> v' e. is_trail v' (e#max_path) n" using induct by metis
  hence "exist_path_length n (length max_path +1)" 
    by (metis One_nat_def exist_path_length_def list.size(4))
  hence "length max_path + 1 \<le> (GREATEST x. exist_path_length n x)"
   by (metis Greatest_le_nat bound)
  hence "length max_path + 1 \<le> length max_path" using max_path by auto
  thus False by auto
qed


lemma even_card':
  assumes "even(card A)" "x\<in>A"
  shows "\<exists>y\<in>A. y\<noteq>x" 
proof (rule ccontr)
  assume "\<not> (\<exists>y\<in>A. y \<noteq> x)"
  hence "\<forall>y\<in>A. y=x" by auto
  hence "A={x}" by (metis all_not_in_conv assms(2) insertI2 mk_disjoint_insert)
  hence "card(A)=1" by auto
  thus False using \<open>even(card A)\<close> by auto
qed

lemma odd_card: 
  assumes "finite A" "odd(card A)"
  shows "\<exists>x. x\<in>A" 
by (metis all_not_in_conv assms(2) card_empty even_zero) 

text\<open>replace an edge (or its reverse in a path) by another path (in an undirected graph)\<close>
fun replace_by_UnPath:: "('v,'w) path \<Rightarrow> 'v \<times>'w \<times>'v \<Rightarrow> ('v,'w) path \<Rightarrow>  ('v,'w) path" where
  "replace_by_UnPath [] _ _ = []" |
  "replace_by_UnPath (x#xs) (v,e,v') ps = 
    (if x=(v,e,v') then ps@replace_by_UnPath xs (v,e,v') ps
     else if x=(v',e,v) then (rev_path ps)@replace_by_UnPath xs (v,e,v') ps
     else x#replace_by_UnPath xs (v,e,v') ps)"

lemma (in valid_graph) path_end:"ps\<noteq>[] \<Longrightarrow> is_path v ps v' \<Longrightarrow> v'=snd (snd(last ps))" 
  by (induct ps arbitrary:v,auto)

lemma sub_graph_degree_frame:
  assumes "valid_graph G2" "edges G1 \<union> edges G2 =edges G" "nodes G1 \<inter> nodes G2={}" "n\<in>nodes G1"
  shows "degree n G=degree n G1"
proof -
  have "{e \<in> edges G. fst e = n}\<subseteq>{e \<in> edges G1. fst e = n}" 
    proof 
      fix e assume  "e \<in> {e \<in> edges G. fst e = n}"
      hence "e\<in>edges G" "fst e=n" by auto
      moreover have "n\<notin>nodes G2" 
        using \<open>nodes G1 \<inter> nodes G2={}\<close> \<open>n\<in>nodes G1\<close>
        by auto
      hence "e\<notin>edges G2" using valid_graph.E_validD[OF \<open>valid_graph G2\<close>] \<open>fst e=n\<close> 
        by (metis prod.exhaust fst_conv)  
      ultimately have "e\<in>edges G1" using \<open>edges G1 \<union> edges G2 =edges G\<close> by auto
      thus "e \<in> {e \<in> edges G1. fst e = n}" using \<open>fst e=n\<close> by auto
    qed
  moreover have "{e \<in> edges G1. fst e = n}\<subseteq>{e \<in> edges G. fst e = n}" 
    by (metis (lifting) Collect_mono Un_iff assms(2))
  ultimately show ?thesis unfolding degree_def by auto
qed
      
lemma odd_nodes_no_edge[simp]: "finite (nodes g) \<Longrightarrow> num_of_odd_nodes (g \<lparr>edges:={} \<rparr>) = 0" 
  unfolding  num_of_odd_nodes_def odd_nodes_set_def degree_def by simp

section \<open>Adjacent nodes\<close>
  
definition (in valid_unMultigraph) adjacent:: "'v \<Rightarrow> 'v \<Rightarrow> bool" where
    "adjacent v v' \<equiv> \<exists>w. (v,w,v')\<in>E"
    
lemma (in valid_unMultigraph) adjacent_sym: "adjacent v v' \<longleftrightarrow> adjacent v' v" 
    unfolding adjacent_def by auto

lemma (in valid_unMultigraph) adjacent_V[simp]: 
    assumes "adjacent v v'"
    shows "v\<in>V" "v'\<in>V"
  using assms E_validD unfolding adjacent_def by auto


lemma (in valid_unMultigraph) adjacent_finite:
  "finite E \<Longrightarrow> finite {n. adjacent v n}"
proof -
  assume "finite E"
  { fix S v 
    have "finite S \<Longrightarrow> finite {n. \<exists>w. (v,w,n)\<in>S}" 
      proof (induct S rule: finite_induct)
        case empty
        thus ?case by auto
      next
        case (insert x F)
        obtain x1 x2 x3 where x: "x=(x1,x2,x3)" by (metis prod_cases3)
        have "x1=v \<Longrightarrow> ?case"
          proof -
            assume "x1=v"
            hence "{n. \<exists>w. (v, w, n) \<in> insert x F}=insert x3 {n. \<exists>w. (v, w, n) \<in> F}"
              using x by auto
            thus ?thesis using insert by auto
          qed
        moreover have "x1\<noteq>v \<Longrightarrow> ?case"
          proof -
            assume "x1\<noteq>v"
            hence "{n. \<exists>w. (v, w, n) \<in> insert x F}={n. \<exists>w. (v, w, n) \<in> F}" using x by auto
            thus ?thesis using insert by auto
          qed
        ultimately show ?case by auto
      qed }
  note aux=this
  show ?thesis using aux[OF \<open>finite E\<close>, of v]  unfolding adjacent_def by auto
qed

section\<open>Undirected simple graph\<close>

locale valid_unSimpGraph=valid_unMultigraph G for G::"('v,'w) graph"+
              assumes no_multi[simp]: "(v,w,u) \<in> edges G \<Longrightarrow> (v,w',u) \<in>edges G \<Longrightarrow> w = w'"

lemma (in valid_unSimpGraph) finV_to_finE[simp]: 
  assumes "finite V" 
  shows "finite E"
proof (cases "{(v1,v2). adjacent v1 v2}={}")
  case True
  hence "E={}" unfolding adjacent_def by auto
  thus "finite E" by auto
next
  case False
  have "{(v1,v2). adjacent v1 v2} \<subseteq> V \<times> V" using adjacent_V by auto
  moreover have "finite (V \<times> V)" using \<open>finite V\<close> by auto
  ultimately have "finite {(v1,v2). adjacent v1 v2}" using finite_subset by auto
  hence "card {(v1,v2). adjacent v1 v2}\<noteq>0" using False card_eq_0_iff by auto
  moreover have "card E=card {(v1,v2). adjacent v1 v2}" 
    proof -
      have "(\<lambda>(v1,w,v2). (v1,v2))`E = {(v1,v2). adjacent v1 v2}" 
        proof -
          have "\<And>x. x\<in>(\<lambda>(v1,w,v2). (v1,v2))`E \<Longrightarrow> x\<in> {(v1,v2). adjacent v1 v2}" 
            unfolding adjacent_def by auto
          moreover have "\<And>x. x\<in>{(v1,v2). adjacent v1 v2} \<Longrightarrow> x\<in>(\<lambda>(v1,w,v2). (v1,v2))`E" 
            unfolding adjacent_def by force
          ultimately show ?thesis by force
        qed
      moreover have "inj_on (\<lambda>(v1,w,v2). (v1,v2)) E" unfolding inj_on_def by auto
      ultimately show ?thesis by (metis card_image)
    qed
  ultimately show "finite E" by (metis card_infinite)
qed


lemma del_unEdge_valid'[simp]:"valid_unSimpGraph G\<Longrightarrow>
    valid_unSimpGraph (del_unEdge v w u G)" 
proof -
  assume "valid_unSimpGraph G"
  hence "valid_unMultigraph (del_unEdge v w u G)" 
    using valid_unSimpGraph_def[of G] del_unEdge_valid[of G] by auto
  moreover have "valid_unSimpGraph_axioms (del_unEdge v w u G)"
    using valid_unSimpGraph.no_multi[OF \<open>valid_unSimpGraph G\<close>]
    unfolding valid_unSimpGraph_axioms_def del_unEdge_def by auto
  ultimately show "valid_unSimpGraph (del_unEdge v w u G)" using valid_unSimpGraph_def
    by auto
qed

lemma (in valid_unSimpGraph) del_UnEdge_non_adj: 
    "(v,w,u)\<in>E \<Longrightarrow> \<not>valid_unMultigraph.adjacent (del_unEdge v w u G) v u"
proof
  assume "(v, w, u) \<in> E" 
      and ccontr:"valid_unMultigraph.adjacent (del_unEdge v w u G) v u"
  have valid:"valid_unMultigraph (del_unEdge v w u G)" 
    using valid_unMultigraph_axioms by auto
  then obtain w' where vw'u:"(v,w',u)\<in>edges (del_unEdge v w u G)"
    using ccontr unfolding valid_unMultigraph.adjacent_def[OF valid] by auto
  hence "(v,w',u)\<notin>{(v,w,u),(u,w,v)}" unfolding del_unEdge_def by auto
  hence "w'\<noteq>w" by auto
  moreover have "(v,w',u)\<in>E" using vw'u unfolding del_unEdge_def by auto
  ultimately show False using no_multi[of v w u w'] \<open>(v, w, u) \<in> E\<close> by auto
qed

lemma (in valid_unSimpGraph) degree_adjacent: "finite E \<Longrightarrow> degree v G=card {n. adjacent v n}"
  using valid_unSimpGraph_axioms 
proof (induct "degree v G" arbitrary: G)
  case 0
  note valid3=\<open>valid_unSimpGraph G\<close>
  hence valid2: "valid_unMultigraph G" using valid_unSimpGraph_def by auto
  have "{a. valid_unMultigraph.adjacent G v a}={}" 
    proof (rule ccontr)
      assume "{a. valid_unMultigraph.adjacent G v a} \<noteq> {}"
      then obtain w u where "(v,w,u)\<in>edges G" 
        unfolding valid_unMultigraph.adjacent_def[OF valid2] by auto
      hence "degree v G\<noteq>0" using \<open>finite (edges G)\<close> unfolding degree_def by auto
      thus False using \<open>0 = degree v G\<close> by auto
    qed
  thus ?case by (metis "0.hyps" card_empty)
next
  case (Suc n)
  hence "{e \<in> edges G. fst e = v}\<noteq>{}" using card_empty unfolding degree_def  by force
  then obtain w u where "(v,w,u)\<in>edges G" by auto
  have valid:"valid_unMultigraph G" using \<open>valid_unSimpGraph G\<close> valid_unSimpGraph_def by auto
  hence valid':"valid_unMultigraph (del_unEdge v w u G)" by auto
  have "valid_unSimpGraph (del_unEdge v w u G)" 
    using del_unEdge_valid' \<open>valid_unSimpGraph G\<close> by auto
  moreover have "n = degree v (del_unEdge v w u G)" 
    using \<open>Suc n = degree v G\<close>\<open>(v, w, u) \<in> edges G\<close>  del_edge_undirected_degree_plus[of G v w u]
    by (metis Suc.prems(1) Suc_eq_plus1 diff_Suc_1 valid valid_unMultigraph.corres)
  moreover have "finite (edges (del_unEdge v w u G))" 
    using \<open>finite (edges G)\<close> unfolding del_unEdge_def
    by auto
  ultimately have "degree v (del_unEdge v w u G) 
      = card (Collect (valid_unMultigraph.adjacent (del_unEdge v w u G) v))"
    using Suc.hyps  by auto
  moreover have "Suc(card ({n. valid_unMultigraph.adjacent (del_unEdge v w u G)  
      v n})) = card ({n. valid_unMultigraph.adjacent G v n})" 
    using valid_unMultigraph.adjacent_def[OF valid'] 
    proof -
      have "{n. valid_unMultigraph.adjacent (del_unEdge v w u G) v n} \<subseteq> 
          {n. valid_unMultigraph.adjacent G v n}"
        using del_unEdge_def[of v w u G]
        unfolding valid_unMultigraph.adjacent_def[OF valid'] 
          valid_unMultigraph.adjacent_def[OF valid]
        by auto
      moreover have "u\<in>{n. valid_unMultigraph.adjacent G v n}" 
        using \<open>(v,w,u)\<in>edges G\<close> unfolding valid_unMultigraph.adjacent_def[OF valid] by auto
      ultimately have "{n. valid_unMultigraph.adjacent (del_unEdge v w u G) v n} \<union> {u}
          \<subseteq> {n. valid_unMultigraph.adjacent G v n}" by auto
      moreover have "{n. valid_unMultigraph.adjacent G v n} - {u}
          \<subseteq> {n. valid_unMultigraph.adjacent (del_unEdge v w u G) v n}"
        using del_unEdge_def[of v w u G]
        unfolding valid_unMultigraph.adjacent_def[OF valid'] 
          valid_unMultigraph.adjacent_def[OF valid]
        by auto
      ultimately have "{n. valid_unMultigraph.adjacent (del_unEdge v w u G) v n} \<union> {u}
          = {n. valid_unMultigraph.adjacent G v n}" by auto
      moreover have "u\<notin>{n. valid_unMultigraph.adjacent (del_unEdge v w u G) v n}" 
        using valid_unSimpGraph.del_UnEdge_non_adj[OF \<open>valid_unSimpGraph G\<close> \<open>(v,w,u)\<in>edges G\<close>]
        by auto
      moreover have "finite {n. valid_unMultigraph.adjacent G v n}" 
        using valid_unMultigraph.adjacent_finite[OF valid \<open>finite (edges G)\<close>] by simp 
      ultimately show ?thesis 
        by (metis Un_insert_right card_insert_disjoint finite_Un sup_bot_right)
    qed
  ultimately show ?case by (metis Suc.hyps(2) \<open>n = degree v (del_unEdge v w u G)\<close>)
qed 
  
end

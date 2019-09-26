(*  adapted from Peter Lammich and René Neumann *)
theory DFS_Phase
  imports Specification
    DFS_Framework.DFS_Framework
    CAVA_Automata.Digraph_Impl \<comment> \<open>maybe \<open>Digraph\<close> is enough?\<close>
    DFS_Framework.Impl_Rev_Array_Stack
begin

locale node_and_MST_in_graph =
  complete_finite_weighted_graph G weight +
  T: tree T
  for G::\<open>('v,'w::weight) graph\<close> and weight
  and T::\<open>('v,'w) graph\<close> +
  fixes v::\<open>'v\<close>
  assumes v_in_V: \<open>v \<in> V\<close>
  and mst: \<open>minimum_spanning_tree T G\<close>
begin

lemma n_in_TV_iff: \<open>n \<in> T.V \<longleftrightarrow> n \<in> V\<close>
  using mst[unfolded minimum_spanning_tree_def spanning_tree_def]
  by (meson subgraph_node)

lemma v_in_TV: \<open>v \<in> T.V\<close>
  using n_in_TV_iff v_in_V by blast

definition T' where
  \<open>T' asdf = \<lparr>g_V = V, g_E = {(v,v'). (\<exists>w.(v,w,v')\<in>T.E) \<or> (\<exists>w.(v',w,v)\<in>T.E)}, g_V0 = {v},\<dots>=asdf\<rparr>\<close>
sublocale dTgraph: graph "(T' ())"
  apply standard
  apply (auto simp: T'_def E_validD v_in_TV v_in_V)
  using T.E_validD n_in_TV_iff by blast+

lemma finite_dTgraph_reachable: \<open>finite dTgraph.reachable\<close>
  unfolding T'_def using dTgraph.finite_E by (simp add: T'_def)

lemma finite_dTgraph_V0: \<open>finite dTgraph.V0\<close>
  by (simp add: dTgraph.finite_V0 finite_dTgraph_reachable)

lemma reachable_finite: \<open>\<And>v. v \<in> dTgraph.reachable \<Longrightarrow> finite (dTgraph.E `` {v})\<close>
  by (simp add: dTgraph.fb_graphI_fr fb_graph.finitely_branching finite_dTgraph_reachable)

end

lemma (in complete_finite_weighted_graph) node_and_MST_in_graphI:
  assumes \<open>minimum_spanning_tree T G\<close> and \<open>v \<in> nodes G\<close>
  shows \<open>node_and_MST_in_graph G weight T v\<close>
  using assms
  by (simp add: complete_finite_weighted_graph_axioms minimum_spanning_tree_def node_and_MST_in_graph.intro node_and_MST_in_graph_axioms_def spanning_tree_def)

txt \<open>more robust variant in case of additional type constraints in \<^locale>\<open>node_and_MST_in_graph\<close>'s def:\<close>
lemma node_and_MST_in_graphI:
  assumes \<open>complete_finite_weighted_graph G weight\<close>
  and \<open>minimum_spanning_tree T G\<close>
  and \<open>v \<in> nodes G\<close>
  shows \<open>node_and_MST_in_graph G weight T v\<close>
  using assms
  by (simp add: minimum_spanning_tree_def node_and_MST_in_graph_axioms_def node_and_MST_in_graph_def spanning_tree_def)

subsection \<open>Framework Instantiation\<close>
text \<open> Define a state, based on the DFS-state.\<close>

record 'v cycc_state = "'v state" +
  break :: \<open>'v list\<close>


text \<open>Some utility lemmas for the simplifier, to handle idiosyncrasies of
  the record package. \<close>
lemma break_more_cong: "state.more s = state.more s' \<Longrightarrow> break s = break s'"
  by (cases s, cases s', simp)

lemma [simp]: "s\<lparr> state.more := \<lparr> break = foo \<rparr> \<rparr> = s \<lparr> break := foo \<rparr>"
  by (cases s) simp

text \<open>
  Define the parameterization. We start at a default parameterization, where
  all operations default to skip, and just add the operations we are 
  interested in: Initially, the break flag is false, it is set if we 
  encounter a back-edge, and once set, the algorithm shall terminate immediately. \<close>
definition cycc_params :: "('v,('v,unit) cycc_state_ext) parameterization"
where "cycc_params \<equiv> dflt_parametrization state.more 
  (RETURN \<lparr> break = [] \<rparr>) \<lparr>
  on_discover := \<lambda>_ n s. RETURN \<lparr>break = break s @ [n]\<rparr>
  \<^cancel>\<open>,on_back_edge := \<lambda>_ _ . RETURN o state.more,\<close>
  \<^cancel>\<open>is_break := \<lambda>s. break s = []\<close> \<rparr>"
lemmas cycc_params_simp[simp] = 
  gen_parameterization.simps[mk_record_simp, OF cycc_params_def[simplified]]

interpretation cycc: param_DFS_defs where param=cycc_params for G .

text \<open>The total correct variant asserts finitely many reachable nodes.\<close>
definition "cyc_checkerT G weight T v \<equiv> do {
  ASSERT (node_and_MST_in_graph G weight T v);
  s \<leftarrow> cycc.it_dfsT TYPE('a) (node_and_MST_in_graph.T' G T v (undefined::'a));
  RETURN (break s)
}"

\<^cancel>\<open>text \<open>
  Next, we define a locale for the cyclicity checker's
  precondition and invariant, by specializing the \<open>param_DFS\<close> locale.\<close>
locale cycc = param_DFS G cycc_params for G :: "('v, 'more) graph_rec_scheme"
begin
  text \<open>We can easily show that our parametrization does not fail, thus we also
    get the DFS-locale, which gives us the correctness theorem for
    the DFS-scheme \<close>
  sublocale DFS G cycc_params
    apply unfold_locales
    apply simp_all
    done

  thm it_dfs_correct  \<comment> \<open>Partial correctness\<close>
  thm it_dfsT_correct \<comment> \<open>Total correctness if set of reachable states is finite\<close> 
end\<close>
context node_and_MST_in_graph begin
sublocale DFS "T' ()" cycc_params
  apply unfold_locales
         apply simp_all
   apply (fact finite_dTgraph_V0)
  by (fact reachable_finite)

  thm it_dfs_correct  \<comment> \<open>Partial correctness\<close>
  thm it_dfsT_correct \<comment> \<open>Total correctness if set of reachable states is finite\<close> 
end


text \<open>Next, we specialize the @{term DFS_invar} locale to our parameterization.
  This locale contains all proven invariants. When proving new invariants,
  this locale is available as assumption, thus allowing us to re-use already 
  proven invariants.
\<close>
locale cycc_invar = dTgraph: DFS_invar
  where param = cycc_params
    and G = \<open>node_and_MST_in_graph.T' G T v ()\<close> +
  node_and_MST_in_graph

text \<open> The lemmas to establish invariants only provide the \<open>DFS_invar\<close> locale.
  This lemma is used to convert it into the \<open>cycc_invar\<close> locale.
\<close>
lemma (in node_and_MST_in_graph) cycc_invar_eq[simp]:
  assumes \<open>DFS_invar (node_and_MST_in_graph.T' G T v ()) cycc_params s\<close>
  shows "cycc_invar s G weight T v"
proof
  assume "DFS_invar (node_and_MST_in_graph.T' G T v) cycc_params s"
  interpret DFS_invar "(node_and_MST_in_graph.T' G T v)" cycc_params s by fact
  show "cycc_invar s G weight T v" by unfold_locales
next
  assume "cycc_invar G s"
  then interpret cycc_invar G s .
  show "DFS_invar G cycc_params s" by unfold_locales
qed*)

subsection \<open>Correctness Proof\<close>
text \<open> We now enter the \<open>cycc_invar\<close> locale, and show correctness of 
  our cyclicity checker.
\<close>
context cycc_invar begin
  text \<open>We show that we break if and only if there are back edges. 
    This is straightforward from our parameterization, and we can use the 
    @{thm [source] dTgraph.establish_invarI} rule provided by the DFS framework.

    We use this example to illustrate the general proof scheme:
    \<close>

lemma (in node_and_MST_in_graph) \<open>is_invar (\<lambda>s. tour (break s))\<close> 
proof (induct rule: establish_invarI)
case init
then show ?case sorry
next
  case (new_root s s' v0)
  then show ?case by (simp_all cong: break_more_cong)
next
  case (finish s s' u)
  then show ?case by (simp_all cong: break_more_cong)
next
  case (cross_edge s s' u v)
  then show ?case by (simp_all cong: break_more_cong)
next
  case (back_edge s s' u v)
  then show ?case by (simp_all cong: break_more_cong)
next
  case (discover s s' u v)
  then show ?case sorry
qed
 

(*
  lemma (in cycc) i_brk_eq_back: "is_invar (\<lambda>s. break s = [] \<longleftrightarrow> back_edges s \<noteq> {})"
  proof (induct rule: establish_invarI)
  txt \<open>The @{thm establish_invarI} rule is used with the induction method, and 
    yields cases\<close>
  print_cases
    txt \<open>Our parameterization has only hooked into initialization and back-edges,
      so only these two cases are non-trivial\<close>
    case init thus ?case try by (simp add: empty_state_def)
  next
    case (back_edge s s' u v)
    txt \<open>For proving invariant preservation, we may assume that the invariant 
      holds on the previous state. Interpreting the invariant locale makes 
      available all invariants ever proved into this locale (i.e., the invariants 
      from all loaded libraries, and the ones you proved yourself.).
      \<close>
    then interpret cycc_invar G s by simp
    txt \<open>However, here we do not need them:\<close>
    from back_edge show ?case by simp
  qed (simp_all cong: break_more_cong)

  text \<open>For technical reasons, invariants are proved in the basic locale, 
    and then transferred to the invariant locale:\<close>  
  lemmas brk_eq_back = i_brk_eq_back[THEN make_invar_thm]

  text \<open>The above lemma is simple enough to have a short apply-style proof:\<close>
  lemma (in cycc) i_brk_eq_back_short_proof: 
    "is_invar (\<lambda>s. break s \<longleftrightarrow> back_edges s \<noteq> {})"
    apply (induct rule: establish_invarI)
    apply (simp_all add: cond_def cong: break_more_cong)
    apply (simp add: empty_state_def)
    done

  text \<open>Now, when we know that the break flag indicates back-edges,
    we can easily prove correctness, using a lemma from the invariant 
    library:\<close>
  thm cycle_iff_back_edges
  lemma cycc_correct_aux: 
    assumes NC: "\<not>cond s"
    shows "break s \<longleftrightarrow> \<not>acyclic (E \<inter> reachable \<times> UNIV)"
  proof (cases "break s", simp_all)
    assume "break s"
    with brk_eq_back have "back_edges s \<noteq> {}" by simp
    with cycle_iff_back_edges have "\<not>acyclic (edges s)" by simp
    with acyclic_subset[OF _ edges_ss_reachable_edges] 
    show "\<not>acyclic (E \<inter> reachable \<times> UNIV)" by blast
  next
    assume A: "\<not>break s"
    from A brk_eq_back have "back_edges s = {}" by simp
    with cycle_iff_back_edges have "acyclic (edges s)" by simp
    also from A nc_edges_covered[OF NC] have "edges s = E \<inter> reachable \<times> UNIV" 
      by simp
    finally show "acyclic (E \<inter> reachable \<times> UNIV)" .
  qed

  text \<open>Again, we have a short two-line proof:\<close>
  lemma cycc_correct_aux_short_proof:
    assumes NC: "\<not>cond s"
    shows "break s \<longleftrightarrow> \<not>acyclic (E \<inter> reachable \<times> UNIV)"
    using nc_edges_covered[OF NC] brk_eq_back cycle_iff_back_edges 
    by (auto dest: acyclic_subset[OF _ edges_ss_reachable_edges])
*)
    
end
(*
definition \<open>circuit_finderT_spec T n \<equiv> do {
ASSERT (node_in_graph w T n);
SPEC (\<lambda>ns. is_hamiltonian_circuit)}\<close>

text \<open>The same for the total correct variant:\<close>
definition "cyc_checkerT_spec G \<equiv> do {
  ASSERT (graph G \<and> finite (graph_defs.reachable G));
  SPEC (\<lambda>r. r \<longleftrightarrow> \<not>acyclic (g_E G \<inter> ((g_E G)\<^sup>* `` g_V0 G) \<times> UNIV))}"

theorem cyc_checkerT_correct: "cyc_checkerT G \<le> cyc_checkerT_spec G"
  unfolding cyc_checkerT_def cyc_checkerT_spec_def
proof (refine_vcg le_ASSERTI order_trans[OF DFS.it_dfsT_correct], clarsimp_all)
  assume "graph G" then interpret graph G .
  assume "finite (graph_defs.reachable G)"
  then interpret fb_graph G by (rule fb_graphI_fr)
  interpret cycc by unfold_locales
  show "DFS G cycc_params" by unfold_locales
next
  fix s
  assume "cycc_invar G s"
  then interpret cycc_invar G s .
  assume "\<not>cycc.cond TYPE('b) G s"
  thus "break s = (\<not> acyclic (g_E G \<inter> cycc.reachable TYPE('b) G \<times> UNIV))"
    by (rule cycc_correct_aux)
qed


subsection \<open>Implementation\<close>
text \<open>
  The implementation has two aspects: Structural implementation and data implementation.
  The framework provides recursive and tail-recursive implementations, as well as a variety
  of data structures for the state.

  We will choose the \<open>simple_state\<close> implementation, which provides 
  a stack, an on-stack and a visited set, but no timing information.

  Note that it is common for state implementations to omit details from the
  very detailed abstract state. This means, that the algorithm's operations 
  must not access these details (e.g. timing). However, the algorithm's 
  correctness proofs may still use them.
\<close>

text \<open>We extend the state template to add a break flag\<close>
record 'v cycc_state_impl = "'v simple_state" +
  break :: bool

text \<open>Definition of refinement relation: The break-flag is refined by identity.\<close>
definition "cycc_erel \<equiv> { 
  (\<lparr> cycc_state_impl.break = b \<rparr>, \<lparr> cycc_state.break = b\<rparr>) | b. True }"
abbreviation "cycc_rel \<equiv> \<langle>cycc_erel\<rangle>simple_state_rel"

text \<open>Implementation of the parameters\<close>
definition cycc_params_impl 
  :: "('v,'v cycc_state_impl,unit cycc_state_impl_ext) gen_parameterization"
where "cycc_params_impl 
  \<equiv> dflt_parametrization simple_state.more (RETURN \<lparr> break = False \<rparr>) \<lparr>
  on_back_edge := \<lambda>u v s. RETURN \<lparr> break = True \<rparr>,
  is_break := break \<rparr>"
lemmas cycc_params_impl_simp[simp,DFS_code_unfold] = 
  gen_parameterization.simps[mk_record_simp, OF cycc_params_impl_def[simplified]]

text \<open>Note: In this simple case, the reformulation of the extension state and 
  parameterization is just redundant, However, in general the refinement will 
  also affect the parameterization.\<close>

lemma break_impl: "(si,s)\<in>cycc_rel 
  \<Longrightarrow> cycc_state_impl.break si = cycc_state.break s"
  by (cases si, cases s, simp add: simple_state_rel_def cycc_erel_def)

interpretation cycc_impl: simple_impl_defs G cycc_params_impl cycc_params 
  for G .

text \<open>The above interpretation creates an iterative and a recursive implementation \<close>
term cycc_impl.tailrec_impl term cycc_impl.rec_impl
term cycc_impl.tailrec_implT \<comment> \<open>Note, for total correctness we currently only support tail-recursive implementations.\<close>

text \<open>We use both to derive a tail-recursive and a recursive cyclicity checker:\<close>
definition [DFS_code_unfold]: "cyc_checker_impl G \<equiv> do {
  ASSERT (fb_graph G);
  s \<leftarrow> cycc_impl.tailrec_impl TYPE('a) G;
  RETURN (break s)
}"

definition [DFS_code_unfold]: "cyc_checker_rec_impl G \<equiv> do {
  ASSERT (fb_graph G);
  s \<leftarrow> cycc_impl.rec_impl TYPE('a) G;
  RETURN (break s)
}"

definition [DFS_code_unfold]: "cyc_checker_implT G \<equiv> do {
  ASSERT (graph G \<and> finite (graph_defs.reachable G));
  s \<leftarrow> cycc_impl.tailrec_implT TYPE('a) G;
  RETURN (break s)
}"



text \<open>To show correctness of the implementation, we integrate the
  locale of the simple implementation into our cyclicity checker's locale:\<close>
context cycc begin
  sublocale simple_impl G cycc_params cycc_params_impl cycc_erel 
    apply unfold_locales
    apply (intro fun_relI, clarsimp simp: simple_state_rel_def, parametricity) []
    apply (auto simp: cycc_erel_def break_impl simple_state_rel_def)
    done

  text \<open>We get that our implementation refines the abstrct DFS algorithm.\<close>  
  lemmas impl_refine = simple_tailrec_refine simple_rec_refine simple_tailrecT_refine

  text \<open>Unfortunately, the combination of locales and abbreviations gets to its 
    limits here, so we state the above lemma a bit more readable:\<close>
  lemma 
    "cycc_impl.tailrec_impl TYPE('more) G \<le> \<Down> cycc_rel it_dfs"
    "cycc_impl.rec_impl TYPE('more) G \<le> \<Down> cycc_rel it_dfs"
    "cycc_impl.tailrec_implT TYPE('more) G \<le> \<Down> cycc_rel it_dfsT"
    using impl_refine .

end

text \<open>Finally, we get correctness of our cyclicity checker implementations\<close>
lemma cyc_checker_impl_refine: "cyc_checker_impl G \<le> \<Down>Id (cyc_checker G)"
  unfolding cyc_checker_impl_def cyc_checker_def
  apply (refine_vcg cycc.impl_refine)
  apply (simp_all add: break_impl cyccI)
  done
  
lemma cyc_checker_rec_impl_refine: 
  "cyc_checker_rec_impl G \<le> \<Down>Id (cyc_checker G)"
  unfolding cyc_checker_rec_impl_def cyc_checker_def
  apply (refine_vcg cycc.impl_refine)
  apply (simp_all add: break_impl cyccI)
  done

lemma cyc_checker_implT_refine: "cyc_checker_implT G \<le> \<Down>Id (cyc_checkerT G)"
  unfolding cyc_checker_implT_def cyc_checkerT_def
  apply (refine_vcg cycc.impl_refine)
  apply (simp_all add: break_impl cyccI')
  done


subsection \<open>Synthesizing Executable Code\<close>
text \<open>
  Our algorithm's implementation is still abstract, as it uses abstract data 
  structures like sets and relations. In a last step, we use the Autoref tool
  to derive an implementation with efficient data structures.
\<close>

text \<open>Again, we derive our state implementation from the template provided by 
  the framework. The break-flag is implemented by a Boolean flag. 
  Note that, in general, the user-defined state extensions may be data-refined
  in this step.\<close>
record ('si,'nsi,'psi)cycc_state_impl' = "('si,'nsi)simple_state_impl" +
  break_impl :: bool

text \<open>We define the refinement relation for the state extension\<close>
definition [to_relAPP]: "cycc_state_erel erel \<equiv> {
  (\<lparr>break_impl = bi, \<dots> =  mi\<rparr>,\<lparr>break = b, \<dots> = m\<rparr>) | bi mi b m.
    (bi,b)\<in>bool_rel \<and> (mi,m)\<in>erel}"

text \<open>And register it with the Autoref tool:\<close>
consts 
  i_cycc_state_ext :: "interface \<Rightarrow> interface"

lemmas [autoref_rel_intf] = REL_INTFI[of cycc_state_erel i_cycc_state_ext]


text \<open>We show that the record operations on our extended state are parametric,
  and declare these facts to Autoref: \<close>
lemma [autoref_rules]:
  fixes ns_rel vis_rel erel
  defines "R \<equiv> \<langle>ns_rel,vis_rel,\<langle>erel\<rangle>cycc_state_erel\<rangle>ss_impl_rel"
  shows 
    "(cycc_state_impl'_ext, cycc_state_impl_ext) \<in> bool_rel \<rightarrow> erel \<rightarrow> \<langle>erel\<rangle>cycc_state_erel"
    "(break_impl, cycc_state_impl.break) \<in> R \<rightarrow> bool_rel"
  unfolding cycc_state_erel_def ss_impl_rel_def R_def
  by auto

(* for Digraph: *)
type_synonym 'a slg = "'a \<Rightarrow> 'a list"

definition slg_rel :: "('a\<times>'b) set \<Rightarrow> ('a slg \<times> 'b digraph) set" where 
  slg_rel_def_internal: "slg_rel R \<equiv> 
  (R \<rightarrow> \<langle>R\<rangle>list_set_rel) O br (\<lambda>succs. {(u,v). v\<in>succs u}) (\<lambda>_. True)"

lemma slg_rel_def: "\<langle>R\<rangle>slg_rel = 
  (R \<rightarrow> \<langle>R\<rangle>list_set_rel) O br (\<lambda>succs. {(u,v). v\<in>succs u}) (\<lambda>_. True)"
  unfolding slg_rel_def_internal relAPP_def by simp

record ('vi,'ei,'v0i) gen_g_impl =
  gi_V :: 'vi
  gi_E :: 'ei
  gi_V0 :: 'v0i

definition gen_f_impl_rel_ext_internal_def: "\<And> Rm Rv Re Rv0. gen_f_impl_rel_ext Rm Rv Re Rv0
  \<equiv> { (gen_g_impl_ext Vi Ei V0i mi, graph_rec_ext V E V0 m) 
      | Vi Ei V0i mi V E V0 m. 
        (Vi,V)\<in>Rv \<and> (Ei,E)\<in>Re \<and> (V0i,V0)\<in>Rv0 \<and> (mi,m)\<in>Rm
    }"

lemma gen_f_impl_rel_ext_def: "\<And>Rm Rv Re Rv0. \<langle>Rm,Rv,Re,Rv0\<rangle>gen_f_impl_rel_ext
  \<equiv> { (gen_g_impl_ext Vi Ei V0i mi, graph_rec_ext V E V0 m) 
      | Vi Ei V0i mi V E V0 m. 
        (Vi,V)\<in>Rv \<and> (Ei,E)\<in>Re \<and> (V0i,V0)\<in>Rv0 \<and> (mi,m)\<in>Rm
    }"
  unfolding gen_f_impl_rel_ext_internal_def relAPP_def by simp

definition f_impl_rel_ext_internal_def: 
  "f_impl_rel_ext Rm Rv 
  \<equiv> \<langle>Rm,\<langle>Rv\<rangle>fun_set_rel,\<langle>Rv\<rangle>slg_rel,\<langle>Rv\<rangle>list_set_rel\<rangle>gen_g_impl_rel_ext"

lemma g_impl_rel_ext_def: "\<langle>Rm,Rv\<rangle>g_impl_rel_ext
  \<equiv> \<langle>Rm,\<langle>Rv\<rangle>fun_set_rel,\<langle>Rv\<rangle>Digraph_Impl.slg_rel,\<langle>Rv\<rangle>list_set_rel\<rangle>gen_g_impl_rel_ext"
  unfolding g_impl_rel_ext_internal_def relAPP_def by simp
(* end for Digraph *)


text \<open>And, again, for the total correct version. 
  Note that we generate a plain implementation, not inside a monad:\<close>
schematic_goal cyc_checker_implT:
  defines "V \<equiv> Id :: ('v \<times> 'v::hashable) set"
  assumes [unfolded V_def,autoref_rules]:
    "(Gi, G) \<in> \<langle>Rm, V\<rangle>g_impl_rel_ext"
  notes [unfolded V_def,autoref_tyrel] = 
    TYRELI[where R="\<langle>V\<rangle>dflt_ahs_rel"]
    TYRELI[where R="\<langle>V \<times>\<^sub>r \<langle>V\<rangle>list_set_rel\<rangle>ras_rel"]
  shows "RETURN (?c::?'c) \<le>\<Down>?R (cyc_checker_implT G)"
  unfolding DFS_code_unfold
  using [[autoref_trace_failed_id, goals_limit=1]]
  apply (autoref_monadic (trace,plain))
  done
concrete_definition cyc_checker_codeT uses cyc_checker_implT
export_code cyc_checker_codeT checking SML

theorem cyc_checker_codeT_correct:
  assumes 1: "graph G" "finite (graph_defs.reachable G)"
  assumes 2: "(Gi, G) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext"
  shows "cyc_checker_codeT Gi \<longleftrightarrow> (\<not>acyclic (g_E G \<inter> ((g_E G)\<^sup>* `` g_V0 G) \<times> UNIV))"
proof -
  note cyc_checker_codeT.refine[OF 2]
  also note cyc_checker_implT_refine
  also note cyc_checkerT_correct
  finally show ?thesis using 1
  unfolding cyc_checkerT_spec_def by auto
qed

context node_in_graph
begin

thm cyc_checker_codeT_correct[OF dgraph.graph_axioms]

end
*)
end

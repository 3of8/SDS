theory SDS_Automation
imports Preference_Profile_Cmd
keywords "derive_orbit_equations" "derive_support_conditions" :: thy_goal
begin

locale strategyproof_an_sds =
  strategyproof_sds agents alts sds + an_sds agents alts sds
  for agents :: "'agent set" and alts :: "'alt set" and sds


lemma disj_False_right: "P \<or> False \<longleftrightarrow> P" by simp

lemmas multiset_add_ac = add_ac[where ?'a = "'a multiset"]

lemma ex_post_efficient_aux:
  assumes "prefs_from_table_wf agents alts xss" "R \<equiv> prefs_from_table xss"
  assumes "i \<in> agents" "\<forall>i\<in>agents. y \<succeq>[prefs_from_table xss i] x" "\<not>y \<preceq>[prefs_from_table xss i] x"
  shows   "ex_post_efficient_sds agents alts sds \<longrightarrow> pmf (sds R) x = 0"
proof
  assume ex_post: "ex_post_efficient_sds agents alts sds"
  from assms(1,2) have wf: "pref_profile_wf agents alts R"
    by (simp add: pref_profile_from_tableI')
  from ex_post interpret ex_post_efficient_sds agents alts sds .
  from assms(2-) show "pmf (sds R) x = 0"
    by (intro ex_post_efficient''[OF wf, of i x y]) simp_all
qed

lemma SD_inefficient_support_aux:
  assumes R: "prefs_from_table_wf agents alts xss" "R \<equiv> prefs_from_table xss"
  assumes as: "as \<noteq> []" "set as \<subseteq> alts" "distinct as" "A = set as" 
  assumes ys: "\<forall>x\<in>set (map snd ys). 0 \<le> x" "listsum (map snd ys) = 1" "set (map fst ys) \<subseteq> alts"
  assumes i: "i \<in> agents"
  assumes SD1: "\<forall>i\<in>agents. \<forall>x\<in>alts. 
    listsum (map snd (filter (\<lambda>y. prefs_from_table xss i x (fst y)) ys)) \<ge>
    real (length (filter (prefs_from_table xss i x) as)) / real (length as)"
  assumes SD2: "\<exists>x\<in>alts. listsum (map snd (filter (\<lambda>y. prefs_from_table xss i x (fst y)) ys)) >
                        real (length (filter (prefs_from_table xss i x) as)) / real (length as)"
  shows   "sd_efficient_sds agents alts sds \<longrightarrow> (\<exists>x\<in>A. pmf (sds R) x = 0)"
proof
  assume "sd_efficient_sds agents alts sds"
  from R have wf: "pref_profile_wf agents alts R" 
    by (simp add: pref_profile_from_tableI')
  then interpret pref_profile_wf agents alts R .
  interpret sd_efficient_sds agents alts sds by fact
  from ys have ys': "pmf_of_list_wf ys" by (intro pmf_of_list_wfI) auto
  
  {
    fix i x assume "x \<in> alts" "i \<in> agents"
    with ys' have "lottery_prob (pmf_of_list ys) (preferred_alts (R i) x) = 
      listsum (map snd (filter (\<lambda>y. prefs_from_table xss i x (fst y)) ys))"
      by (subst measure_pmf_of_list) (simp_all add: preferred_alts_def R)
  } note A = this
  {
    fix i x assume "x \<in> alts" "i \<in> agents"
    with as have "lottery_prob (pmf_of_set (set as)) (preferred_alts (R i) x) = 
      real (card (set as \<inter> preferred_alts (R i) x)) / real (card (set as))"
      by (subst measure_pmf_of_set) simp_all
    also have "set as \<inter> preferred_alts (R i) x = set (filter (\<lambda>y. R i x y) as)"
      by (auto simp add: preferred_alts_def)
    also have "card \<dots> = length (filter (\<lambda>y. R i x y) as)"
      by (intro distinct_card distinct_filter assms)
    also have "card (set as) = length as" by (intro distinct_card assms)
    finally have "lottery_prob (pmf_of_set (set as)) (preferred_alts (R i) x) =
      real (length (filter (prefs_from_table xss i x) as)) / real (length as)"
      by (simp add: R)
  } note B = this

  from wf show "\<exists>x\<in>A. pmf (sds R) x = 0"
  proof (rule SD_inefficient_support')
    from ys ys' show lottery1: "pmf_of_list ys \<in> lotteries" by (intro pmf_of_list_lottery)
    show i: "i \<in> agents" by fact
    from as have lottery2: "pmf_of_set (set as) \<in> lotteries"
      by (intro pmf_of_set_lottery) simp_all
    from i as SD2 lottery1 lottery2 show "\<not>SD (R i) (pmf_of_list ys) (pmf_of_set A)"
      by (subst preorder_on.SD_preorder[of alts]) (auto simp: A B not_le)
    from as SD1 lottery1 lottery2 
      show "\<forall>i\<in>agents. SD (R i) (pmf_of_set A) (pmf_of_list ys)"
        by safe (auto simp: preorder_on.SD_preorder[of alts] A B)
  qed (insert as, simp_all)
qed



definition pref_classes where
  "pref_classes alts le = preferred_alts le ` alts - {alts}"

primrec pref_classes_lists where
  "pref_classes_lists [] = {}"
| "pref_classes_lists (xs#xss) = insert (\<Union>(set (xs#xss))) (pref_classes_lists xss)"

lemma pref_classes_of_weak_ranking:
  assumes "\<Union>(set xss) = alts" "is_weak_ranking xss"
  shows   "pref_classes alts (of_weak_ranking xss) = pref_classes_lists (rev xss)"
proof -
  from assms(2) 
    have "of_weak_ranking_Collect_ge xss ` (\<Union>(set xss)) = pref_classes_lists xss"
apply (induction xss)
apply simp
unfolding is_weak_ranking_Cons of_weak_ranking_Collect_ge_Cons' pref_classes_lists.simps
apply (auto simp: split: if_splits)
apply blast
done

context preorder_on
begin

lemma preferred_alts_subset: "preferred_alts le x \<subseteq> carrier"
  unfolding preferred_alts_def using not_outside by blast

lemma SD_iff_pref_classes:
  assumes "p \<in> lotteries_on carrier" "q \<in> lotteries_on carrier"
  shows   "p \<preceq>[SD(le)] q \<longleftrightarrow> 
             (\<forall>A\<in>pref_classes carrier le. measure_pmf.prob p A \<le> measure_pmf.prob q A)"
proof safe
  fix A assume "p \<preceq>[SD(le)] q" "A \<in> pref_classes carrier le"
  thus "measure_pmf.prob p A \<le> measure_pmf.prob q A"
    by (auto simp: SD_preorder pref_classes_def)
next
  assume A: "\<forall>A\<in>pref_classes carrier le. measure_pmf.prob p A \<le> measure_pmf.prob q A"
  show "p \<preceq>[SD(le)] q"
  proof (rule SD_preorderI)
    fix x assume x: "x \<in> carrier"
    show "measure_pmf.prob p (preferred_alts le x)
             \<le> measure_pmf.prob q (preferred_alts le x)"
    proof (cases "preferred_alts le x = carrier")
      case False
      with x have "preferred_alts le x \<in> pref_classes carrier le"
        unfolding pref_classes_def by (intro DiffI imageI) simp_all
      with A show ?thesis by simp
    next
      case True
      from assms have "measure_pmf.prob p carrier = 1" "measure_pmf.prob q carrier = 1"
        by (auto simp: measure_pmf.prob_eq_1 lotteries_on_def AE_measure_pmf_iff)
      with True show ?thesis by simp
    qed
  qed (insert assms, simp_all)
qed

lemma (in strategyproof_an_sds) strategyproof':
  assumes wf: "is_pref_profile R" "complete_preorder_on alts Ri'" and i: "i \<in> agents"
  shows   "(\<exists>A\<in>pref_classes alts (R i). lottery_prob (sds (R(i := Ri'))) A <
                        lottery_prob (sds R) A) \<or>
           (\<forall>A\<in>pref_classes alts (R i). lottery_prob (sds (R(i := Ri'))) A =
                        lottery_prob (sds R) A)"
proof -
  from wf(1) interpret R: pref_profile_wf agents alts R .
  from i interpret complete_preorder_on alts "R i" by simp
  from assms have "\<not> manipulable_profile R i Ri'" by (intro strategyproof)
  moreover from wf i have "sds R \<in> lotteries" "sds (R(i := Ri')) \<in> lotteries"
    by (simp_all add: sds_wf)
  ultimately show ?thesis
    by (fastforce simp: manipulable_profile_def strongly_preferred_def
                        SD_iff_pref_classes not_le not_less)
qed

lemma strategyproof_aux:
  assumes wf: "prefs_from_table_wf agents alts xss1" "R1 = prefs_from_table xss1"
              "prefs_from_table_wf agents alts xss2" "R2 = prefs_from_table xss2"
  assumes sds: "strategyproof_an_sds agents alts sds" and i: "i \<in> agents" and j: "j \<in> agents"
  assumes eq:  "R1(i := R2 j) = R2"
  shows P
proof -
  from sds interpret strategyproof_an_sds agents alts sds .
  let ?Ri' = "R2 j"
  from wf j have wf': "is_pref_profile R1" "complete_preorder_on alts ?Ri'"
    by (auto intro: pref_profile_from_tableI pref_profile_wf.prefs_wf'(1))

  from strategyproof'[OF wf' i] eq have
    "(\<exists>A\<in>pref_classes alts (R1 i). lottery_prob (sds R2) A < lottery_prob (sds R1) A) \<or>
     (\<forall>A\<in>pref_classes alts (R1 i). lottery_prob (sds R2) A = lottery_prob (sds R1) A)"
    by simp
   

  let ?R' = "R(i := Ri')" and ?P = "\<lambda>S x. lottery_prob (sds S) (preferred_alts (R i) x)"
  from wf(1) interpret R: pref_profile_wf agents alts R .
  from i interpret complete_preorder_on alts "R i" by simp
  from assms have "\<not> manipulable_profile R i Ri'" by (intro strategyproof)
  moreover from wf i have "sds R \<in> lotteries" "sds (R(i := Ri')) \<in> lotteries"
    by (simp_all add: sds_wf)
  ultimately show ?thesis
    by (force simp: manipulable_profile_def strongly_preferred_def SD_preorder not_le not_less)
qed



ML \<open>

open Preference_Profiles
open Preference_Profiles_Cmd

fun mk_permutation_term sigma = 
  let
    val altT = sigma |> hd |> fst |> fastype_of
  in
    sigma |> map HOLogic.mk_prod |> HOLogic.mk_list (HOLogic.mk_prodT (altT, altT))
  end

fun prepare_orbit_intro_thms_single ctxt sds_am_thm (p : info) ((x,y), sigma) =
  let
    val {wf_raw_thm = wf_raw_thm, def_thm = def_thm, ...} = p
    val cterm = Thm.cterm_of ctxt
    val sigma_term = mk_permutation_term sigma
    val thm = (@{thm an_sds_automorphism_aux} OF [wf_raw_thm, def_thm, sds_am_thm])
              |> Thm.instantiate' [] (map (SOME o cterm) [sigma_term, x, y])
  in
    thm
  end

fun prepare_orbit_intro_thms ctxt sds_am_thm (p : info) =
  let
    val {raw = p_raw, ...} = p
  in
    derive_orbit_equations p_raw
    |> map (prepare_orbit_intro_thms_single ctxt sds_am_thm p)
  end

fun get_agents_alts_term ({wf_thm, ...} : info) =
  let
    val agents :: alts :: _ = wf_thm |> Thm.concl_of |> HOLogic.dest_Trueprop |> strip_comb |> snd
  in
    (agents, alts)
  end

fun gen_derive_orbit_equations lthy ps =
  let
    val lthy0 = lthy
    val infos = map (fn p => get_info p lthy) ps
    val (altT, agentT) = infos |> hd |> #raw |> (fn x => (altT x, agentT x))
    val sdsT = sdsT agentT altT

    val ([sds], lthy) = Variable.variant_fixes ["sds"] lthy0
    val sds = Free (sds, sdsT)
    val lthy = Variable.declare_term sds lthy

    val (agents_term, alts_term) = get_agents_alts_term (hd infos)
    val sds_an_const = Const (@{const_name an_sds}, HOLogic.mk_setT agentT --> 
      HOLogic.mk_setT altT --> sdsT --> HOLogic.boolT)
    val sds_am_prop = HOLogic.mk_Trueprop (sds_an_const $ agents_term $ alts_term $ sds)
    val ([sds_am_thm], lthy) = Assumption.add_assumes [Thm.cterm_of lthy sds_am_prop] lthy

    val intros = map (prepare_orbit_intro_thms lthy sds_am_thm) infos
    val goals = map (map (fn x => (Thm.concl_of x, []))) intros
    val bindings = infos |> map 
      (fn info => Binding.qualify true (Binding.name_of (#binding info)) (Binding.name "orbits"))
    val lthy = lthy addsimps @{thms multiset_add_ac insert_commute}

    val before_proof = 
      let
        fun tac ctxt = 
          ALLGOALS (resolve_tac ctxt (List.concat intros))
          THEN distinct_subgoals_tac
      in
        Method.Basic (SIMPLE_METHOD o tac)
      end

    fun afterqed (thmss : thm list list) lthy =
      let
        val thmss = burrow (Proof_Context.export lthy lthy0) thmss
        val thmss_aux = map2 (fn bdg => fn thms => ((bdg, []), [(thms, [])])) bindings thmss
      in
        Local_Theory.notes thmss_aux lthy0
        |> snd
      end
  in
    Proof.theorem NONE afterqed goals lthy
    |> Proof.refine_singleton before_proof
  end

fun derive_orbit_equations_cmd ps lthy =
  gen_derive_orbit_equations lthy (map (Syntax.read_term lthy) ps)

val _ =
  Outer_Syntax.local_theory_to_proof @{command_keyword derive_orbit_equations}
    "automatically derives the orbit equations for preference profiles"
    (Scan.repeat1 Parse.term >> derive_orbit_equations_cmd);



fun prepare_ex_post_conditions sds (info : info) lthy =
  let
    val {raw = p, wf_raw_thm, def_thm, ...} = info
    val losers = pareto_losers p
    val cterm = Thm.cterm_of lthy
    fun prep (x,y,i) = 
      (@{thm ex_post_efficient_aux} OF [wf_raw_thm, def_thm])
      |> Thm.instantiate' [] (map (SOME o cterm) [i, x, y, sds])
  in
    map prep losers
  end

fun prepare_sdeff_conditions sds (info : info) lthy =
  let
    val {raw = p, wf_raw_thm, def_thm, ...} = info
    val altT = altT p
    val supports = find_minimal_inefficient_supports p
    val cterm = Thm.cterm_of lthy
    fun prep (supp,lott,i) = 
      let
        val supp_list = HOLogic.mk_list altT supp
        val supp_set = HOLogic.mk_set altT supp
        val lott = 
          lott
          |> map (HOLogic.mk_prod o apsnd (MyRat.mk_rat_number @{typ Real.real}))
          |> HOLogic.mk_list (HOLogic.mk_prodT (altT, @{typ Real.real}))
      in
        (@{thm SD_inefficient_support_aux} OF [wf_raw_thm, def_thm])
        |> Thm.instantiate' [] (map (SOME o cterm) [supp_list, supp_set, lott, i, sds])
    end
  in
    map prep supports
  end

fun gen_derive_support_conditions providers ps lthy =
  let
    val lthy0 = lthy
    val infos = map (fn p => get_info p lthy) ps
    val (altT, agentT) = infos |> hd |> #raw |> (fn x => (altT x, agentT x))
    val sdsT = sdsT agentT altT

    val ([sds], lthy) = Variable.variant_fixes ["sds"] lthy0
    val sds = Free (sds, sdsT)
    val lthy = Variable.declare_term sds lthy

    val intros = map (fn info => List.concat (map (fn p => p sds info lthy) providers)) infos
    val goals = map (map (fn x => (Thm.concl_of x, []))) intros
    val bindings = infos |> map 
      (fn info => Binding.qualify true (Binding.name_of (#binding info)) (Binding.name "support"))

    val before_proof = 
      let
        fun tac ctxt = 
          ALLGOALS (resolve_tac ctxt (List.concat intros))
          THEN distinct_subgoals_tac
      in
        Method.Basic (SIMPLE_METHOD o tac)
      end

    fun postproc lthy thm =
      thm 
        |> (fn thm => thm RS @{thm HOL.mp})
        |> Local_Defs.unfold lthy 
             (map (fn thm => thm RS @{thm eq_reflection}) @{thms Set.bex_simps disj_False_right})

    fun afterqed (thmss : thm list list) lthy =
      let
        val thmss = 
          thmss |> burrow (Proof_Context.export lthy lthy0 o map (postproc lthy))
        val thmss_aux = map2 (fn bdg => fn thms => ((bdg, []), [(thms, [])])) bindings thmss
      in
        Local_Theory.notes thmss_aux lthy0
        |> snd
      end
  in
    Proof.theorem NONE afterqed goals lthy
    |> Proof.refine_singleton before_proof
  end

fun gen_derive_support_conditions_cmd providers ts lthy = 
  gen_derive_support_conditions providers (map (Syntax.read_term lthy) ts) lthy

val derive_support_conditions_cmd = 
  gen_derive_support_conditions_cmd [prepare_ex_post_conditions, prepare_sdeff_conditions]

val _ =
  Outer_Syntax.local_theory_to_proof @{command_keyword derive_support_conditions}
    "automatically conditions for the support of preference profiles"
    (Scan.repeat1 Parse.term >> derive_support_conditions_cmd);

\<close>


(* TODO: For testing only; can be removed *)
datatype agents = A1 | A2 | A3 | A4
datatype alts = a | b | c | d

preference_profile 
  agents: "{A1, A2, A3, A4}"
  alts:   "{a, b, c, d}"
where R1  = A1: [c, d], [a, b]    A2: [b, d], a, c      A3: a, b, [c, d]      A4: [a, c], [b, d]
  and R2  = A1: [a, c], [b, d]    A2: [c, d], a, b      A3: [b, d], a, c      A4: a, b, [c, d]
  and R3  = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: d, [a, b], c      A4: c, a, [b, d]
  and R4  = A1: [a, b], [c, d]    A2: [a, d], [b, c]    A3: c, [a, b], d      A4: d, c, [a, b]
  and R5  = A1: [c, d], [a, b]    A2: [a, b], [c, d]    A3: [a, c], d, b      A4: d, [a, b], c
  and R6  = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: [a, c], [b, d]    A4: d, b, a, c
  and R7  = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: a, c, d, b        A4: d, [a, b], c
  and R8  = A1: [a, b], [c, d]    A2: [a, c], [b, d]    A3: d, [a, b], c      A4: d, c, [a, b]
  and R9  = A1: [a, b], [c, d]    A2: [a, d], c, b      A3: d, c, [a, b]      A4: [a, b, c], d
  and R10 = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: [a, c], d, b      A4: [b, d], a, c
  and R11 = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: d, [a, b], c      A4: c, a, b, d
  and R12 = A1: [c, d], [a, b]    A2: [a, b], [c, d]    A3: [a, c], d, b      A4: [a, b, d], c
  and R13 = A1: [a, c], [b, d]    A2: [c, d], a, b      A3: [b, d], a, c      A4: a, b, d, c
  and R14 = A1: [a, b], [c, d]    A2: d, c, [a, b]      A3: [a, b, c], d      A4: a, d, c, b
  and R15 = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: [b, d], a, c      A4: a, c, d, b
  and R16 = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: a, c, d, b        A4: [a, b, d], c
  and R17 = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: [a, c], [b, d]    A4: d, [a, b], c
  and R18 = A1: [a, b], [c, d]    A2: [a, d], [b, c]    A3: [a, b, c], d      A4: d, c, [a, b]
  and R19 = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: [b, d], a, c      A4: [a, c], [b, d]
  and R20 = A1: [b, d], a, c      A2: b, a, [c, d]      A3: a, c, [b, d]      A4: d, c, [a, b]
  and R21 = A1: [a, d], c, b      A2: d, c, [a, b]      A3: c, [a, b], d      A4: a, b, [c, d]
  and R22 = A1: [a, c], d, b      A2: d, c, [a, b]      A3: d, [a, b], c      A4: a, b, [c, d]
  and R23 = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: [a, c], [b, d]    A4: [a, b, d], c
  and R24 = A1: [c, d], [a, b]    A2: d, b, a, c        A3: c, a, [b, d]      A4: b, a, [c, d]
  and R25 = A1: [c, d], [a, b]    A2: [b, d], a, c      A3: a, b, [c, d]      A4: a, c, [b, d]
  and R26 = A1: [b, d], [a, c]    A2: [c, d], [a, b]    A3: a, b, [c, d]      A4: a, c, [b, d]
  and R27 = A1: [a, b], [c, d]    A2: [b, d], a, c      A3: [a, c], [b, d]    A4: [c, d], a, b
  and R28 = A1: [c, d], a, b      A2: [b, d], a, c      A3: a, b, [c, d]      A4: a, c, [b, d]
  and R29 = A1: [a, c], d, b      A2: [b, d], a, c      A3: a, b, [c, d]      A4: d, c, [a, b]
  and R30 = A1: [a, d], c, b      A2: d, c, [a, b]      A3: c, [a, b], d      A4: [a, b], d, c
  and R31 = A1: [b, d], a, c      A2: [a, c], d, b      A3: c, d, [a, b]      A4: [a, b], c, d
  and R32 = A1: [a, c], d, b      A2: d, c, [a, b]      A3: d, [a, b], c      A4: [a, b], d, c
  and R33 = A1: [c, d], [a, b]    A2: [a, c], d, b      A3: a, b, [c, d]      A4: d, [a, b], c
  and R34 = A1: [a, b], [c, d]    A2: a, c, d, b        A3: b, [a, d], c      A4: c, d, [a, b]
  and R35 = A1: [a, d], c, b      A2: a, b, [c, d]      A3: [a, b, c], d      A4: d, c, [a, b]
  and R36 = A1: [c, d], [a, b]    A2: [a, c], d, b      A3: [b, d], a, c      A4: a, b, [c, d]
  and R37 = A1: [a, c], [b, d]    A2: [b, d], [a, c]    A3: a, b, [c, d]      A4: c, d, [a, b]
  and R38 = A1: [c, d], a, b      A2: [b, d], a, c      A3: a, b, [c, d]      A4: [a, c], b, d
  and R39 = A1: [a, c], d, b      A2: [b, d], a, c      A3: a, b, [c, d]      A4: [c, d], a, b
  and R40 = A1: [a, d], c, b      A2: [a, b], c, d      A3: [a, b, c], d      A4: d, c, [a, b]
  and R41 = A1: [a, d], c, b      A2: [a, b], d, c      A3: [a, b, c], d      A4: d, c, [a, b]
  and R42 = A1: [c, d], [a, b]    A2: [a, b], [c, d]    A3: d, b, a, c        A4: c, a, [b, d]
  and R43 = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: d, [a, b], c      A4: a, [c, d], b
  and R44 = A1: [c, d], [a, b]    A2: [a, c], d, b      A3: [a, b], d, c      A4: [a, b, d], c
  and R45 = A1: [a, c], d, b      A2: [b, d], a, c      A3: [a, b], c, d      A4: [c, d], b, a
  and R46 = A1: [b, d], a, c      A2: d, c, [a, b]      A3: [a, c], [b, d]    A4: b, a, [c, d]
  and R47 = A1: [a, b], [c, d]    A2: [a, d], c, b      A3: d, c, [a, b]      A4: c, [a, b], d
  by simp_all


derive_orbit_equations
  R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20
  R21 R22 R23 R24 R25 R26 R27 R28 R29 R30 R31 R32 R33 R34 R35 R36 R37 R38 R39 R40
  R41 R42 R43 R44 R45 R46 R47
  by simp_all

derive_support_conditions 
  R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20
  R21 R22 R23 R24 R25 R26 R27 R28 R29 R30 R31 R32 R33 R34 R35 R36 R37 R38 R39 R40
  R41 R42 R43 R44 R45 R46 R47
  by simp_all




(*
preference_profile 
  agents: "{A1, A2, A3, A4}"
  alts:   "{a, b, c, d}"
  where R1  = A1: [a,c], [b,d]     A2: [b,d], [a,c]     A3: [a,d], b, c     A4: [b,c], a, d
    and R2  = A1: [a,c], [b,d]     A2: [b,d], [a,c]     A3: a, d, [b,c]     A4: b, c, [a, d]
    and R3  = A1: [a,c], [b,d]     A2: [b,d], [a,c]     A3: [a,d], b, c     A4: d, c, a, b
    and R4  = A1: [a,c], [b,d]     A2: [b,d], [a,c]     A3: [c,b], d, a     A4: b, a, c, d
    and R5  = A1: [a,c,d], [b]     A2: [b,a], [c,d]     A3: [c,b], d, a     A4: b, a, [d,c]
    and R6  = A1: [a,c], d, b      A2: [b,d], a, c      A3: [a,b], c, d     A4: [c, d], b, a
by (simp_all add: insert_eq_iff)
*)

(*
ML_val \<open>
  open Preference_Profiles;
  
  let
    val ctxt = @{context}
    val {raw = raw1, ...} = Preference_Profiles_Cmd.get_info @{term R1} ctxt
    val {raw = raw2, ...} = Preference_Profiles_Cmd.get_info @{term R2} ctxt
    val {raw = raw3, ...} = Preference_Profiles_Cmd.get_info @{term R3} ctxt
    val {raw = raw4, ...} = Preference_Profiles_Cmd.get_info @{term R4} ctxt
    val {raw = raw5, ...} = Preference_Profiles_Cmd.get_info @{term R5} ctxt
    val b = Preference_Profiles.equiv_profile_anonymity (raw1, raw2)
    val w = Preference_Profiles.find_an_isomorphisms (raw1, raw2) |> Seq.list_of
    val auto = derive_orbit_equations raw1
    val cterm = Thm.cterm_of ctxt
  in
    auto |> hd
(*    auto |> map (apfst (apply2 cterm) o apsnd (map (apply2 cterm))) *)
(*    find_manipulations (raw1, raw3)
    |> map (fn (a,b,c) => (cterm a, map (map cterm) b, map (apply2 cterm) c)) *)
(*      find_minimal_inefficient_supports raw1 
      |> map (fn (a,b,c) => (map cterm a, map (apfst cterm) b, cterm c)) *)
(*      pareto_losers raw5 |> map (fn (a,b,c) => (cterm a, cterm b, cterm c)) *)
  end
  
\<close>*)

end

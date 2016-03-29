(*  
  Title:    SDS_Impossibility.thy
  Author:   Manuel Eberl, TU München

  The impossibility of an anonymous, neutral, SD-efficient, and
  weakly strategy-proof SDS for at least 4 agents and alternatives.
*)

section \<open>Main Impossibility Result\<close>

theory SDS_Impossibility
imports
  Complex_Main
  Social_Decision_Schemes
  Preference_Profile_Cmd
  Random_Dictatorship
begin


locale sds_impossibility = 
  anonymous_sds agents alts sds +
  neutral_sds agents alts sds +
  sd_efficient_sds agents alts sds +
  strategyproof_sds agents alts sds
  for agents :: "'agent set" and alts :: "'alt set" and sds +
  assumes agents_ge_4: "card agents \<ge> 4"
      and alts_ge_4:   "card alts \<ge> 4"

      
subsection \<open>Proof of the impossibility for 4 agents and alternatives\<close>
      
locale sds_impossibility_4_4 = sds_impossibility agents alts sds
  for agents :: "'agent set" and alts :: "'alt set" and sds +
  fixes A1 A2 A3 A4 :: 'agent and a b c d :: 'alt
  assumes distinct_agents: "distinct [A1, A2, A3, A4]"
      and distinct_alts: "distinct [a, b, c, d]"
      and agents: "agents = {A1, A2, A3, A4}"
      and alts:   "alts   = {a, b, c, d}"
begin

lemma distinct_agents' [simp]: 
  "A1 \<noteq> A2" "A1 \<noteq> A3" "A1 \<noteq> A4" "A2 \<noteq> A1" "A2 \<noteq> A3" "A2 \<noteq> A4" 
  "A3 \<noteq> A1" "A3 \<noteq> A2" "A3 \<noteq> A4" "A4 \<noteq> A1" "A4 \<noteq> A2" "A4 \<noteq> A3"
  using distinct_agents by auto
  
lemma distinct_alts' [simp]:
  "a \<noteq> b" "a \<noteq> c" "a \<noteq> d" "b \<noteq> a" "b \<noteq> c" "b \<noteq> d" 
  "c \<noteq> a" "c \<noteq> b" "c \<noteq> d" "d \<noteq> a" "d \<noteq> b" "d \<noteq> c"
  using distinct_alts by auto


subsubsection \<open>Definition of preference profiles\<close>

preference_profile 
  agents: agents 
  alts:   alts 
  where R1  = A1: [a,c], [b,d]     A2: [b,d], [a,c]     A3: [a,d], b, c     A4: [b,c], a, d
    and R2  = A1: [a,c], [b,d]     A2: [b,d], [a,c]     A3: a, d, [b,c]     A4: b, c, [a, d]
    and R3  = A1: a, c, [b, d]     A2: [b, d], a, c     A3: a, d, [b, c]    A4: [b, c], a, d
    and R4  = A1: a, [b, c, d]     A2: [b, d], a, c     A3: a, d, [b, c]    A4: [b, c], a, d
    and R5  = A1: a, [b, c, d]     A2: [b, d], a, c     A3: a, [b, c, d]    A4: [b, c], a, d
    and R6  = A1: a, [b, c, d]     A2: b, [a, c, d]     A3: a, [b, c, d]    A4: [b, c], a, d
    and R7  = A1: a, [b, c, d]     A2: b, [a, c, d]     A3: a, [b, c, d]    A4: b, [a, c, d]
    and R8  = A1: [a, c], [b, d]   A2: [b, d], [a, c]   A3: a, d, [b, c]    A4: [b, c], a, d
    and R9  = A1: a, c, [b, d]     A2: [b, d], [a, c]   A3: a, d, [b, c]    A4: [b, c], a, d
    and R10 = A1: [a, c], [b, d]   A2: b, [a, c], d     A3: a, d, [b, c]    A4: [b, c], a, d
    and R11 = A1: c, a, [b, d]     A2: b, [a, c], d     A3: a, d, [b, c]    A4: [b, c], a, d
    and R12 = A1: c, [a, b], d     A2: b, [a, c], d     A3: a, d, [b, c]    A4: [b, c], a, d
    and R13 = A1: c, [a, b], d     A2: b, [a, c], d     A3: a, d, [b, c]    A4: b, c, a, d
  by (simp_all add: agents alts insert_eq_iff)

ML_val \<open>
  let
    val {raw, ...} = Preference_Profiles.get_info @{term "R1"} @{context}
    in raw
    end
  \<close>
  
lemma "a \<succ>[R1 A1] b"
  by (simp add: R1_eval)

lemma "favorites R1 A1 = {a, c}"
  by (simp add: R1_eval)

  
subsubsection \<open>Simplification setup\<close>

lemmas eval_profile_permutation = 
  permute_profile_from_table[of agents alts] permute_prefs_from_table agents alts prefs_from_table_wf_def
  is_weak_ranking_Cons is_finite_weak_ranking_Cons insert_commute insert_eq_iff inv_lists_succ_eq
  prefs_from_table_swap lists_succ_permutes' distincts_Cons list_succ_def prefs_from_table_eqI

lemmas [simp] = sds_wf

lemma card_agents [simp]: "card agents = 4" and card_alts [simp]: "card alts = 4"
  using distinct_agents distinct_alts by (simp_all add: agents alts)

lemma in_agents [simp]: "A1 \<in> agents" "A2 \<in> agents" "A3 \<in> agents" "A4 \<in> agents"
  by (simp_all add: agents)

lemma in_alts [simp]: "a \<in> alts" "b \<in> alts" "c \<in> alts" "d \<in> alts"
  by (simp_all add: alts)
  
lemma agent_iff: "x \<in> agents \<longleftrightarrow> x \<in> {A1, A2, A3, A4}"
                 "Ball agents P \<longleftrightarrow> P A1 \<and> P A2 \<and> P A3 \<and> P A4"
                 "Bex agents P \<longleftrightarrow> P A1 \<or> P A2 \<or> P A3 \<or> P A4"
  by (auto simp add: agents)

lemma alt_iff: "x \<in> alts \<longleftrightarrow> x \<in> {a,b,c,d}"
               "Ball alts P \<longleftrightarrow> P a \<and> P b \<and> P c \<and> P d"
               "Bex alts P \<longleftrightarrow> P a \<or> P b \<or> P c \<or> P d"
  by (auto simp add: alts)
  
lemma mset_agents: "mset_set agents = {#A1, A2, A3, A4#}"
  by (simp add: agents)

lemma complete_preorder_on_altsI [simp]:
  "is_pref_profile R \<Longrightarrow> i \<in> agents \<Longrightarrow> complete_preorder_on alts (R i)"
  by (rule pref_profile_wf.prefs_wf')


lemma pmf_of_set_in_lotteries [simp]:
  "A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> pmf_of_set A \<in> lotteries \<longleftrightarrow> A \<subseteq> alts"
  unfolding lotteries_on_def by simp

lemma pmf_of_multiset_in_lotteries [simp]:
  "A \<noteq> {#} \<Longrightarrow> pmf_of_multiset A \<in> lotteries \<longleftrightarrow> set_mset A \<subseteq> alts"
  unfolding lotteries_on_def by simp

lemma lottery_prob_alts': "p \<in> lotteries \<Longrightarrow> pmf p a + pmf p b + pmf p c + pmf p d = 1"
  using lottery_prob_alts[of p]
  by (simp add: alts measure_measure_pmf_finite)

lemma pmf_lottery_0: "p \<in> lotteries \<Longrightarrow> i \<notin> alts \<Longrightarrow> pmf p i = 0"
  unfolding lotteries_on_def by (auto simp add: set_pmf_iff)

lemma lottery_eqI:
  assumes "p \<in> lotteries" "q \<in> lotteries" "\<And>i. i \<in> alts \<Longrightarrow> pmf p i = pmf q i"
  shows   "p = q"
proof (rule pmf_eqI)
  fix i
  from assms show "pmf p i = pmf q i" 
    by (cases "i \<in> alts") (simp_all add: pmf_lottery_0)
qed

lemma lottery_eqI':
  assumes "p \<in> lotteries" "q \<in> lotteries" "\<And>i. i \<in> {a,b,c,d} \<Longrightarrow> pmf p i = pmf q i"
  shows   "p = q"
  using assms lottery_eqI[of p q] by (subst (asm) alts [symmetric]) simp_all

lemma SD_agenda_abs: 
  "complete_preorder_on alts R \<Longrightarrow>
     SD R = (\<lambda>p q. q \<in> lotteries \<and> p \<in> lotteries \<and>
       (\<forall>x\<in>alts. lottery_prob p (preferred_alts R x) \<le> lottery_prob q (preferred_alts R x)))"
  by (intro ext) (simp_all add: SD_agenda)

lemmas eval_SD = 
  strongly_preferred_def measure_measure_pmf_finite SD_agenda_abs alt_iff agent_iff
  R1_eval R2_eval R3_eval R4_eval R5_eval R6_eval R7_eval R8_eval R9_eval R10_eval
  R11_eval R12_eval R13_eval

lemma Pareto_strict_iff: 
  "is_pref_profile R \<Longrightarrow> x \<prec>[Pareto(R)] y \<longleftrightarrow> (\<forall>i\<in>agents. R i x y) \<and> (\<exists>i\<in>agents. x \<prec>[R i] y)"
  by (intro pref_profile_wf.Pareto_strict_iff[of agents])
  
  
  
subsubsection \<open>Contradiction proof\<close>
                  
lemma sds_R1: "sds R1 = pmf_of_set {a, b}"
proof -
  def \<pi> \<equiv> "lists_succ [[A1,A2],[A3,A4]]" and \<sigma> \<equiv> "lists_succ [[a,b],[c,d]]"
  let ?p = "pmf (sds R1)"
  have perm: "\<pi> permutes agents" "\<sigma> permutes alts"
    by (simp_all add: \<pi>_def \<sigma>_def lists_succ_permutes' distincts_Cons agents alts insert_commute)
  have "sds R1 = sds (permute_profile \<sigma> R1 \<circ> \<pi>)"
    by (simp add: R1_def \<sigma>_def \<pi>_def eval_profile_permutation)
  also from perm have "\<dots> = map_pmf \<sigma> (sds R1)"
    by (simp add: anonymous neutral perm pref_profile_wf.wf_permute_alts)
  finally have "pmf (map_pmf \<sigma> (sds R1)) x = pmf (sds R1) x" for x by simp
  from this[of "\<sigma> b"] this[of "\<sigma> d"] perm 
    have [simp]: "?p a = ?p b" "?p c = ?p d"
    by (simp_all add: pmf_map_inj' permutes_inj) (simp_all add: \<sigma>_def list_succ_def)

  have A: "pmf (sds R1) b * 2 + pmf (sds R1) d * 2 = 1"
    using lottery_prob_alts'[of "sds R1"] by simp

  have "?p d = 0"
  proof (rule ccontr, rule SD_efficient')
    assume "?p d \<noteq> 0"
    hence pos: "?p d > 0" using pmf_nonneg[of "sds R1" c] by simp    
    from A show "pmf_of_set {a, b} \<succeq>[SD(R1 i)] sds R1" if "i \<in> agents" for i
      using measure_pmf.prob_le_1[of "sds R1" "{a,b,c}"] that
      by (auto simp: eval_SD)
    from A pos show "pmf_of_set {a, b} \<succ>[SD(R1 A3)] sds R1"
      by (auto simp: eval_SD)
  qed simp_all
  with A have "\<forall>x\<in>alts. pmf (sds R1) x = pmf (pmf_of_set {a, b}) x"
    by (auto simp: alts)
  thus "sds R1 = pmf_of_set {a, b}"
    by (intro lottery_eqI) (simp_all add: indicator_def)
qed

lemma sds_R2: "sds R2 = pmf_of_set {a, b}"
proof -
  def \<pi> \<equiv> "lists_succ [[A1,A2],[A3,A4]]" and \<sigma> \<equiv> "lists_succ [[a,b],[c,d]]"
  let ?p = "pmf (sds R2)"
  have perm: "\<pi> permutes agents" "\<sigma> permutes alts"
    by (simp_all add: \<pi>_def \<sigma>_def lists_succ_permutes' distincts_Cons agents alts insert_commute)
  have "sds R2 = sds (permute_profile \<sigma> R2 \<circ> \<pi>)"
    by (simp add: R2_def \<sigma>_def \<pi>_def eval_profile_permutation)
  also from perm have "\<dots> = map_pmf \<sigma> (sds R2)"
    by (simp add: anonymous neutral perm pref_profile_wf.wf_permute_alts)
  finally have "pmf (map_pmf \<sigma> (sds R2)) x = pmf (sds R2) x" for x by simp
  from this[of "\<sigma> b"] this[of "\<sigma> d"] perm 
    have [simp]: "?p a = ?p b" "?p c = ?p d"
    by (simp_all add: pmf_map_inj' permutes_inj) (simp_all add: \<sigma>_def list_succ_def)

  have A: "pmf (sds R2) b * 2 + pmf (sds R2) d * 2 = 1"
    using lottery_prob_alts'[of "sds R2"] by simp

  have "?p d = 0"
  proof (rule ccontr, rule SD_efficient')
    assume "?p d \<noteq> 0"
    hence pos: "?p d > 0" using pmf_nonneg[of "sds R2" c] by simp    
    from A show "pmf_of_set {a, b} \<succeq>[SD(R2 i)] sds R2" if "i \<in> agents" for i
      using measure_pmf.prob_le_1[of "sds R2" "{a,b,c}"] that by (auto simp: eval_SD)
    from A pos show "pmf_of_set {a, b} \<succ>[SD(R2 A3)] sds R2"
      by (auto simp: eval_SD)
  qed simp_all
  with A have "\<forall>x\<in>alts. pmf (sds R2) x = pmf (pmf_of_set {a, b}) x"
    by (auto simp: alts)
  thus "sds R2 = pmf_of_set {a, b}"
    by (intro lottery_eqI) (simp_all add: indicator_def)
qed

lemma pmf_of_list_lottery:
  assumes "pmf_of_list_wf xs" "set (map fst xs) \<subseteq> alts"
  shows   "pmf_of_list xs \<in> lotteries"
  using set_pmf_of_list[OF assms(1)] assms(2) unfolding lotteries_on_def by blast

lemma sds_R3 [simp]: "pmf (sds R3) c = 0" "pmf (sds R3) d = 0"
proof -
  def \<pi> \<equiv> "lists_succ [[A1,A3],[A2,A4]]" and \<sigma> \<equiv> "lists_succ [[a],[b],[c,d]]"
  let ?p = "pmf (sds R3)"
  have perm: "\<pi> permutes agents" "\<sigma> permutes alts"
    by (simp_all add: \<pi>_def \<sigma>_def lists_succ_permutes' distincts_Cons agents alts insert_commute)
  have R3_eq: "R3 = (permute_profile \<sigma> R3 \<circ> \<pi>)"
    by (simp add: R3_def \<sigma>_def \<pi>_def eval_profile_permutation)
  from perm have "pmf (map_pmf \<sigma> (sds R3)) x = pmf (sds R3) x" for x
    by (subst R3_eq) (simp add: anonymous neutral perm pref_profile_wf.wf_permute_alts)
  from this[of "\<sigma> b"] this[of "\<sigma> d"] perm 
    have [simp]: "?p c = ?p d"
    by (simp_all add: pmf_map_inj' permutes_inj) (simp_all add: \<sigma>_def list_succ_def)

  have A: "pmf (sds R3) a + pmf (sds R3) b + pmf (sds R3) d * 2 = 1"
      using lottery_prob_alts'[of "sds R3"] by simp

  show "?p d = 0"
  proof (rule ccontr, rule SD_efficient')
    assume "?p d \<noteq> 0"
    hence pos: "?p d > 0" using pmf_nonneg[of "sds R3" c] by simp    
    def q \<equiv> "pmf_of_list [(a, ?p a + ?p c), (b, ?p b + ?p c)]"
    have [simp]: "q \<in> lotteries" 
      using set_pmf_of_list[of "[(a, ?p a + ?p c), (b, ?p b + ?p c)]"] A
      by (auto simp add: q_def lotteries_on_def alt_iff pmf_of_list_wf_def pmf_nonneg)
    have [simp]: "pmf q a = ?p a + ?p c" "pmf q b = ?p b + ?p d" "pmf q c = 0" "pmf q d = 0"
      using A unfolding q_def
      by (subst pmf_pmf_of_list; (auto simp: q_def pmf_pmf_of_list pmf_nonneg
                                         intro!: pmf_of_list_wfI)[])+
    from A show "q \<succeq>[SD(R3 i)] sds R3" if "i \<in> agents" for i
      using measure_pmf.prob_le_1[of "sds R3" "{a,b,c}"] that
      by (auto simp: eval_SD)
    from A pos show "q \<succ>[SD(R3 A1)] sds R3" by (auto simp: eval_SD)
  qed (insert A, auto simp: pmf_nonneg intro!: pmf_of_list_lottery pmf_of_list_wfI)
  thus "?p c = 0" by simp
qed

lemma sds_R3_b: "pmf (sds R3) b = 1 - pmf (sds R3) a"
  using lottery_prob_alts'[OF sds_wf[OF R3_wf]] by simp


lemma less_by_contradiction: "((x::real) \<le> y \<Longrightarrow> False) \<Longrightarrow> x > y"
  by (cases "x > y") simp_all

lemma le_by_contradiction: "((x::real) < y \<Longrightarrow> False) \<Longrightarrow> x \<ge> y"
  by (cases "x \<ge> y") simp_all

  
context
assumes sds_R3_a: "pmf (sds R3) a > 1/2"
begin

lemma sds_R4_a: "pmf (sds R4) a > 1/2"
proof (rule less_by_contradiction)
  have A: "pmf (sds R4) a + pmf (sds R4) b + pmf (sds R4) c + pmf (sds R4) d = 1"
          "pmf (sds R3) a + pmf (sds R3) b + pmf (sds R3) c + pmf (sds R3) d = 1"
      using lottery_prob_alts'[of "sds R4"] lottery_prob_alts'[of "sds R3"]
      by simp_all

  assume a: "pmf (sds R4) a \<le> 1/2"
  with sds_R3_a have "sds R3 \<succ>[SD (R4 A1)] sds R4"
    using A by (auto simp: eval_SD)
  also have "R3 = R4(A1 := R3 A1)"
    unfolding R4_def R3_def by (simp add: prefs_from_table_update)
  finally have "manipulable_profile R4 A1 (R3 A1)"
    unfolding manipulable_profile_def .
  with strategyproof[of R4 A1 "R3 A1"] show False by simp
qed

lemma sds_R5_a: "pmf (sds R5) a > 1/2"
proof (rule less_by_contradiction)
  have A: "pmf (sds R5) a + pmf (sds R5) b + pmf (sds R5) c + pmf (sds R5) d = 1"
          "pmf (sds R4) a + pmf (sds R4) b + pmf (sds R4) c + pmf (sds R4) d = 1"
      using lottery_prob_alts'[of "sds R5"] lottery_prob_alts'[of "sds R4"] by simp_all

  assume a: "pmf (sds R5) a \<le> 1/2"
  with sds_R4_a have "sds R4 \<succ>[SD (R5 A3)] sds R5"
    using A by (auto simp: eval_SD)
  also have "R4 = R5(A3 := R4 A3)"
    unfolding R4_def R5_def by (simp add: prefs_from_table_update)
  finally have "manipulable_profile R5 A3 (R4 A3)"
    unfolding manipulable_profile_def .
  with strategyproof[of R5 A3 "R4 A3"] show False by simp
qed

lemma sds_R5 [simp]: "pmf (sds R5) c = 0" "pmf (sds R5) d = 0"
proof -
  have "c \<prec>[Pareto(R5)] b" "d \<prec>[Pareto(R5)] b"
    by (auto simp: Pareto_strict_iff R5_eval agent_iff)
  thus "pmf (sds R5) c = 0" "pmf (sds R5) d = 0"
    by (auto intro: ex_post_efficient' R5_wf)
qed

lemma sds_R6 [simp]: "pmf (sds R6) c = 0" "pmf (sds R6) d = 0"
proof -
  have "c \<prec>[Pareto(R6)] b" "d \<prec>[Pareto(R6)] b"
    by (auto simp: Pareto_strict_iff R6_eval agent_iff)
  thus "pmf (sds R6) c = 0" "pmf (sds R6) d = 0"
    by (auto intro: ex_post_efficient' R6_wf)
qed

lemma sds_R6_a: "pmf (sds R6) a > 1/2"
proof (rule less_by_contradiction)
  have A: "pmf (sds R5) a + pmf (sds R5) b + pmf (sds R5) c + pmf (sds R5) d = 1"
          "pmf (sds R6) a + pmf (sds R6) b + pmf (sds R6) c + pmf (sds R6) d = 1"
      using lottery_prob_alts'[of "sds R5"] lottery_prob_alts'[of "sds R6"] by simp_all

  assume "pmf (sds R6) a \<le> 1/2"
  with sds_R5_a have "sds R6 \<succ>[SD (R5 A2)] sds R5"
    using A by (auto simp: eval_SD)
  also have "R6 = R5(A2 := R6 A2)"
    unfolding R5_def R6_def by (simp add: prefs_from_table_update)
  finally have "manipulable_profile R5 A2 (R6 A2)"
    unfolding manipulable_profile_def .
  with strategyproof[of R5 A2 "R6 A2"] show False by simp
qed

lemma sds_R7 [simp]: "pmf (sds R7) c = 0" "pmf (sds R7) d = 0"
proof -
  have "c \<prec>[Pareto(R7)] b" "d \<prec>[Pareto(R7)] b"
    by (auto simp: Pareto_strict_iff R7_eval agent_iff)
  thus "pmf (sds R7) c = 0" "pmf (sds R7) d = 0"
    by (auto intro: ex_post_efficient' R7_wf)
qed

lemma sds_R7_a: "pmf (sds R7) a > 1/2"
proof (rule less_by_contradiction)
  have A: "pmf (sds R6) a + pmf (sds R6) b + pmf (sds R6) c + pmf (sds R6) d = 1"
          "pmf (sds R7) a + pmf (sds R7) b + pmf (sds R7) c + pmf (sds R7) d = 1"
      using lottery_prob_alts'[of "sds R6"] lottery_prob_alts'[of "sds R7"] by simp_all

  assume "pmf (sds R7) a \<le> 1/2"
  with sds_R6_a have "sds R7 \<succ>[SD (R6 A4)] sds R6"
    using A by (auto simp add: eval_SD)
  also have "R7 = R6(A4 := R7 A4)"
    unfolding R6_def R7_def by (simp add: prefs_from_table_update)
  finally have "manipulable_profile R6 A4 (R7 A4)"
    unfolding manipulable_profile_def .
  with strategyproof[of R6 A4 "R7 A4"] show False by simp
qed

lemma sds_R7_b: "pmf (sds R7) b = pmf (sds R7) a"
proof -
  def \<pi> \<equiv> "lists_succ [[A1,A2],[A3,A4]]" and \<sigma> \<equiv> "lists_succ [[a,b],[c],[d]]"
  let ?p = "pmf (sds R7)"
  have perm: "\<pi> permutes agents" "\<sigma> permutes alts"
    by (simp_all add: \<pi>_def \<sigma>_def lists_succ_permutes' distincts_Cons agents alts insert_commute)
  have R7_eq: "R7 = (permute_profile \<sigma> R7 \<circ> \<pi>)"
    by (simp add: R7_def \<sigma>_def \<pi>_def eval_profile_permutation)
  from perm have "pmf (map_pmf \<sigma> (sds R7)) x = pmf (sds R7) x" for x
    by (subst R7_eq) (simp add: anonymous neutral perm pref_profile_wf.wf_permute_alts)
  from this[of "\<sigma> a"] this[of "\<sigma> b"] perm 
    show "?p b = ?p a"
    by (simp_all add: pmf_map_inj' permutes_inj) (simp_all add: \<sigma>_def list_succ_def)
qed

lemma sds_R3_a_aux: False
  using lottery_prob_alts'[OF sds_wf[OF R7_wf]] sds_R7_a sds_R7_b by simp

end


lemma sds_R3_a: "pmf (sds R3) a \<le> 1/2"
  using sds_R3_a_aux by force


lemma sds_R8_bc: "pmf (sds R8) b + pmf (sds R8) c = 1/2"
proof (rule antisym)
  have A: "pmf (sds R8) a + pmf (sds R8) b + pmf (sds R8) c + pmf (sds R8) d = 1"
    using lottery_prob_alts'[of "sds R8"] by simp_all

  show "pmf (sds R8) b + pmf (sds R8) c \<le> 1/2"
  proof (rule le_by_contradiction)
    assume B: "pmf (sds R8) b + pmf (sds R8) c > 1/2"
    with B have "sds R1 \<succ>[SD (R8 A3)] sds R8"
      using A pmf_nonneg pmf_nonneg[of "sds R8" d]
      by (auto simp add: eval_SD sds_R1)
    also have "R1 = R8(A3 := R1 A3)"
      unfolding R1_def R8_def by (simp add: prefs_from_table_update)
    finally have "manipulable_profile R8 A3 (R1 A3)"
      unfolding manipulable_profile_def .
    with strategyproof[of R8 A3 "R1 A3"] show False by simp
  qed

  show "pmf (sds R8) b + pmf (sds R8) c \<ge> 1/2"
  proof (rule le_by_contradiction)
    assume B: "pmf (sds R8) b + pmf (sds R8) c < 1/2"
    with B have "sds R2 \<succ>[SD (R8 A4)] sds R8"
      using A pmf_nonneg pmf_nonneg[of "sds R8" d]
      by (auto simp add: eval_SD sds_R2)
    also have "R2 = R8(A4 := R2 A4)"
      unfolding R2_def R8_def by (simp add: prefs_from_table_update)
    finally have "manipulable_profile R8 A4 (R2 A4)"
      unfolding manipulable_profile_def .
    with strategyproof[of R8 A4 "R2 A4"] show False by simp
  qed
qed

lemma sds_R8_b: "pmf (sds R8) b = 1/2 - pmf (sds R8) c"
  using sds_R8_bc by simp

lemma sds_R8_d [simp]: "pmf (sds R8) d = 0"
proof (rule ccontr)
  have A: "pmf (sds R8) a + pmf (sds R8) b + pmf (sds R8) c + pmf (sds R8) d = 1"
    using lottery_prob_alts'[of "sds R8"] by simp_all
  assume "pmf (sds R8) d \<noteq> 0"
  hence pos: "pmf (sds R8) d > 0" using pmf_nonneg[of "sds R8" d] by simp
  hence "sds R2 \<succ>[SD(R8 A4)] sds R8" using sds_R8_bc A
    by (auto simp: eval_SD sds_R2)
  also have "R2 = R8(A4 := R2 A4)"
    unfolding R2_def R8_def by (simp add: prefs_from_table_update)
  finally have "manipulable_profile R8 A4 (R2 A4)"
    unfolding manipulable_profile_def .
  with strategyproof[of R8 A4 "R2 A4"] show False by simp
qed

lemma sds_R8_a [simp]: "pmf (sds R8) a = 1/2"
  using sds_R8_b lottery_prob_alts'[OF sds_wf[OF R8_wf]] by simp

lemma sds_R9_ac: "pmf (sds R9) a + pmf (sds R9) c \<le> 1/2"
proof (rule le_by_contradiction)
  have A: "pmf (sds R9) a + pmf (sds R9) b + pmf (sds R9) c + pmf (sds R9) d = 1"
    using lottery_prob_alts'[of "sds R9"] by simp_all
  assume "pmf (sds R9) a + pmf (sds R9) c > 1/2"
  hence "sds R3 \<succ>[SD(R9 A2)] sds R9" using A sds_R3_a
    by (auto simp: eval_SD sds_R3_b)
  also have "R3 = R9(A2 := R3 A2)"
    unfolding R3_def R9_def by (simp add: prefs_from_table_update)
  finally have "manipulable_profile R9 A2 (R3 A2)"
    unfolding manipulable_profile_def .
  with strategyproof[of R9 A2 "R3 A2"] show False by simp
qed

lemma sds_R9_a_aux: "pmf (sds R9) a \<ge> 1/2"
proof (rule le_by_contradiction)
  have A: "pmf (sds R9) a + pmf (sds R9) b + pmf (sds R9) c + pmf (sds R9) d = 1"
    using lottery_prob_alts'[of "sds R9"] by simp_all
  assume "pmf (sds R9) a < 1/2"
  hence "sds R8 \<succ>[SD(R9 A1)] sds R9" using A sds_R8_a sds_R9_ac pmf_nonneg[of "sds R8" c]
    by (auto simp: eval_SD sds_R8_b)
  also have "R8 = R9(A1 := R8 A1)"
    unfolding R8_def R9_def by (simp add: prefs_from_table_update)
  finally have "manipulable_profile R9 A1 (R8 A1)"
    unfolding manipulable_profile_def .
  with strategyproof[of R9 A1 "R8 A1"] show False by simp
qed

lemma sds_R9_a [simp]: "pmf (sds R9) a = 1/2" 
  and sds_R9_c [simp]: "pmf (sds R9) c = 0"
  using sds_R9_a_aux sds_R9_ac pmf_nonneg[of "sds R9" c] by simp_all

lemma sds_R8_c: "pmf (sds R8) c = 0"
proof (rule ccontr)
  have A: "pmf (sds R9) a + pmf (sds R9) b + pmf (sds R9) c + pmf (sds R9) d = 1"
    using lottery_prob_alts'[of "sds R9"] by simp_all
  assume "pmf (sds R8) c \<noteq> 0"
  hence pos: "pmf (sds R8) c > 0" using pmf_nonneg[of "sds R8" c] by simp
  hence "sds R8 \<succ>[SD(R9 A1)] sds R9" using A sds_R8_a sds_R9_ac pmf_nonneg[of "sds R8" c]
    by (auto simp: eval_SD sds_R8_b)
  also have "R8 = R9(A1 := R8 A1)"
    unfolding R8_def R9_def by (simp add: prefs_from_table_update)
  finally have "manipulable_profile R9 A1 (R8 A1)"
    unfolding manipulable_profile_def .
  with strategyproof[of R9 A1 "R8 A1"] show False by simp
qed

lemma sds_R8: "sds R8 = pmf_of_set {a, b}"
  using sds_R8_c sds_R8_a sds_R8_b
  by (intro lottery_eqI') auto

lemma sds_R10_d [simp]: "pmf (sds R10) d = 0"
proof (rule ex_post_efficient')
  show "d \<prec>[Pareto(R10)] a"
    by (auto simp: Pareto_strict_iff R10_eval agent_iff)
qed simp_all

lemma sds_R10_b [simp]: "pmf (sds R10) b = 1/2"
proof (rule antisym)
  have A: "pmf (sds R10) a + pmf (sds R10) b + pmf (sds R10) c + pmf (sds R10) d = 1"
    using lottery_prob_alts'[of "sds R10"] by simp_all

  show "pmf (sds R10) b \<le> 1/2"
  proof (rule le_by_contradiction)
    assume "pmf (sds R10) b > 1/2"
    hence "sds R10 \<succ>[SD (R8 A2)] sds R8"
      using A pmf_nonneg by (auto simp: eval_SD sds_R8)
    also have "R10 = R8(A2 := R10 A2)"
      unfolding R10_def R8_def by (simp add: prefs_from_table_update)
    finally have "manipulable_profile R8 A2 (R10 A2)"
      unfolding manipulable_profile_def .
    with strategyproof[of R8 A2 "R10 A2"] show False by simp
  qed

  show "pmf (sds R10) b \<ge> 1/2"
  proof (rule le_by_contradiction)
    assume "pmf (sds R10) b < 1/2"
    hence "sds R8 \<succ>[SD (R10 A2)] sds R10"
      using A pmf_nonneg by (auto simp add: eval_SD sds_R8)
    also have "R8 = R10(A2 := R8 A2)"
      unfolding R10_def R8_def by (simp add: prefs_from_table_update)
    finally have "manipulable_profile R10 A2 (R8 A2)"
      unfolding manipulable_profile_def .
    with strategyproof[of R10 A2 "R8 A2"] show False by simp
  qed
qed

lemma sds_R10_a: "pmf (sds R10) a = 1/2 - pmf (sds R10) c"
  using lottery_prob_alts'[OF sds_wf[OF R10_wf]] by simp

lemma sds_R11_d [simp]: "pmf (sds R11) d = 0"
proof (rule ex_post_efficient')
  show "d \<prec>[Pareto(R11)] a"
    by (auto simp: Pareto_strict_iff R11_eval agent_iff)
qed simp_all

lemma sds_R11_b: "pmf (sds R11) b \<ge> 1/2"
proof (rule le_by_contradiction)
  have A: "pmf (sds R11) a + pmf (sds R11) b + pmf (sds R11) c + pmf (sds R11) d = 1"
    using lottery_prob_alts'[of "sds R11"] by simp_all
  assume "pmf (sds R11) b < 1/2"
  hence "sds R11 \<succ>[SD (R10 A1)] sds R10"
    using A by (auto simp add: eval_SD sds_R10_a)
  also have "R11 = R10(A1 := R11 A1)"
    unfolding R10_def R11_def by (simp add: prefs_from_table_update)
  finally have "manipulable_profile R10 A1 (R11 A1)"
    unfolding manipulable_profile_def .
  with strategyproof[of R10 A1 "R11 A1"] show False by simp
qed

lemma sds_R12_d [simp]: "pmf (sds R12) d = 0"
proof (rule ex_post_efficient')
  show "d \<prec>[Pareto(R12)] a"
    by (auto simp: Pareto_strict_iff R12_eval agent_iff)
qed simp_all

lemma sds_R12_b [simp]: "pmf (sds R12) b = pmf (sds R12) c"
proof -
  def \<pi> \<equiv> "lists_succ [[A1,A2],[A3],[A4]]" and \<sigma> \<equiv> "lists_succ [[a],[b,c],[d]]"
  let ?p = "pmf (sds R12)"
  have perm: "\<pi> permutes agents" "\<sigma> permutes alts"
    by (simp_all add: \<pi>_def \<sigma>_def lists_succ_permutes' distincts_Cons agents alts insert_commute)
  have R12_eq: "R12 = (permute_profile \<sigma> R12 \<circ> \<pi>)"
    by (simp add: R12_def \<sigma>_def \<pi>_def eval_profile_permutation)
  from perm have "pmf (map_pmf \<sigma> (sds R12)) x = pmf (sds R12) x" for x
    by (subst R12_eq) (simp add: anonymous neutral perm pref_profile_wf.wf_permute_alts)
  from this[of "\<sigma> b"] perm show "?p b = ?p c"
    by (simp_all add: pmf_map_inj' permutes_inj) (simp_all add: \<sigma>_def list_succ_def)
qed

lemma sds_R12_b_le_sds_R11_b:
  "pmf (sds R12) b \<le> pmf (sds R11) b"
proof -
  from lottery_prob_alts'[OF sds_wf[OF R12_wf]] pmf_nonneg[of "sds R12" a]
    have "pmf (sds R12) b \<le> 1/2" by simp
  also from sds_R11_b have "1/2 \<le> pmf (sds R11) b" .
  finally show ?thesis .
qed

lemma sds_R12_c_eq_sds_R11_c: "pmf (sds R12) c = pmf (sds R11) c"
proof (rule antisym)
  have A: "pmf (sds R11) a + pmf (sds R11) b + pmf (sds R11) c + pmf (sds R11) d = 1"
          "pmf (sds R12) a + pmf (sds R12) b + pmf (sds R12) c + pmf (sds R12) d = 1"
    using lottery_prob_alts'[of "sds R11"] lottery_prob_alts'[of "sds R12"] 
    by simp_all

  show "pmf (sds R12) c \<ge> pmf (sds R11) c"
  proof (rule le_by_contradiction)
    assume "pmf (sds R12) c < pmf (sds R11) c"
    hence "sds R11 \<succ>[SD (R12 A1)] sds R12"
      using A sds_R12_b_le_sds_R11_b by (auto simp add: eval_SD)
    also have "R11 = R12(A1 := R11 A1)"
      unfolding R11_def R12_def by (simp add: prefs_from_table_update)
    finally have "manipulable_profile R12 A1 (R11 A1)"
      unfolding manipulable_profile_def .
    with strategyproof[of R12 A1 "R11 A1"] show False by simp
  qed

  show "pmf (sds R12) c \<le> pmf (sds R11) c"
  proof (rule le_by_contradiction)
    assume "pmf (sds R12) c > pmf (sds R11) c"
    hence "sds R12 \<succ>[SD (R11 A1)] sds R11"
      using A sds_R12_b_le_sds_R11_b by (auto simp add: eval_SD)
    also have "R12 = R11(A1 := R12 A1)"
      unfolding R11_def R12_def by (simp add: prefs_from_table_update)
    finally have "manipulable_profile R11 A1 (R12 A1)"
      unfolding manipulable_profile_def .
    with strategyproof[of R11 A1 "R12 A1"] show False by simp
  qed
qed

lemma sds_R12_a_le_sds_R11_a: "pmf (sds R12) a \<le> pmf (sds R11) a"
proof (rule le_by_contradiction)
  have A: "pmf (sds R11) a + pmf (sds R11) b + pmf (sds R11) c + pmf (sds R11) d = 1"
          "pmf (sds R12) a + pmf (sds R12) b + pmf (sds R12) c + pmf (sds R12) d = 1"
    using lottery_prob_alts'[of "sds R11"] lottery_prob_alts'[of "sds R12"] 
    by simp_all
  assume "pmf (sds R12) a > pmf (sds R11) a"
  
  hence "sds R12 \<succ>[SD (R11 A1)] sds R11"
    using A sds_R12_b_le_sds_R11_b sds_R12_c_eq_sds_R11_c by (auto simp add: eval_SD)
  also have "R12 = R11(A1 := R12 A1)"
    unfolding R11_def R12_def by (simp add: prefs_from_table_update)
  finally have "manipulable_profile R11 A1 (R12 A1)"
    unfolding manipulable_profile_def .
  with strategyproof[of R11 A1 "R12 A1"] show False by simp
qed

lemma sds_R12: "sds R12 = pmf_of_set {b, c}"
  using sds_R12_a_le_sds_R11_a sds_R12_c_eq_sds_R11_c sds_R11_b
        pmf_nonneg[of "sds R12" a] lottery_prob_alts'[of "sds R11"]
        lottery_prob_alts'[of "sds R12"]
  by (intro lottery_eqI') auto

lemma rd_R13: "RD R13 = pmf_of_multiset {#a,b,b,c#}"
  by (simp add: random_dictatorship_unique_favorites' R13_eval mset_agents add_ac)  

lemma sds_R13_d [simp]: "pmf (sds R13) d = 0"
proof (rule ex_post_efficient')
  show "d \<prec>[Pareto(R13)] a"
    by (auto simp: Pareto_strict_iff R13_eval agent_iff)
qed simp_all

lemma sds_R13: "sds R13 = pmf_of_multiset {#a,b,b,c#}"
  sorry

lemma no_such_sds: False
proof -
  have "sds R12 \<succ>[SD(R13 A4)] sds R13"
    using sds_R12 sds_R13 sds_wf[OF R13_wf] by (simp add: eval_SD)
  also have "R12 = R13(A4 := R12 A4)"
    unfolding R12_def R13_def by (simp add: prefs_from_table_update)
  finally have "manipulable_profile R13 A4 (R12 A4)"
    unfolding manipulable_profile_def .
  with strategyproof[of R13 A4 "R12 A4"] show False by simp
qed

end



subsection \<open>Lifting to more than 4 agents and alternatives\<close>

lemma finite_list':
  assumes "finite A"
  obtains xs where "A = set xs" "distinct xs" "length xs = card A"
proof -
  from assms obtain xs where "set xs = A" using finite_list by blast
  thus ?thesis using distinct_card[of "remdups xs"]
    by (intro that[of "remdups xs"]) simp_all
qed

lemma finite_list_subset:
  assumes "finite A" "card A \<ge> n"
  obtains xs where "set xs \<subseteq> A" "distinct xs" "length xs = n"
proof -
  obtain xs where "A = set xs" "distinct xs" "length xs = card A"
    using finite_list'[OF assms(1)] by blast
  with assms show ?thesis
    by (intro that[of "take n xs"]) (simp_all add: set_take_subset)
qed

lemma card_ge_4E:
  assumes "finite A" "card A \<ge> 4"
  obtains a b c d where "distinct [a,b,c,d]" "{a,b,c,d} \<subseteq> A"
proof -
  from finite_list_subset[OF assms] guess xs .
  moreover then obtain a b c d where "xs = [a, b, c, d]" 
    by (auto simp: eval_nat_numeral length_Suc_conv)
  ultimately show ?thesis by (intro that[of a b c d]) simp_all
qed

context sds_impossibility
begin

(* 
  TODO: This proof could be generalised to show that any SDS with these properties
  can be lowered to one on a smaller set of agents/alternatives.
*)
lemma no_such_sds: False
proof -
  from card_ge_4E[OF finite_agents agents_ge_4] guess A1 A2 A3 A4 .
  note agents = this
  from card_ge_4E[OF finite_alts alts_ge_4] guess a b c d .
  note alts = this
  def agents' \<equiv> "{A1,A2,A3,A4}" and alts' \<equiv> "{a,b,c,d}"
  have agents'_subset: "agents' \<subseteq> agents" and alts'_subset: "alts' \<subseteq> alts"
    unfolding agents'_def alts'_def using alts agents by auto

  def lift \<equiv> "\<lambda>R i x y. x \<in> alts \<and> y \<in> alts \<and> i \<in> agents \<and>
                 (x = y \<or> x \<notin> alts' \<or> i \<notin> agents' \<or> (y \<in> alts' \<and> R i x y))"
  def sds' \<equiv> "sds \<circ> lift"

  have lift_wf [simp, intro]: "is_pref_profile (lift R)" 
     if "pref_profile_wf agents' alts' R" for R
  proof
    fix i assume i: "i \<in> agents"
    from that interpret pref_profile_wf agents' alts' R .
    show "complete_preorder_on alts (lift R i)"
    proof (cases "i \<in> agents'")
      assume "i \<notin> agents'"
      with i show ?thesis by unfold_locales (simp_all add: lift_def)
    next
      assume "i \<in> agents'"
      then interpret R: complete_preorder_on alts' "R i" by simp
      from i show "complete_preorder_on alts (lift R i)"
        by unfold_locales (insert R.complete, auto simp: R.refl lift_def intro: R.trans) 
    qed
  next
    fix i assume "i \<notin> agents"
    with agents'_subset show "lift R i = (\<lambda>_ _. False)"
      by (intro ext) (simp add: lift_def)
  qed

  interpret SDS': agenda agents' alts'
    using agents alts by unfold_locales (simp_all add: agents'_def alts'_def)

  have lift_lottery [simp]: "p \<in> lotteries" if "p \<in> SDS'.lotteries" for p
    using that alts'_subset by (auto simp: lotteries_on_def)

  interpret SDS': social_decision_scheme agents' alts' sds'
  proof
    fix R assume R_wf: "SDS'.is_pref_profile R"
    then interpret R: pref_profile_wf agents' alts' R .
    from R_wf interpret R': pref_profile_wf agents alts "lift R" by simp
    have "pmf (sds' R) x = 0" if x: "x \<in> alts - alts'" for x
      unfolding sds'_def o_def
    proof (rule ex_post_efficient'[OF _ R'.Pareto_strictI'])
      fix i assume "i \<in> agents"
      with alts x show "a \<succeq>[lift R i] x"
        by (auto simp: lift_def alts'_def)
    next
      from alts x show "\<not>x \<succeq>[lift R A1] a" by (auto simp: lift_def agents'_def alts'_def)
    qed (insert R_wf x alts agents, simp_all)
    moreover have "sds' R \<in> lotteries" unfolding sds'_def o_def
      by (intro sds_wf lift_wf R_wf)
    ultimately show "sds' R \<in> SDS'.lotteries"
      by (auto simp: lotteries_on_def set_pmf_eq)
  qed

  interpret anonymous_sds agents' alts' sds'
  proof
    fix \<pi> R assume perm: "\<pi> permutes agents'" and R_wf: "SDS'.is_pref_profile R"
    from perm agents'_subset have perm': "\<pi> permutes agents" by (rule permutes_subset)
    from perm perm' have "lift (R \<circ> \<pi>) = lift R \<circ> \<pi>"
      using agents'_subset by (intro ext) (auto simp: lift_def permutes_in_image)
    hence "sds (lift (R \<circ> \<pi>)) = sds (lift R \<circ> \<pi>)" by simp
    also from perm R_wf have "\<pi> permutes agents" "is_pref_profile (lift R)"
      using agents'_subset by (auto dest: permutes_subset)
    from anonymous[OF this] have "sds (lift R \<circ> \<pi>) = sds (lift R)"
      by (simp add: sds'_def)
    finally show "sds' (R \<circ> \<pi>) = sds' R" unfolding sds'_def o_def .
  qed

  interpret neutral_sds agents' alts' sds'
  proof
    fix \<sigma> R assume perm: "\<sigma> permutes alts'" and R_wf: "SDS'.is_pref_profile R"
    from perm have perm': "\<sigma> permutes alts"
      using alts'_subset by (blast dest: permutes_subset)
    have inj: "inj (inv \<sigma>)" using permutes_inj permutes_inv perm' by blast

    have "lift (permute_profile \<sigma> R) = permute_profile \<sigma> (lift R)"
      using alts'_subset permutes_inv[OF perm] permutes_inv[OF perm'] inj
      by (intro ext) (auto simp: lift_def permutes_in_image permute_profile_def dest: injD)
    hence "sds (lift (permute_profile \<sigma> R)) = sds (permute_profile \<sigma> (lift R))" by simp
    also from R_wf have "is_pref_profile (lift R)" by simp
    from neutral[OF perm' this] 
      have "sds (permute_profile \<sigma> (lift R)) = map_pmf \<sigma> (sds (lift R))" .
    finally show "sds' (permute_profile \<sigma> R) = map_pmf \<sigma> (sds' R)"
      by (simp add: sds'_def o_def)
  qed

  have lift_preferred_alts: "preferred_alts (lift R i) x = 
       (if i \<in> agents' \<and> x \<in> alts' then SDS'.preferred_alts (R i) x else alts)"
    if "i \<in> agents" "x \<in> alts" "SDS'.is_pref_profile R" for R i x
  proof (cases "i \<in> agents'")
    from that interpret pref_profile_wf agents' alts' R by simp
    assume i: "i \<in> agents'"
    then interpret Ri: complete_preorder_on alts' "R i"
      using that by simp
    show ?thesis
    using i that alts'_subset Ri.not_outside
      by (auto simp: SDS'.preferred_alts_def preferred_alts_def lift_def Ri.refl)
  qed (auto simp: preferred_alts_def SDS'.preferred_alts_def lift_def that)

  interpret SDS': sd_efficient_sds agents' alts' sds'
  proof (unfold_locales, unfold SDS'.SD_efficient_def, safe)
    fix R q i 
    assume R_wf: "SDS'.is_pref_profile R" and q: "q \<in> SDS'.lotteries"
    assume i: "i \<in> agents'"
    assume weak: "\<forall>i\<in>agents'. q \<succeq>[SD(R i)] sds' R"
    assume strong: "q \<succ>[SD(R i)] sds' R"
    interpret R: pref_profile_wf agents' alts' R by fact
    from R_wf interpret R': pref_profile_wf agents alts "lift R" by simp

    have pmf_zero: "pmf (sds' R) x = 0" if x: "x \<notin> alts'" for x
      using x SDS'.sds_wf[OF R_wf]
      by (auto simp: lotteries_on_def set_pmf_eq lift_def)

    from SD_efficient have "SD_efficient (lift R) (sds' R)" unfolding sds'_def o_def
      using R_wf by simp
    moreover have "q \<in> lotteries" using q by simp
    moreover have "q \<succeq>[SD(lift R i)] sds' R" if i: "i \<in> agents" for i
    proof (cases "i \<in> agents'")
      assume i: "i \<in> agents'"
      with agents'_subset have [simp]: "i \<in> agents" by blast
      show ?thesis
      proof (rule SD_agendaI) 
        show "complete_preorder_on alts (lift R i)" by simp
        fix x assume x: "x \<in> alts"
        show "SDS'.lottery_prob (sds' R) (preferred_alts (lift R i) x)
                \<le> SDS'.lottery_prob q (preferred_alts (lift R i) x)"
        using i bspec[OF weak i] agents'_subset R_wf x
        by (subst (asm) SDS'.SD_agenda, cases "x \<in> alts'") 
           (auto simp: lift_preferred_alts lottery_prob_alts)
      qed (auto simp: SDS'.sds_wf R_wf q)
    next
      assume i': "i \<notin> agents'"
      from i have "complete_preorder_on alts (lift R i)" by simp
      with i' agents'_subset i q R_wf show ?thesis
        by (intro SD_agendaI)
           (auto intro!: SDS'.sds_wf lift_lottery simp: lift_def preferred_alts_def lottery_prob_alts)
    qed
    moreover have "\<exists>i\<in>agents. \<not>(q \<preceq>[SD(lift R i)] sds' R)"
    proof
      from i agents'_subset show i': "i \<in> agents" by blast
      from i interpret R: complete_preorder_on alts' "R i"
        using R_wf by (simp add: i)
      from strong have "\<not>(q \<preceq>[SD(R i)] sds' R)" 
        by (simp add: strongly_preferred_def)
      then obtain x where x: "x \<in> alts'" and
         "SDS'.lottery_prob (sds' R) (SDS'.preferred_alts (R i) x)
           < SDS'.lottery_prob q (SDS'.preferred_alts (R i) x)"
        using q i R_wf by (subst (asm) SDS'.SD_agenda) (auto intro!: SDS'.sds_wf)
      moreover from x alts'_subset have "x \<in> alts" by blast
      ultimately show "\<not>(q \<preceq>[SD(lift R i)] sds' R)"
        using q i R_wf alts'_subset agents'_subset
        by (subst SD_agenda) 
           (auto intro!: bexI[of _ x] SDS'.sds_wf simp: lift_preferred_alts not_le)
    qed
    ultimately show False by (rule SD_efficientD)
  qed

  interpret strategyproof_sds agents' alts' sds'
  proof (unfold_locales, safe)
    fix R i Ri'
    assume R_wf: "SDS'.is_pref_profile R" and i: "i \<in> agents'"
    assume Ri': "complete_preorder_on alts' Ri'"
    assume manipulable: "SDS'.manipulable_profile R i Ri'"
    from i agents'_subset have i': "i \<in> agents" by blast
    interpret R: pref_profile_wf agents' alts' R by fact
    from R_wf interpret liftR: pref_profile_wf agents alts "lift R" by simp
   
    def lift_Ri' \<equiv> "\<lambda>x y. x \<in> alts \<and> y \<in> alts \<and> (x = y \<or> x \<notin> alts' \<or> (y \<in> alts' \<and> Ri' x y))"
    def S \<equiv> "(lift R)(i := lift_Ri')"
    from Ri' interpret Ri': complete_preorder_on alts' Ri' .
    have [simp]: "complete_preorder_on alts lift_Ri'" using Ri'.complete
      by unfold_locales (auto simp: lift_Ri'_def intro: Ri'.trans)
    from lift_wf[OF R_wf] Ri' i agents'_subset have [simp]: "sds S \<in> lotteries" 
      by (auto intro!: sds_wf simp: S_def pref_profile_wf_def)

    have "manipulable_profile (lift R) i lift_Ri'"
    proof -
      from manipulable have "sds (lift R) \<prec>[SD (R i)] sds (lift (R(i := Ri')))" 
        unfolding SDS'.manipulable_profile_def unfolding sds'_def o_def .
      also from i agents'_subset have "lift (R(i := Ri')) = S"
        by (intro ext) (auto simp: lift_def lift_Ri'_def S_def)
      finally show ?thesis using i i' Ri' alts'_subset R_wf
        unfolding manipulable_profile_def S_def [symmetric] strongly_preferred_def
          by (subst (1 2) SD_agenda, simp only: liftR.prefs_wf',
              subst (asm) (1 2) SDS'.SD_agenda, simp only: R.prefs_wf')
             (auto simp: lottery_prob_alts lift_preferred_alts strongly_preferred_def)
    qed
    moreover from R_wf i agents'_subset
      have "\<not>manipulable_profile (lift R) i lift_Ri'"
      by (intro strategyproof) auto
    ultimately show False by contradiction
  qed

  interpret sds_impossibility_4_4 agents' alts' sds' A1 A2 A3 A4 a b c d
    by unfold_locales (insert agents alts, simp_all add: agents'_def alts'_def)

  from no_such_sds show False .
qed

end

end

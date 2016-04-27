theory SDS_Impossibility_Definitions
imports Social_Decision_Schemes
begin

locale sds_impossibility = 
  anonymous_sds agents alts sds +
  neutral_sds agents alts sds +
  sd_efficient_sds agents alts sds +
  strategyproof_sds agents alts sds
  for agents :: "'agent set" and alts :: "'alt set" and sds +
  assumes agents_ge_4: "card agents \<ge> 4"
      and alts_ge_4:   "card alts \<ge> 4"

locale sds_impossibility_4_4 = sds_impossibility agents alts sds
  for agents :: "'agent set" and alts :: "'alt set" and sds +
  fixes A1 A2 A3 A4 :: 'agent and a b c d :: 'alt
  assumes distinct_agents: "distinct [A1, A2, A3, A4]"
      and distinct_alts: "distinct [a, b, c, d]"
      and agents: "agents = {A1, A2, A3, A4}"
      and alts:   "alts   = {a, b, c, d}"
begin

lemma an_sds: "an_sds agents alts sds" by unfold_locales
lemma ex_post_efficient_sds: "ex_post_efficient_sds agents alts sds" by unfold_locales
lemma sd_efficient_sds: "sd_efficient_sds agents alts sds" by unfold_locales
lemma strategyproof_an_sds: "strategyproof_an_sds agents alts sds" by unfold_locales

lemma distinct_agents' [simp]: 
  "A1 \<noteq> A2" "A1 \<noteq> A3" "A1 \<noteq> A4" "A2 \<noteq> A1" "A2 \<noteq> A3" "A2 \<noteq> A4" 
  "A3 \<noteq> A1" "A3 \<noteq> A2" "A3 \<noteq> A4" "A4 \<noteq> A1" "A4 \<noteq> A2" "A4 \<noteq> A3"
  using distinct_agents by auto
  
lemma distinct_alts' [simp]:
  "a \<noteq> b" "a \<noteq> c" "a \<noteq> d" "b \<noteq> a" "b \<noteq> c" "b \<noteq> d" 
  "c \<noteq> a" "c \<noteq> b" "c \<noteq> d" "d \<noteq> a" "d \<noteq> b" "d \<noteq> c"
  using distinct_alts by auto

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

lemma total_preorder_on_altsI [simp]:
  "is_pref_profile R \<Longrightarrow> i \<in> agents \<Longrightarrow> total_preorder_on alts (R i)"
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

end

end
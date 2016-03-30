theory SD_Inefficiency
imports Complex_Main Preference_Profiles Stochastic_Dominance
begin

lemma pmf_not_neg [simp]: "\<not>pmf p x < 0"
  by (simp add: not_less pmf_nonneg)

lemma set_pmf_eq': "set_pmf p = {x. pmf p x > 0}"
proof safe
  fix x assume "x \<in> set_pmf p"
  hence "pmf p x \<noteq> 0" by (auto simp: set_pmf_eq)
  with pmf_nonneg[of p x] show "pmf p x > 0" by simp
qed (auto simp: set_pmf_eq)


lemma setsum_pmf_eq_1:
  assumes "finite A" "set_pmf p \<subseteq> A"
  shows   "(\<Sum>x\<in>A. pmf p x) = 1"
proof -
  have "(\<Sum>x\<in>A. pmf p x) = measure_pmf.prob p A"
    by (simp add: measure_measure_pmf_finite assms)
  also from assms have "\<dots> = 1"
    by (subst measure_pmf.prob_eq_1) (auto simp: AE_measure_pmf_iff)
  finally show ?thesis .
qed

context pref_profile_wf
begin

lemma SD_inefficient_support_subset:
  assumes inefficient: "\<not>SD_efficient R p'"
  assumes support: "set_pmf p' \<subseteq> set_pmf p"
  assumes lotteries: "p \<in> lotteries_on alts"
  shows   "\<not>SD_efficient R p"
proof -
  from assms have p'_wf: "p' \<in> lotteries_on alts" by (simp add: lotteries_on_def)
  from inefficient obtain q' i where q': "q' \<in> lotteries_on alts" "i \<in> agents"
    "\<And>i. i \<in> agents \<Longrightarrow> q' \<succeq>[SD(R i)] p'" "q' \<succ>[SD(R i)] p'" 
    unfolding SD_efficient_def by blast

  have subset: "{x. pmf p' x > pmf q' x} \<subseteq> set_pmf p'" by (auto simp: set_pmf_eq)
  also have "\<dots> \<subseteq> set_pmf p" by fact
  also have "\<dots> \<subseteq> alts" using lotteries by (simp add: lotteries_on_def)
  finally have finite: "finite {x. pmf p' x > pmf q' x}" 
    using finite_alts by (rule finite_subset)

  def \<epsilon> \<equiv> "Min (insert 1 {pmf p x / (pmf p' x - pmf q' x) |x. pmf p' x > pmf q' x})"
  def supp \<equiv> "set_pmf p \<union> set_pmf q'"
  from lotteries finite_alts q'(1) have finite_supp: "finite supp"
    by (auto simp: lotteries_on_def supp_def dest: finite_subset)
  from support have [simp]: "pmf p x = 0" "pmf p' x = 0" "pmf q' x = 0" if "x \<notin> supp" for x
    using that by (auto simp: supp_def set_pmf_eq)

  from finite support subset have \<epsilon>: "\<epsilon> > 0" unfolding \<epsilon>_def 
    by (intro Min_grI) (auto simp: field_simps set_pmf_eq')
  have nonneg: "pmf p x + \<epsilon> * (pmf q' x - pmf p' x) \<ge> 0" for x
  proof (cases "pmf p' x > pmf q' x")
    case True
    with finite have "\<epsilon> \<le> pmf p x / (pmf p' x - pmf q' x)"
      unfolding \<epsilon>_def by (intro Min_le) auto
    with True show ?thesis by (simp add: field_simps)
  next
    case False
    with pmf_nonneg[of p x] \<epsilon> show ?thesis by simp
  qed

  def q \<equiv> "embed_pmf (\<lambda>x. pmf p x + \<epsilon> * (pmf q' x - pmf p' x))"
  have "(\<integral>\<^sup>+ x. ereal (pmf p x + \<epsilon> * (pmf q' x - pmf p' x)) \<partial>count_space UNIV) = 1"
  proof (subst nn_integral_count_space')
    have "(\<Sum>x\<in>supp. ereal (pmf p x + \<epsilon> * (pmf q' x - pmf p' x))) = 
            ereal ((\<Sum>x\<in>supp. pmf p x) + \<epsilon> * ((\<Sum>x\<in>supp. pmf q' x) - (\<Sum>x\<in>supp. pmf p' x)))"
      by (simp add: setsum.distrib setsum_right_distrib setsum_subtractf ring_distribs)
    also from finite_supp support have "\<dots> = 1"
      by (subst (1 2 3) setsum_pmf_eq_1) (auto simp: supp_def)
    finally show "(\<Sum>x\<in>supp. ereal (pmf p x + \<epsilon> * (pmf q' x - pmf p' x))) = 1" .
  qed (insert nonneg finite_supp, simp_all)
  with nonneg have pmf_q: "pmf q x = pmf p x + \<epsilon> * (pmf q' x - pmf p' x)" for x
    unfolding q_def by (intro pmf_embed_pmf) simp_all
  with support have "set_pmf q \<subseteq> supp" 
    unfolding supp_def by (auto simp: set_pmf_eq)
  
  with lotteries support q'(1) have support_q: "set_pmf q \<subseteq> supp"
    by (auto simp add: lotteries_on_def supp_def)
  with lotteries support q'(1) have q_wf: "q \<in> lotteries_on alts"
    by (auto simp add: lotteries_on_def supp_def)
  
  from support_q support have expected_utility:
    "measure_pmf.expectation q u = measure_pmf.expectation p u + 
         \<epsilon> * (measure_pmf.expectation q' u - measure_pmf.expectation p' u)" for u
    by (subst (1 2 3 4) integral_measure_pmf[OF finite_supp])
       (auto simp: pmf_q supp_def setsum.distrib setsum_right_distrib 
                   setsum_left_distrib setsum_subtractf algebra_simps)
  
  have "q \<succeq>[SD(R i)] p" if i: "i \<in> agents" for i
  proof -
    from i interpret finite_complete_preorder_on alts "R i" by simp
    from i lotteries q'(1) q'(3)[OF i] q_wf p'_wf \<epsilon> show ?thesis
      by (fastforce simp: SD_iff_expected_utilities_le expected_utility)
  qed
  moreover from \<open>i \<in> agents\<close> interpret finite_complete_preorder_on alts "R i" by simp
    from lotteries q'(1,4) q_wf p'_wf \<epsilon> have "q \<succ>[SD(R i)] p"
    by (force simp: SD_iff_expected_utilities_le expected_utility not_le strongly_preferred_def)
  ultimately show ?thesis using q_wf \<open>i \<in> agents\<close> unfolding SD_efficient_def by blast
qed

lemma SD_efficient_support_subset:
  assumes "SD_efficient R p" "set_pmf p' \<subseteq> set_pmf p" "p \<in> lotteries_on alts"
  shows   "SD_efficient R p'"
  using SD_inefficient_support_subset[OF _ assms(2,3)] assms(1) by blast

lemma SD_efficient_same_support:
  assumes "set_pmf p = set_pmf p'" "p \<in> lotteries_on alts"
  shows   "SD_efficient R p \<longleftrightarrow> SD_efficient R p'"
  using SD_inefficient_support_subset[of p p'] SD_inefficient_support_subset[of p' p] assms
  by (auto simp: lotteries_on_def)  

lemma SD_efficient_iff:
  assumes "p \<in> lotteries_on alts"
  shows   "SD_efficient R p \<longleftrightarrow> SD_efficient R (pmf_of_set (set_pmf p))"
  using assms finite_alts
  by (intro SD_efficient_same_support)
     (simp, subst set_pmf_of_set,
      auto simp: set_pmf_not_empty lotteries_on_def intro: finite_subset[OF _ finite_alts])

end


(*

definition lottery_lists_on :: "'a list \<Rightarrow> real list set" where
  "lottery_lists_on xs = 
     {ys. length ys = length xs \<and> list_all (op \<le> 0) ys \<and> listsum ys = 1}"

(*
lemma "\<exists>p\<in>lotteries_on {a,b,c,d}. P p"
apply (simp only: set_simps [symmetric]) *)

lemma pmf_of_list_lottery:
  assumes "ys \<in> lottery_lists_on xs"
  shows   "pmf_of_list (zip xs ys) \<in> lotteries_on (set xs)"
unfolding lotteries_on_def
proof
  from assms have "set_pmf (pmf_of_list (zip xs ys)) \<subseteq> set (map fst (zip xs ys))"
    by (intro set_pmf_of_list pmf_of_list_wfI) (auto simp: list_all_def lottery_lists_on_def)
  also from assms have "map fst (zip xs ys) = xs" by (simp add: lottery_lists_on_def)
  finally show "set_pmf (pmf_of_list (zip xs ys)) \<subseteq> set xs" .
qed

lemma Bex_lotteries_on_setI:
  assumes "\<exists>ys\<in>lottery_lists_on xs. P (pmf_of_list (zip xs ys))"
  shows   "\<exists>p\<in>lotteries_on (set xs). P p"
proof -
  from assms guess ys .. note ys = this
  def p \<equiv> "pmf_of_list (zip xs ys)"
  from ys have "p \<in> lotteries_on (set xs)" "P p" unfolding p_def
    by (simp_all add: pmf_of_list_lottery)
  thus ?thesis ..
qed  



context agenda
begin

definition inefficient_support_witness :: 
    "('agent, 'alt) pref_profile \<Rightarrow> 'alt lottery \<Rightarrow> 'alt lottery \<Rightarrow> bool" where
  "inefficient_support_witness R p wit \<longleftrightarrow>
     p \<in> lotteries \<and> wit \<in> lotteries \<and> 
     (\<forall>i\<in>agents. wit \<succeq>[SD(R i)] p) \<and> (\<exists>i\<in>agents. wit \<succ>[SD(R i)] p)"

lemma inefficient_support_witnessI:
  assumes "p \<in> lotteries" "wit \<in> lotteries"

*)

end

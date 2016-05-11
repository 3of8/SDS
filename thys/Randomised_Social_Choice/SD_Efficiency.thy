(*  
  Title:    SD_Efficiency.thy
  Author:   Manuel Eberl, TU München

  Characterisation of SD-efficiency.
*)

theory SD_Efficiency
imports Complex_Main Preference_Profiles Missing_PMF Stochastic_Dominance
begin

(* 
  TODO: Perhaps a general concept of "efficiency" can be introduced, 
  parametrised over the way in which two lotteries are compared.
*)

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
    unfolding SD_efficient_def' by blast

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
  with support have support_q: "set_pmf q \<subseteq> supp" 
    unfolding supp_def by (auto simp: set_pmf_eq)
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
    from i interpret finite_total_preorder_on alts "R i" by simp
    from i lotteries q'(1) q'(3)[OF i] q_wf p'_wf \<epsilon> show ?thesis
      by (fastforce simp: SD_iff_expected_utilities_le expected_utility)
  qed
  moreover from \<open>i \<in> agents\<close> interpret finite_total_preorder_on alts "R i" by simp
    from lotteries q'(1,4) q_wf p'_wf \<epsilon> have "q \<succ>[SD(R i)] p"
    by (force simp: SD_iff_expected_utilities_le expected_utility not_le strongly_preferred_def)
  ultimately show ?thesis using q_wf \<open>i \<in> agents\<close> unfolding SD_efficient_def' by blast
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

lemma SD_efficient_no_pareto_loser:
  assumes efficient: "SD_efficient R p" and p_wf: "p \<in> lotteries_on alts"
  shows   "set_pmf p \<inter> pareto_losers R = {}"
proof -
  have "x \<notin> pareto_losers R" if x: "x \<in> set_pmf p" for x
  proof -
    from x have "set_pmf (return_pmf x) \<subseteq> set_pmf p" by auto
    from efficient this p_wf have "SD_efficient R (return_pmf x)"
      by (rule SD_efficient_support_subset)
    moreover from assms x have "x \<in> alts" by (auto simp: lotteries_on_def)
    ultimately show "x \<notin> pareto_losers R" by (simp add: SD_efficient_singleton_iff)
  qed
  thus ?thesis by blast
qed


(*
lemma pmf_neq_exists_less:
  assumes "(p :: 'a pmf) \<noteq> q"
  shows   "\<exists>x. pmf p x < pmf q x"
proof (rule ccontr)
  assume "\<not>(\<exists>x. pmf p x < pmf q x)"
  hence ge: "pmf p x \<ge> pmf q x" for x by (auto simp: not_less)
  from assms obtain x where "pmf p x \<noteq> pmf q x" by (auto simp: pmf_eq_iff)
  with ge[of x] have gt: "pmf p x > pmf q x" by simp
  have "1 = measure (measure_pmf q) UNIV" by simp
  also have "\<dots> = measure (measure_pmf q) {x} + measure (measure_pmf q) (UNIV - {x})"
    by (subst measure_pmf.finite_measure_Union [symmetric]) simp_all
  also from gt have "measure (measure_pmf q) {x} < measure (measure_pmf p) {x}" 
    by (simp add: measure_pmf_single)
  also have "measure (measure_pmf q) (UNIV - {x}) \<le> measure (measure_pmf p) (UNIV - {x})"
    by (subst (1 2) integral_pmf [symmetric]) 
       (intro integral_mono integrable_pmf, simp_all add: ge)
  also have "measure (measure_pmf p) {x} + \<dots> = 1"
    by (subst measure_pmf.finite_measure_Union [symmetric]) simp_all
  finally show False by simp_all
qed

lemma
  assumes "p \<in> lotteries_on alts" "q \<in> lotteries_on alts" "q \<succ>[Pareto(SD \<circ> R)] p"
  obtains r where "r \<in> lotteries_on alts" "r \<succ>[Pareto(SD \<circ> R)] p" "set_pmf r \<subset> set_pmf p"
proof -
  have subset: "{x. pmf p x > pmf q x} \<subseteq> set_pmf p" by (auto simp: set_pmf_eq)
  also have "\<dots> \<subseteq> alts" using assms by (simp add: lotteries_on_def)
  finally have finite: "finite {x. pmf p x > pmf q x}" 
    using finite_alts by (rule finite_subset)

  from assms have "q \<noteq> p" by (auto simp: strongly_preferred_def)
  hence ex_less: "\<exists>x. pmf p x > pmf q x" by (rule pmf_neq_exists_less)

  def \<epsilon> \<equiv> "Min {pmf p x / (pmf p x - pmf q x) |x. pmf p x > pmf q x}"
  def supp \<equiv> "set_pmf p \<union> set_pmf q"
  from assms finite_alts have finite_supp: "finite supp"
    by (auto simp: lotteries_on_def supp_def dest: finite_subset)
  have [simp]: "pmf p x = 0" "pmf q x = 0" if "x \<notin> supp" for x
    using that by (auto simp: supp_def set_pmf_eq)

  from finite subset ex_less have \<epsilon>: "\<epsilon> > 0" unfolding \<epsilon>_def 
    by (intro Min_grI) (auto simp: field_simps set_pmf_eq')
  have nonneg: "pmf p x + \<epsilon> * (pmf q x - pmf p x) \<ge> 0" for x
  proof (cases "pmf p x > pmf q x")
    case True
    with finite have "\<epsilon> \<le> pmf p x / (pmf p x - pmf q x)"
      unfolding \<epsilon>_def by (intro Min_le) auto
    with True show ?thesis by (simp add: field_simps)
  next
    case False
    with pmf_nonneg[of p x] \<epsilon> show ?thesis by simp
  qed

  def r \<equiv> "embed_pmf (\<lambda>x. pmf p x + \<epsilon> * (pmf q x - pmf p x))"
  have "(\<integral>\<^sup>+ x. ereal (pmf p x + \<epsilon> * (pmf q x - pmf p x)) \<partial>count_space UNIV) = 1"
  proof (subst nn_integral_count_space')
    have "(\<Sum>x\<in>supp. ereal (pmf p x + \<epsilon> * (pmf q x - pmf p x))) = 
            ereal ((\<Sum>x\<in>supp. pmf p x) + \<epsilon> * ((\<Sum>x\<in>supp. pmf q x) - (\<Sum>x\<in>supp. pmf p x)))"
      by (simp add: setsum.distrib setsum_right_distrib setsum_subtractf ring_distribs)
    also from finite_supp  have "\<dots> = 1"
      by (subst (1 2 3) setsum_pmf_eq_1) (auto simp: supp_def)
    finally show "(\<Sum>x\<in>supp. ereal (pmf p x + \<epsilon> * (pmf q x - pmf p x))) = 1" .
  qed (insert nonneg finite_supp, simp_all)
  with nonneg have pmf_r: "pmf r x = pmf p x + \<epsilon> * (pmf q x - pmf p x)" for x
    unfolding r_def by (intro pmf_embed_pmf) simp_all

  hence "set_pmf r \<subseteq> supp" 
    unfolding supp_def by (auto simp: set_pmf_eq)
  from finite ex_less have "\<epsilon> \<in> {pmf p x / (pmf p x - pmf q x) |x. pmf p x > pmf q x}"
     unfolding \<epsilon>_def by (intro Min_in) auto
  then obtain x where "\<epsilon> = pmf p x / (pmf p x - pmf q x)" "pmf p x > pmf q x" by blast
  hence "pmf r x = 0" by (simp add: pmf_r field_simps)
  moreover from \<open>pmf p x > pmf q x\<close> pmf_nonneg[of q x] 
    have "pmf p x > 0" by simp
  ultimately have "x \<in> set_pmf p - set_pmf r" by (auto simp: set_pmf_iff)
  with \<open>set_pmf r \<close>

  from support_r assms have q_wf: "q \<in> lotteries_on alts"
    by (auto simp add: lotteries_on_def supp_def)  



lemma
  assumes "p \<in> lotteries_on alts"
  shows   "\<exists>q\<in>lotteries_on alts. q \<succeq>[Pareto(SD \<circ> R)] p \<and> SD_efficient R q"
proof -
  from assms have "set_pmf p \<subseteq> alts" by (simp add: lotteries_on_def)
  from this and finite_alts have "finite (set_pmf p)" by (rule finite_subset)
  thus ?thesis
  proof (induction "set_pmf p"  arbitrary: p rule: finite_psubset_induct)
    case (psubset p)
*)    
  
end

end

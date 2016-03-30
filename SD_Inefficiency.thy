theory SD_Inefficiency
imports Complex_Main Preference_Profiles Social_Decision_Schemes PMF_Of_List Missing_PMF
begin

lemma pmf_not_neg [simp]: "\<not>pmf p x < 0"
  by (simp add: not_less pmf_nonneg)

lemma set_pmf_eq': "set_pmf p = {x. pmf p x > 0}"
proof safe
  fix x assume "x \<in> set_pmf p"
  hence "pmf p x \<noteq> 0" by (auto simp: set_pmf_eq)
  with pmf_nonneg[of p x] show "pmf p x > 0" by simp
qed (auto simp: set_pmf_eq)


context pref_profile_wf
begin

lemma
  assumes "finite alts"
  assumes lotteries: "p \<in> lotteries_on alts" "q \<in> lotteries_on alts"
  assumes support: "set_pmf p' \<subseteq> set_pmf p"
  assumes inefficient: "\<not>SD_efficient R p'"
  shows   "\<not>SD_efficient R p"
proof -
  from inefficient obtain q' i where q': "q' \<in> lotteries_on alts" "i \<in> agents"
    "\<And>i. i \<in> agents \<Longrightarrow> q' \<succeq>[SD(R i)] p'" "q' \<succ>[SD(R i)] p'" 
    unfolding SD_efficient_def by blast

  have subset: "{x. pmf p' x > pmf q' x} \<subseteq> set_pmf p'" by (auto simp: set_pmf_eq)
  also have "\<dots> \<subseteq> set_pmf p" by fact
  also have "\<dots> \<subseteq> alts" using lotteries by (simp add: lotteries_on_def)
  finally have finite: "finite {x. pmf p' x > pmf q' x}" 
    using \<open>finite alts\<close> by (rule finite_subset)

  def \<epsilon> \<equiv> "Min (insert 1 {pmf p x / (pmf p' x - pmf q' x) |x. pmf p' x > pmf q' x})"
  from finite support subset have \<epsilon>: "\<epsilon> > 0" unfolding \<epsilon>_def 
    by (intro Min_grI) (auto simp: field_simps set_pmf_eq')
  have "pmf p x + \<epsilon> * (pmf q' x - pmf p' x) \<ge> 0" for x
  proof (cases "pmf p' x > pmf q' x")
    case True
    with finite have "\<epsilon> \<le> pmf p x / (pmf p' x - pmf q' x)"
      unfolding \<epsilon>_def by (intro Min_le) auto
    with True show ?thesis by (simp add: field_simps)
  next
    case False
    with pmf_nonneg[of p x] \<epsilon> show ?thesis by simp
  qed

  from lotteries have "(\<integral>\<^sup>+ x. ereal (pmf p x + \<epsilon> * (pmf q' x - pmf p' x)) \<partial>count_space UNIV) = 1"
apply (subst nn_integral_count_space'[of "set_pmf p \<union> set_pmf q'"])
apply (auto simp: lotteries_on_def)
find_theorems nn_integral count_space setsum
apply (subst nn_integral_measure_pmf_finite)
find_theorems nn_integral pmf setsum
apply (simp add: plus_ereal.simps [symmetric] del: plus_ereal.simps)
apply (subst nn_integral_add)
apply (simp_all add: pmf_nonneg)
find_theorems "nn_integral _ (\<lambda>_. _ + _)"
find_theorems "ereal (_ + _)"


  find_theorems "pmf (pmf p x + \<epsilon> * (pmf q' x - pmf p' x)) x = pmf p x + \<epsilon> * (pmf q' x - pmf p' x)"


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

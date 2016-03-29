theory SD_Inefficiency
imports Complex_Main Preference_Profiles Social_Decision_Schemes PMF_Of_List
begin

definition lotteries_on :: "'a set \<Rightarrow> 'a pmf set" where
  "lotteries_on A = {p. set_pmf p \<subseteq> A}"

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

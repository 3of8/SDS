(*  
  Title:    Missing_PMF.thy
  Author:   Manuel Eberl, TU München

  Auxiliary facts about PMFs that should go in the library at some point
*)

section \<open>Auxiliary facts about PMFs\<close>

theory Missing_PMF
  imports Complex_Main Probability PMF_Of_List Missing_Multiset
begin

(* TODO: Move? *)
adhoc_overloading Monad_Syntax.bind bind_pmf

lemma map_pmf_of_set:
  assumes "finite A" "A \<noteq> {}"
  shows   "map_pmf f (pmf_of_set A) = pmf_of_multiset (image_mset f (mset_set A))" 
    (is "?lhs = ?rhs")
proof (intro pmf_eqI)
  fix x
  from assms have "ereal (pmf ?lhs x) = ereal (pmf ?rhs x)"
    by (subst ereal_pmf_map)
       (simp_all add: emeasure_pmf_of_set mset_set_empty_iff count_image_mset Int_commute)
  thus "pmf ?lhs x = pmf ?rhs x" by simp
qed

lemma pmf_bind_pmf_of_set:
  assumes "A \<noteq> {}" "finite A"
  shows   "pmf (bind_pmf (pmf_of_set A) f) x = 
             (\<Sum>xa\<in>A. pmf (f xa) x) / real_of_nat (card A)" (is "?lhs = ?rhs")
proof -
  from assms have "ereal ?lhs = ereal ?rhs"
    by (subst ereal_pmf_bind) (simp_all add: nn_integral_pmf_of_set max_def pmf_nonneg)
  thus ?thesis by simp
qed

end
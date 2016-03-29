theory Missing_Multiset
imports Main "~~/src/HOL/Library/Multiset" "~~/src/HOL/Library/Disjoint_Sets"
begin

lemma bij_betw_UNION_disjoint:
  assumes disj: "disjoint_family_on A' I"
  assumes bij: "\<And>i. i \<in> I \<Longrightarrow> bij_betw f (A i) (A' i)"
  shows   "bij_betw f (\<Union>i\<in>I. A i) (\<Union>i\<in>I. A' i)"
unfolding bij_betw_def
proof
  from bij show eq: "f ` UNION I A = UNION I A'"
    by (auto simp: bij_betw_def image_UN)
  show "inj_on f (UNION I A)"
  proof (rule inj_onI, clarify)
    fix i j x y assume A: "i \<in> I" "j \<in> I" "x \<in> A i" "y \<in> A j" and B: "f x = f y"
    from A bij[of i] bij[of j] have "f x \<in> A' i" "f y \<in> A' j"
      by (auto simp: bij_betw_def)
    with B have "A' i \<inter> A' j \<noteq> {}" by auto
    with disj A have "i = j" unfolding disjoint_family_on_def by blast
    with A B bij[of i] show "x = y" by (auto simp: bij_betw_def dest: inj_onD)
  qed
qed

lemma mset_set_empty_iff: "mset_set A = {#} \<longleftrightarrow> A = {} \<or> infinite A"
  using finite_set_mset_mset_set by fastforce
  
lemma size_mset_set [simp]: "size (mset_set A) = card A"
  by (simp only: size_eq_msetsum card_eq_setsum setsum_unfold_msetsum)  

lemma count_image_mset: 
  "count (image_mset f A) x = (\<Sum>y\<in>f -` {x} \<inter> set_mset A. count A y)"
  by (induction A)
     (auto simp: setsum.distrib setsum.delta' intro!: setsum.mono_neutral_left)

end
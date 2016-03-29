(*  
  Title:    Preference_Profiles.thy
  Author:   Manuel Eberl, TU München

  Definition of (weak) preference profiles and functions for building
  and manipulating them
*)

section \<open>Preference Profiles\<close>

theory Preference_Profiles
imports
  Main 
  Order_Predicates 
  "~~/src/HOL/Library/Multiset"
  "~~/src/HOL/Library/Disjoint_Sets"
  Missing_Multiset
  Missing_Permutations
begin

text \<open>The type of preference profiles\<close>
type_synonym ('agent, 'alt) pref_profile = "'agent \<Rightarrow> 'alt relation"

definition pref_profile_wf :: "'agent set \<Rightarrow> 'alt set \<Rightarrow> ('agent, 'alt) pref_profile \<Rightarrow> bool" where
  "pref_profile_wf agents alts R \<longleftrightarrow> 
     (\<forall>i\<in>agents. finite_complete_preorder_on alts (R i)) \<and>
     (\<forall>i. i \<notin> agents \<longrightarrow> R i = (\<lambda>_ _. False))"

lemma pref_profile_wfI [intro?]:
  "(\<And>i. i \<in> agents \<Longrightarrow> finite_complete_preorder_on alts (R i)) \<Longrightarrow>
   (\<And>i. i \<notin> agents \<Longrightarrow> R i = (\<lambda>_ _. False)) \<Longrightarrow> pref_profile_wf agents alts R"
  by (simp add: pref_profile_wf_def)

lemma pref_profile_wfD [dest]:
  "pref_profile_wf agents alts R \<Longrightarrow> i \<in> agents \<Longrightarrow> complete_preorder_on alts (R i)"
  "pref_profile_wf agents alts R \<Longrightarrow> i \<in> agents \<Longrightarrow> finite_complete_preorder_on alts (R i)"
  "pref_profile_wf agents alts R \<Longrightarrow> i \<notin> agents \<Longrightarrow> R i = (\<lambda>_ _. False)"
  by (simp_all add: pref_profile_wf_def finite_complete_preorder_on_iff)

lemma pref_profile_wf_update:
  "pref_profile_wf agents alts R \<Longrightarrow> i \<in> agents \<Longrightarrow>
     finite_complete_preorder_on alts Ri' \<Longrightarrow> 
     pref_profile_wf agents alts (R(i := Ri'))"
  by (auto simp: pref_profile_wf_def)

lemma pref_profile_wf_permute_agents:
  assumes "\<sigma> permutes agents" "pref_profile_wf agents alts R"
  shows   "pref_profile_wf agents alts (R \<circ> \<sigma>)"
  unfolding o_def using permutes_in_image[OF assms(1)]
  by (intro pref_profile_wfI pref_profile_wfD[OF assms(2)]) simp_all

lemma pref_profile_eqI:
  assumes "pref_profile_wf agents alts R1" "pref_profile_wf agents alts R2"
  assumes "\<And>x. x \<in> agents \<Longrightarrow> R1 x = R2 x"
  shows   "R1 = R2"
proof
  fix x
  from assms show "R1 x = R2 x"
    by (cases "x \<in> agents") (simp_all add: pref_profile_wf_def) 
qed


text \<open>
  Permutes a preference profile w.r.t. alternatives in the way described in the paper.
  This is needed for the definition of neutrality.
\<close>
definition permute_profile where
  "permute_profile \<sigma> R = (\<lambda>i x y. R i (inv \<sigma> x) (inv \<sigma> y))"
  
lemma permute_profile_map_relation:
  "permute_profile \<sigma> R = (\<lambda>i. map_relation (inv \<sigma>) (R i))"
  by (simp add: permute_profile_def map_relation_def)

lemma permute_profile_compose [simp]:
  "permute_profile \<sigma> (R \<circ> \<pi>) = permute_profile \<sigma> R \<circ> \<pi>"
  by (auto simp: fun_eq_iff permute_profile_def o_def)

lemma permute_profile_id [simp]: "permute_profile id R = R"
  by (simp add: permute_profile_def)

lemma permute_profile_o:
  assumes "bij f" "bij g"
  shows   "permute_profile f (permute_profile g R) = permute_profile (f \<circ> g) R"
  using assms by (simp add: permute_profile_def o_inv_distrib)

lemma pref_profile_wf_permute:
  assumes "\<sigma> permutes alts" "pref_profile_wf agents alts R"
  shows   "pref_profile_wf agents alts (permute_profile \<sigma> R)"
proof
  fix i assume "i \<in> agents"
  with assms interpret R: finite_complete_preorder_on alts "R i"
    by (simp add: pref_profile_wfD)
  from assms have [simp]: "inv \<sigma> x \<in> alts \<longleftrightarrow> x \<in> alts" for x
    by (simp add: permutes_in_image permutes_inv)

  show "finite_complete_preorder_on alts (permute_profile \<sigma> R i)"
  proof
    fix x y assume "permute_profile \<sigma> R i x y"
    thus "x \<in> alts" "y \<in> alts"
      using R.not_outside[of "inv \<sigma> x" "inv \<sigma> y"]
      by (auto simp: permute_profile_def)
  next
    fix x y z assume "permute_profile \<sigma> R i x y" "permute_profile \<sigma> R i y z"
    thus "permute_profile \<sigma> R i x z"
      using R.trans[of "inv \<sigma> x" "inv \<sigma> y" "inv \<sigma> z"] 
      by (simp_all add: permute_profile_def)
  qed (insert R.complete R.refl R.finite_carrier, simp_all add: permute_profile_def)
qed (insert assms, simp_all add: permute_profile_def pref_profile_wf_def)


text \<open>
  This shows that the above definition is equivalent to that in the paper.  
\<close>
lemma permute_profile_iff [simp]:
  fixes R :: "('agent, 'alt) pref_profile"
  assumes "\<sigma> permutes alts" "x \<in> alts" "y \<in> alts"
  defines "R' \<equiv> permute_profile \<sigma> R"
  shows   "\<sigma> x \<preceq>[R' i] \<sigma> y \<longleftrightarrow> x \<preceq>[R i] y"
  using assms by (simp add: permute_profile_def permutes_inverses)


subsection \<open>Favourite alternatives\<close>

definition favorites :: "('agent, 'alt) pref_profile \<Rightarrow> 'agent \<Rightarrow> 'alt set" where
  "favorites R i = Max_wrt (R i)"

lemma favorites_altdef:
  assumes "pref_profile_wf agents alts R"
  shows   "favorites R i = Max_wrt_among (R i) alts"
proof (cases "i \<in> agents")
  assume "i \<in> agents"
  with assms interpret complete_preorder_on alts "R i" by (simp add: pref_profile_wfD)
  show ?thesis 
    by (simp add: favorites_def Max_wrt_complete_preorder Max_wrt_among_complete_preorder)
qed (insert assms, simp_all add: favorites_def Max_wrt_def Max_wrt_among_def pref_profile_wf_def)


(* TODO Move *)
definition is_singleton :: "'a set \<Rightarrow> bool" where
  "is_singleton A \<longleftrightarrow> (\<exists>x. A = {x})"

lemma is_singletonI [simp, intro!]: "is_singleton {x}"
  unfolding is_singleton_def by simp

lemma is_singletonE: "is_singleton A \<Longrightarrow> (\<And>x. A = {x} \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding is_singleton_def by blast

lemma is_singleton_altdef: "is_singleton A \<longleftrightarrow> card A = 1"
  unfolding is_singleton_def
  by (auto elim!: card_1_singletonE is_singletonE simp del: One_nat_def)
  
lemma is_singleton_the_elem: "is_singleton A \<longleftrightarrow> A = {the_elem A}"
  by (auto simp: is_singleton_def)

definition favorite :: "('agent, 'alt) pref_profile \<Rightarrow> 'agent \<Rightarrow> 'alt" where
  "favorite R i = the_elem (favorites R i)"
  

subsection \<open>Anonymous profiles\<close>

type_synonym ('agent, 'alt) apref_profile = "'alt set list multiset"

definition anonymous_profile :: "'agent set \<Rightarrow> ('agent, 'alt) pref_profile \<Rightarrow> ('agent, 'alt) apref_profile" 
  where "anonymous_profile agents R = image_mset (weak_ranking \<circ> R) (mset_set agents)"

lemma anonymous_profile_permute:
  assumes "pref_profile_wf agents alts R" "\<sigma> permutes alts"  "finite agents" 
  shows   "anonymous_profile agents (permute_profile \<sigma> R) = image_mset (map (op ` \<sigma>)) (anonymous_profile agents R)"
proof -
  have "anonymous_profile agents (permute_profile \<sigma> R) = 
          {#weak_ranking (map_relation (inv \<sigma>) (R x)). x \<in># mset_set agents#}"
    by (simp add: anonymous_profile_def multiset.map_comp permute_profile_map_relation o_def)
  also from assms have "\<dots> = {#map (op ` \<sigma>) (weak_ranking (R x)). x \<in># mset_set agents#}"
    by (intro image_mset_cong)
       (simp add: pref_profile_wfD finite_complete_preorder_on.weak_ranking_permute[of alts])
  also have "\<dots> = image_mset (map (op ` \<sigma>)) (anonymous_profile agents R)"
    by (simp add: anonymous_profile_def multiset.map_comp o_def)
  finally show ?thesis .
qed

lemma image_mset_If:
  "image_mset (\<lambda>x. if P x then f x else g x) A = 
     image_mset f (filter_mset P A) + image_mset g (filter_mset (\<lambda>x. \<not>P x) A)"
  by (induction A) (auto simp: add_ac)

lemma mset_set_Union: 
  "finite A \<Longrightarrow> finite B \<Longrightarrow> A \<inter> B = {} \<Longrightarrow> mset_set (A \<union> B) = mset_set A + mset_set B"
  by (induction A rule: finite_induct) (auto simp: add_ac)


lemma filter_mset_mset_set [simp]:
  "finite A \<Longrightarrow> filter_mset P (mset_set A) = mset_set {x\<in>A. P x}"
proof (induction A rule: finite_induct)
  case (insert x A)
  from insert.hyps have "filter_mset P (mset_set (insert x A)) = 
      filter_mset P (mset_set A) + mset_set (if P x then {x} else {})"
    by (simp add: add_ac)
  also have "filter_mset P (mset_set A) = mset_set {x\<in>A. P x}"
    by (rule insert.IH)
  also from insert.hyps 
    have "\<dots> + mset_set (if P x then {x} else {}) =
            mset_set ({x \<in> A. P x} \<union> (if P x then {x} else {}))" (is "_ = mset_set ?A")
     by (intro mset_set_Union [symmetric]) simp_all
  also from insert.hyps have "?A = {y\<in>insert x A. P y}" by auto
  finally show ?case .
qed simp_all

lemma image_mset_Diff: 
  assumes "B \<subseteq># A"
  shows   "image_mset f (A - B) = image_mset f A - image_mset f B"
proof -
  have "image_mset f (A - B + B) = image_mset f (A - B) + image_mset f B"
    by simp
  also from assms have "A - B + B = A"
    by (simp add: subset_mset.diff_add) 
  finally show ?thesis by simp
qed

lemma mset_set_Diff:
  assumes "finite A" "B \<subseteq> A"
  shows  "mset_set (A - B) = mset_set A - mset_set B"
proof -
  from assms have "mset_set ((A - B) \<union> B) = mset_set (A - B) + mset_set B"
    by (intro mset_set_Union) (auto dest: finite_subset)
  also from assms have "A - B \<union> B = A" by blast
  finally show ?thesis by simp
qed

lemma anonymous_profile_update:
  assumes i:  "i \<in> agents" and fin [simp]: "finite agents"
  shows   "anonymous_profile agents (R(i := Ri')) =
             anonymous_profile agents R - {#weak_ranking (R i)#} + {#weak_ranking Ri'#}"
proof -
  have "anonymous_profile agents (R(i := Ri')) = 
          {#weak_ranking (if x = i then Ri' else R x). x \<in># mset_set agents#}"
    by (simp add: anonymous_profile_def o_def)
  also have "\<dots> = {#if x = i then weak_ranking Ri' else weak_ranking (R x). x \<in># mset_set agents#}"
    by (intro image_mset_cong) simp_all
  also have "\<dots> = {#weak_ranking Ri'. x \<in># mset_set {x \<in> agents. x = i}#} +
                    {#weak_ranking (R x). x \<in># mset_set {x \<in> agents. x \<noteq> i}#}"
    by (subst image_mset_If) ((subst filter_mset_mset_set, simp)+, rule refl)
  also from i have "{x \<in> agents. x = i} = {i}" by auto
  also have "{x \<in> agents. x \<noteq> i} = agents - {i}" by auto
  also have "{#weak_ranking Ri'. x \<in># mset_set {i}#} = {#weak_ranking Ri'#}" by simp
  also from i have "mset_set (agents - {i}) = mset_set agents - {#i#}"
    by (simp add: mset_set_Diff)
  also from i 
    have "{#weak_ranking (R x). x \<in># \<dots>#} =
            {#weak_ranking (R x). x \<in># mset_set agents#} - {#weak_ranking (R i)#}"
      by (subst image_mset_Diff) (simp_all add: in_multiset_in_set mset_le_single)
  also have "{#weak_ranking Ri'#} + \<dots> = 
               anonymous_profile agents R - {#weak_ranking (R i)#} + {#weak_ranking Ri'#}"
    by (simp add: anonymous_profile_def add_ac o_def)
  finally show ?thesis .
qed


subsection \<open>Preference profiles from lists\<close>

definition prefs_from_table :: "('agent \<times> 'alt set list) list \<Rightarrow> ('agent, 'alt) pref_profile" where
  "prefs_from_table xss = (\<lambda>i. case_option (\<lambda>_ _. False) of_weak_ranking (map_of xss i))"

definition prefs_from_table_wf where
  "prefs_from_table_wf agents alts xss \<longleftrightarrow> distinct (map fst xss) \<and> set (map fst xss) = agents \<and>
       (\<forall>xs\<in>set (map snd xss). (\<Union>set xs) = alts \<and> is_finite_weak_ranking xs)"

lemma prefs_from_table_wfI:
  assumes "distinct (map fst xss)"
  assumes "set (map fst xss) = agents"
  assumes "\<And>xs. xs \<in> set (map snd xss) \<Longrightarrow> (\<Union>set xs) = alts"
  assumes "\<And>xs. xs \<in> set (map snd xss) \<Longrightarrow> is_finite_weak_ranking xs"
  shows   "prefs_from_table_wf agents alts xss"
  using assms unfolding prefs_from_table_wf_def by auto

lemma prefs_from_table_wfD:
  assumes "prefs_from_table_wf agents alts xss"
  shows "distinct (map fst xss)"
    and "set (map fst xss) = agents"
    and "\<And>xs. xs \<in> set (map snd xss) \<Longrightarrow> (\<Union>set xs) = alts"
    and "\<And>xs. xs \<in> set (map snd xss) \<Longrightarrow> is_finite_weak_ranking xs"
  using assms unfolding prefs_from_table_wf_def by auto
       
lemma pref_profile_from_tableI: 
  "prefs_from_table_wf agents alts xss \<Longrightarrow> pref_profile_wf agents alts (prefs_from_table xss)"
  unfolding pref_profile_wf_def
proof safe
  assume wf: "prefs_from_table_wf agents alts xss"
  fix i assume i: "i \<in> agents"
  with wf have "i \<in> set (map fst xss)" by (simp add: prefs_from_table_wf_def)
  then obtain xs where xs: "xs \<in> set (map snd xss)" "prefs_from_table xss i = of_weak_ranking xs"
    by (cases "map_of xss i")
       (fastforce dest: map_of_SomeD simp: prefs_from_table_def map_of_eq_None_iff)+
  with wf show "finite_complete_preorder_on alts (prefs_from_table xss i)"
    by (auto simp: prefs_from_table_wf_def intro!: finite_complete_preorder_of_weak_ranking)
next
  assume wf: "prefs_from_table_wf agents alts xss"
  fix i assume i: "i \<notin> agents"
  with wf have "i \<notin> set (map fst xss)" by (simp add: prefs_from_table_wf_def)
  hence "map_of xss i = None" by (simp add: map_of_eq_None_iff)
  thus "prefs_from_table xss i = (\<lambda>_ _. False)"
    by (simp add: prefs_from_table_def)
qed

lemma prefs_from_table_eqI:
  assumes "distinct (map fst xs)" "distinct (map fst ys)" "set xs = set ys"
  shows   "prefs_from_table xs = prefs_from_table ys"
proof -
  from assms have "map_of xs = map_of ys" by (subst map_of_inject_set) simp_all
  thus ?thesis by (simp add: prefs_from_table_def)
qed

lemma prefs_from_table_undef:
  assumes "prefs_from_table_wf agents alts xss" "i \<notin> agents"
  shows   "prefs_from_table xss i = (\<lambda>_ _. False)"
proof -
  from assms have "i \<notin> fst ` set xss"
    by (simp add: prefs_from_table_wf_def)
  hence "map_of xss i = None" by (simp add: map_of_eq_None_iff)
  thus ?thesis by (simp add: prefs_from_table_def)
qed

lemma prefs_from_table_map_of:
  assumes "prefs_from_table_wf agents alts xss" "i \<in> agents"
  shows   "prefs_from_table xss i = of_weak_ranking (the (map_of xss i))"
  using assms 
  by (auto simp: prefs_from_table_def map_of_eq_None_iff prefs_from_table_wf_def
           split: option.splits)

lemma prefs_from_table_update:
  fixes x xs
  assumes "i \<in> set (map fst xs)"
  defines "xs' \<equiv> map (\<lambda>(j,y). if j = i then (j, x) else (j, y)) xs"
  shows   "(prefs_from_table xs)(i := of_weak_ranking x) =
             prefs_from_table xs'" (is "?lhs = ?rhs")
proof
  have xs': "set (map fst xs') = set (map fst xs)" by (force simp: xs'_def)  
  fix k
  consider "k = i" | "k \<notin> set (map fst xs)" | "k \<noteq> i" "k \<in> set (map fst xs)" by blast
  thus "?lhs k = ?rhs k"
  proof cases 
    assume k: "k = i"
    moreover from k have "y = x" if "(i, y) \<in> set xs'" for y
      using that by (auto simp: xs'_def split: if_splits)
    ultimately show ?thesis using assms(1) k xs'
      by (auto simp add: prefs_from_table_def map_of_eq_None_iff 
               dest!: map_of_SomeD split: option.splits)
  next
    assume k: "k \<notin> set (map fst xs)"
    with assms(1) have k': "k \<noteq> i" by auto
    with k xs' have "map_of xs k = None" "map_of xs' k = None"
      by (simp_all add: map_of_eq_None_iff)
    thus ?thesis by (simp add: prefs_from_table_def k')
  next
    assume k: "k \<noteq> i" "k \<in> set (map fst xs)"
    with k(1) have "map_of xs k = map_of xs' k" unfolding xs'_def
      by (induction xs) fastforce+
    with k show ?thesis by (simp add: prefs_from_table_def)
  qed
qed

lemma prefs_from_table_swap:
  "x \<noteq> y \<Longrightarrow> prefs_from_table ((x,x')#(y,y')#xs) = prefs_from_table ((y,y')#(x,x')#xs)"
  by (intro ext) (auto simp: prefs_from_table_def)

lemma permute_prefs_from_table:
  assumes "\<sigma> permutes fst ` set xs"
  shows   "prefs_from_table xs \<circ> \<sigma> = prefs_from_table (map (\<lambda>(x,y). (inv \<sigma> x, y)) xs)"
proof
  fix i
  have "(prefs_from_table xs \<circ> \<sigma>) i = 
          (case map_of xs (\<sigma> i) of
             None \<Rightarrow> \<lambda>_ _. False
           | Some x \<Rightarrow> of_weak_ranking x)"
    by (simp add: prefs_from_table_def o_def)
  also have "map_of xs (\<sigma> i) = map_of (map (\<lambda>(x,y). (inv \<sigma> x, y)) xs) i"
    using map_of_permute[OF assms] by (simp add: o_def fun_eq_iff)
  finally show "(prefs_from_table xs \<circ> \<sigma>) i = prefs_from_table (map (\<lambda>(x,y). (inv \<sigma> x, y)) xs) i"
    by (simp only: prefs_from_table_def)
qed

lemma permute_profile_from_table:
  assumes wf: "prefs_from_table_wf agents alts xss"
  assumes perm: "\<sigma> permutes alts"
  shows   "permute_profile \<sigma> (prefs_from_table xss) = 
             prefs_from_table (map (\<lambda>(x,y). (x, map (op ` \<sigma>) y)) xss)" (is "?f = ?g")
proof
  fix i
  (* TODO: Clean up this mess *)
  from assms have wf': "prefs_from_table_wf agents alts (map (\<lambda>(x, y). (x, map (op ` \<sigma>) y)) xss)"
    apply (intro prefs_from_table_wfI)
    apply (simp add: o_def case_prod_unfold prefs_from_table_wf_def)
    apply (simp add: o_def case_prod_unfold prefs_from_table_wf_def)
    apply (simp add: o_def case_prod_unfold)
    apply (elim imageE)
    apply (simp add: image_Union [symmetric] prefs_from_table_wf_def permutes_image)
    apply (simp add: o_def case_prod_unfold)
    apply (elim imageE)
    apply (simp add: is_finite_weak_ranking_def is_weak_ranking_iff distinct_map
             permutes_inj_on inj_on_image)
    apply (auto simp: prefs_from_table_wf_def is_finite_weak_ranking_def 
                      is_weak_ranking_iff permutes_inj_on inj_on_image
                intro!: disjoint_image)
    done
  show "?f i = ?g i"
  proof (cases "i \<in> agents")
    assume "i \<notin> agents"
    with assms wf' show ?thesis
      by (simp add: permute_profile_def prefs_from_table_undef)
  next
    assume i: "i \<in> agents"
    def xs \<equiv> "the (map_of xss i)"
    from i wf have xs: "map_of xss i = Some xs"
      by (cases "map_of xss i") (auto simp: prefs_from_table_wf_def xs_def)
    have xs_in_xss: "xs \<in> snd ` set xss"
      using xs by (force dest!: map_of_SomeD)
    with wf have set_xs: "\<Union>set xs = alts"
      by (simp add: prefs_from_table_wfD)

    from i have "prefs_from_table (map (\<lambda>(x,y). (x, map (op ` \<sigma>) y)) xss) i =
                   of_weak_ranking (the (map_of (map (\<lambda>(x,y). (x, map (op ` \<sigma>) y)) xss) i))"
      using wf' by (intro prefs_from_table_map_of) simp_all
    also have "\<dots> = of_weak_ranking (map (op ` \<sigma>) xs)"
      by (subst map_of_map) (simp add: xs)
    also have "\<dots> = (\<lambda>a b. of_weak_ranking xs (inv \<sigma> a) (inv \<sigma> b))"
      by (intro ext) (simp add: of_weak_ranking_permute map_relation_def set_xs perm)
    also have "\<dots> = permute_profile \<sigma> (prefs_from_table xss) i"
      by (simp add: prefs_from_table_def xs permute_profile_def)
    finally show ?thesis ..
  qed
qed


subsection \<open>Automatic evaluation of preference profiles\<close>

lemma eval_prefs_from_table [simp]:
  "prefs_from_table []i = (\<lambda>_ _. False)"
  "prefs_from_table ((i, y) # xs) i = of_weak_ranking y"
  "i \<noteq> j \<Longrightarrow> prefs_from_table ((j, y) # xs) i = prefs_from_table xs i"
  by (simp_all add: prefs_from_table_def)

lemma eval_of_weak_ranking [simp]:
  "a \<notin> \<Union>set xs \<Longrightarrow> \<not>of_weak_ranking xs a b"
  "b \<in> x \<Longrightarrow> a \<in> \<Union>set (x#xs) \<Longrightarrow> of_weak_ranking (x # xs) a b"
  "b \<notin> x \<Longrightarrow> of_weak_ranking (x # xs) a b \<longleftrightarrow> of_weak_ranking xs a b"
  by (induction xs) (simp_all add: of_weak_ranking_Cons)

lemma prefs_from_table_cong [cong]:
  assumes "prefs_from_table xs = prefs_from_table ys"
  shows   "prefs_from_table (x#xs) = prefs_from_table (x#ys)"
proof
  fix i
  show "prefs_from_table (x # xs) i = prefs_from_table (x # ys) i"
    using assms by (cases x, cases "i = fst x") simp_all
qed

definition of_weak_ranking_Collect_ge where
  "of_weak_ranking_Collect_ge xs x = {y. of_weak_ranking xs y x}"

lemma eval_Collect_of_weak_ranking:
  "Collect (of_weak_ranking xs x) = of_weak_ranking_Collect_ge (rev xs) x"
  by (simp add: of_weak_ranking_Collect_ge_def)

lemma of_weak_ranking_Collect_ge_empty [simp]:
  "of_weak_ranking_Collect_ge [] x = {}"
  by (simp add: of_weak_ranking_Collect_ge_def)

lemma of_weak_ranking_Collect_ge_Cons [simp]:
  "y \<in> x \<Longrightarrow> of_weak_ranking_Collect_ge (x#xs) y = (\<Union>set (x#xs))"
  "y \<notin> x \<Longrightarrow> of_weak_ranking_Collect_ge (x#xs) y = of_weak_ranking_Collect_ge xs y"
  by (auto simp: of_weak_ranking_Cons of_weak_ranking_Collect_ge_def)

(* TODO Move *)
lemma mset_set_set: "distinct xs \<Longrightarrow> mset_set (set xs) = mset xs"
  by (induction xs) (simp_all add: add_ac)

lemma image_mset_map_of: 
  "distinct (map fst xs) \<Longrightarrow> {#the (map_of xs i). i \<in># mset (map fst xs)#} = mset (map snd xs)"
proof (induction xs)
  case (Cons x xs)
  have "{#the (map_of (x # xs) i). i \<in># mset (map fst (x # xs))#} = 
          {#the (if i = fst x then Some (snd x) else map_of xs i). 
             i \<in># mset (map fst xs)#} + {#snd x#}" (is "_ = ?A + _") by simp
  also from Cons.prems have "?A = {#the (map_of xs i). i :# mset (map fst xs)#}"
    by (cases x, intro image_mset_cong) (auto simp: in_multiset_in_set)
  also from Cons.prems have "\<dots> = mset (map snd xs)" by (intro Cons.IH) simp_all
  finally show ?case by simp
qed simp_all

lemma anonymise_prefs_from_table:
  assumes "prefs_from_table_wf agents alts xs"
  shows   "anonymous_profile agents (prefs_from_table xs) = mset (map snd xs)"
proof -
  from assms have agents: "agents = fst ` set xs"
    by (simp add: prefs_from_table_wf_def)
  hence [simp]: "finite agents" by auto
  have "anonymous_profile agents (prefs_from_table xs) = 
          {#weak_ranking (prefs_from_table xs x). x \<in># mset_set agents#}"
    by (simp add: o_def anonymous_profile_def)
  also from assms have "\<dots> = {#the (map_of xs i). i \<in># mset_set agents#}"
  proof (intro image_mset_cong)
    fix i assume i: "i \<in># mset_set agents"
    from i assms 
      have "weak_ranking (prefs_from_table xs i) = 
              weak_ranking (of_weak_ranking (the (map_of xs i))) "
      by (simp add: prefs_from_table_map_of)
    also from assms i have "\<dots> = the (map_of xs i)"
      by (intro weak_ranking_of_weak_ranking)
         (auto simp: prefs_from_table_wf_def)
    finally show "weak_ranking (prefs_from_table xs i) = the (map_of xs i)" .
  qed
  also from agents have "mset_set agents = mset_set (set (map fst xs))" by simp
  also from assms have "\<dots> = mset (map fst xs)"
    by (intro mset_set_set) (simp_all add: prefs_from_table_wf_def)
  also from assms have "{#the (map_of xs i). i \<in># mset (map fst xs)#} = mset (map snd xs)"
    by (intro image_mset_map_of) (simp_all add: prefs_from_table_wf_def)
  finally show ?thesis .
qed

lemma prefs_from_table_agent_permutation:
  assumes wf: "prefs_from_table_wf agents alts xs" "prefs_from_table_wf agents alts ys"
  assumes mset_eq: "mset (map snd xs) = mset (map snd ys)"
  obtains \<pi> where "\<pi> permutes agents" "prefs_from_table xs \<circ> \<pi> = prefs_from_table ys"
proof -
  from wf(1) have agents: "agents = set (map fst xs)"
    by (simp_all add: prefs_from_table_wf_def)
  from wf(2) have agents': "agents = set (map fst ys)"
    by (simp_all add: prefs_from_table_wf_def)
  from agents agents' wf(1) wf(2) have "mset (map fst xs) = mset (map fst ys)"
    by (subst set_eq_iff_mset_eq_distinct [symmetric]) (simp_all add: prefs_from_table_wfD)
  hence same_length: "length xs = length ys" by (auto dest: mset_eq_length)

  from \<open>mset (map fst xs) = mset (map fst ys)\<close>
    obtain g where g: "g permutes {..<length ys}" "permute_list g (map fst ys) = map fst xs"
    by (auto elim: mset_eq_permutation simp: same_length)

  from mset_eq g 
    have "mset (map snd ys) = mset (permute_list g (map snd ys))" by simp
  with mset_eq obtain f 
    where f: "f permutes {..<length xs}" 
             "permute_list f (permute_list g (map snd ys)) = map snd xs"
    by (auto elim: mset_eq_permutation simp: same_length)
  from permutes_in_image[OF f(1)]
    have [simp]: "f x < length xs \<longleftrightarrow> x < length xs" 
                 "f x < length ys \<longleftrightarrow> x < length ys" for x by (simp_all add: same_length)

  def idx \<equiv> "index (map fst xs)" and unidx \<equiv> "\<lambda>i. map fst xs ! i"
  from wf(1) have "bij_betw idx agents {0..<length xs}" unfolding idx_def
    by (intro bij_betw_index) (simp_all add: prefs_from_table_wf_def)
  hence bij_betw_idx: "bij_betw idx agents {..<length xs}" by (simp add: atLeast0LessThan)
  have [simp]: "idx x < length xs" if "x \<in> agents" for x
    using that by (simp add: idx_def agents)
  have [simp]: "unidx i \<in> agents" if "i < length xs" for i
    using that by (simp add: agents unidx_def)

  have unidx_idx: "unidx (idx x) = x" if x: "x \<in> agents" for x
    using x unfolding idx_def unidx_def using nth_index[of x "map fst xs"]
    by (simp add: agents set_map [symmetric] nth_map [symmetric] del: set_map)
  have idx_unidx: "idx (unidx i) = i" if i: "i < length xs" for i
    unfolding idx_def unidx_def using wf(1) index_nth_id[of "map fst xs" i] i
    by (simp add: prefs_from_table_wfD(1))
 
  def \<pi> \<equiv> "\<lambda>x. if x \<in> agents then (unidx \<circ> f \<circ> idx) x else x"
  def \<pi>' \<equiv> "\<lambda>x. if x \<in> agents then (unidx \<circ> inv f \<circ> idx) x else x"
  have "bij_betw (unidx \<circ> f \<circ> idx) agents agents" (is "?P") unfolding unidx_def
    by (rule bij_betw_trans bij_betw_idx permutes_imp_bij f g bij_betw_nth)+
       (insert wf(1) g, simp_all add: prefs_from_table_wf_def same_length)
  also have "?P \<longleftrightarrow> bij_betw \<pi> agents agents"
    by (intro bij_betw_cong) (simp add: \<pi>_def)
  finally have perm: "\<pi> permutes agents"
    by (intro bij_imp_permutes) (simp_all add: \<pi>_def)

  def h \<equiv> "g \<circ> f"
  from f g have h: "h permutes {..<length ys}" unfolding h_def
    by (intro permutes_compose) (simp_all add: same_length)

  have inv_\<pi>: "inv \<pi> = \<pi>'"
  proof (rule permutes_invI[OF perm])
    fix x assume "x \<in> agents"
    with f(1) show "\<pi>' (\<pi> x) = x"
      by (simp add: \<pi>_def \<pi>'_def idx_unidx unidx_idx inv_f_f permutes_inj)
  qed (simp add: \<pi>_def \<pi>'_def)
  with perm have inv_\<pi>': "inv \<pi>' = \<pi>" by (auto simp: inv_inv_eq permutes_bij)

  from wf h have "prefs_from_table ys = prefs_from_table (permute_list h ys)"
    by (intro prefs_from_table_eqI)
       (simp_all add: prefs_from_table_wfD permute_list_map [symmetric])
  also have "permute_list h ys = permute_list h (zip (map fst ys) (map snd ys))"
    by (simp add: zip_map_fst_snd)
  also from same_length f g
    have "permute_list h (zip (map fst ys) (map snd ys)) = 
            zip (permute_list f (map fst xs)) (map snd xs)"
    by (subst permute_list_zip[OF h]) (simp_all add: h_def permute_list_compose)
  also {
    fix i assume i: "i < length xs"
    from i have "permute_list f (map fst xs) ! i = unidx (f i)"
      using permutes_in_image[OF f(1)] f(1) 
      by (subst permute_list_nth) (simp_all add: same_length unidx_def)
    also from i have "\<dots> = \<pi> (unidx i)" by (simp add: \<pi>_def idx_unidx)
    also from i have "\<dots> = map \<pi> (map fst xs) ! i" by (simp add: unidx_def)
    finally have "permute_list f (map fst xs) ! i = map \<pi> (map fst xs) ! i" .
  }
  hence "permute_list f (map fst xs) = map \<pi> (map fst xs)"
    by (intro nth_equalityI) simp_all
  also have "zip (map \<pi> (map fst xs)) (map snd xs) = map (\<lambda>(x,y). (inv \<pi>' x, y)) xs"
    by (induction xs) (simp_all add: case_prod_unfold inv_\<pi>')
  also from permutes_inv[OF perm] inv_\<pi> have "prefs_from_table \<dots> = prefs_from_table xs \<circ> \<pi>'"
    by (intro permute_prefs_from_table [symmetric]) (simp_all add: agents)
  finally have "prefs_from_table xs \<circ> \<pi>' = prefs_from_table ys" ..
  with that[of \<pi>'] permutes_inv[OF perm] inv_\<pi> show ?thesis by auto
qed

lemma permute_list_distinct:
  assumes "f ` {..<length xs} \<subseteq> {..<length xs}" "distinct xs"
  shows   "permute_list f xs = map (\<lambda>x. xs ! f (index xs x)) xs"
  using assms by (intro nth_equalityI) (auto simp: index_nth_id permute_list_def)

lemma image_mset_eq_permutation:
  assumes "{#f x. x \<in># mset_set A#} = {#g x. x \<in># mset_set A#}" "finite A"
  obtains \<pi> where "\<pi> permutes A" "\<And>x. x \<in> A \<Longrightarrow> g (\<pi> x) = f x"
proof -
  from assms(2) obtain xs where xs: "A = set xs" "distinct xs"
    using finite_distinct_list by blast
  with assms have "mset (map f xs) = mset (map g xs)" 
    by (simp add: mset_set_set mset_map)
  from mset_eq_permutation[OF this] obtain \<pi> where
    \<pi>: "\<pi> permutes {0..<length xs}" "permute_list \<pi> (map g xs) = map f xs"
    by (auto simp: atLeast0LessThan)
  def \<pi>' \<equiv> "\<lambda>x. if x \<in> A then (op ! xs \<circ> \<pi> \<circ> index xs) x else x"
  have "bij_betw (op ! xs \<circ> \<pi> \<circ> index xs) A A" (is "?P")
    by (rule bij_betw_trans bij_betw_index xs refl permutes_imp_bij \<pi> bij_betw_nth)+
       (simp_all add: atLeast0LessThan xs)
  also have "?P \<longleftrightarrow> bij_betw \<pi>' A A"
    by (intro bij_betw_cong) (simp_all add: \<pi>'_def)
  finally have "\<pi>' permutes A"
    by (rule bij_imp_permutes) (simp_all add: \<pi>'_def)
  moreover from \<pi> xs(1)[symmetric] xs(2) have "g (\<pi>' x) = f x" if "x \<in> A" for x
    by (simp add: permute_list_map permute_list_distinct
          permutes_image \<pi>'_def that atLeast0LessThan)
  ultimately show ?thesis by (rule that)
qed

lemma anonymous_profile_agent_permutation:
  assumes eq:  "anonymous_profile agents R1 = anonymous_profile agents R2"
  assumes wf:  "pref_profile_wf agents alts R1" "pref_profile_wf agents alts R2"
  assumes fin: "finite agents"
  obtains \<pi> where "\<pi> permutes agents" "R2 \<circ> \<pi> = R1"
proof -
  from eq have "{#weak_ranking (R1 x). x \<in># mset_set agents#} = 
                  {#weak_ranking (R2 x). x \<in># mset_set agents#}"
    by (simp add: anonymous_profile_def o_def)
  from image_mset_eq_permutation[OF this fin] guess \<pi> . note \<pi> = this
  from wf \<pi> have wf': "pref_profile_wf agents alts (R2 \<circ> \<pi>)"
    by (intro pref_profile_wf_permute_agents)
  have "R2 \<circ> \<pi> = R1"
  proof (intro pref_profile_eqI[OF wf' wf(1)])
    fix x assume x: "x \<in> agents"
    with \<pi> have "weak_ranking ((R2 o \<pi>) x) = weak_ranking (R1 x)" by simp
    with wf' wf(1) x show "(R2 \<circ> \<pi>) x = R1 x"
      by (intro weak_ranking_eqD[of alts]) auto
  qed
  from \<pi>(1) and this show ?thesis by (rule that)
qed

end
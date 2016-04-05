theory SDS_Automation
imports Preference_Profile_Cmd
begin


(* TODO: For testing only; can be removed *)
datatype agents = A1 | A2 | A3 | A4
datatype alts = a | b | c | d

preference_profile 
  agents: "{A1, A2, A3, A4}"
  alts:   "{a, b, c, d}"
  where R1  = A1: [a,c], [b,d]     A2: [b,d], [a,c]     A3: [a,d], b, c     A4: [b,c], a, d
    and R2  = A1: [a,c], [b,d]     A2: [b,d], [a,c]     A3: a, d, [b,c]     A4: b, c, [a, d]
    and R3  = A1: [a,c], [b,d]     A2: [b,d], [a,c]     A3: [a,d], b, c     A4: d, c, a, b
    and R4  = A1: [a,c], [b,d]     A2: [b,d], [a,c]     A3: [c,b], d, a     A4: b, a, c, d
    and R5  = A1: [a,c,d], [b]     A2: [b,a], [c,d]     A3: [c,b], d, a     A4: b, a, [d,c]
by (simp_all add: insert_eq_iff)

lemma "anonymous_profile {A1, A2, A3, A4} R1 = 
  {#[{a, c}, {b, d}], [{b, d}, {a, c}], [{a, d}, {b}, {c}], [{b, c}, {a}, {d}]#}"
  by (simp add: R1_eval add_ac)

lemma
  defines "\<sigma> \<equiv> permutation_of_list [(a,b),(b,a),(c,d),(d,c)]"
  assumes "an_sds {A1,A2,A3,A4} {a,b,c,d} sds"
  shows   "pmf (sds R1) (\<sigma> a) = pmf (sds R1) a"
  by (rule an_sds_automorphism_aux[OF R1_wf, of sds \<sigma>])
     (simp_all add: assms insert_commute insert_eq_iff add_ac
        distincts_Cons pref_profile_wf.anonymous_profile_permute[OF R1_wf] R1_eval)

lemma
  defines "\<sigma> \<equiv> permutation_of_list [(a,b),(b,a),(c,d),(d,c)]"
  assumes "an_sds {A1,A2,A3,A4} {a,b,c,d} sds"
  shows   "pmf (sds R1) (\<sigma> a) = pmf (sds R1) a"
proof -
  have "\<sigma> permutes {a,b,c,d}" by (simp add: \<sigma>_def insert_commute)
  with assms show ?thesis
apply (intro an_sds_automorphism_aux[OF R1_wf, of sds \<sigma>])
apply assumption
apply (simp only: R1_eval add_ac insert_commute list.map mset.simps empty_neutral image_mset_union image_mset_single snd_conv image_insert image_empty)
apply (simp only: eval_permutation_of_list alts.simps not_False_eq_True add_ac insert_commute)
apply simp_all
done
qed

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
(*    auto |> map (apfst (apply2 cterm) o apsnd (map (apply2 cterm))) *)
(*    find_manipulations (raw1, raw3)
    |> map (fn (a,b,c) => (cterm a, map (map cterm) b, map (apply2 cterm) c)) *)
(*      find_minimal_inefficient_supports raw1 
      |> map (fn (a,b,c) => (map cterm a, map (apfst cterm) b, cterm c)) *)
      pareto_losers raw5 |> map (fn (a,b,c) => (cterm a, cterm b, cterm c))
  end
  
\<close>

term lotteries_on

lemma pmf_of_list_wfI':
  "(\<forall>x\<in>set (map snd xs). x \<ge> 0) \<Longrightarrow> listsum (map snd xs) = 1 \<Longrightarrow> pmf_of_list_wf xs"
  unfolding pmf_of_list_wf_def by simp

lemma
  assumes "ex_post_efficient_sds {A1,A2,A3,A4} {a,b,c,d} sds"
  shows   "pmf (sds R5) d = 0"
apply (rule ex_post_efficient_sds.ex_post_efficient''[OF assms R5_wf, of A3 _ c])
apply (simp_all only: insert_iff HOL.simp_thms Set.ball_simps R5_eval
         eval_prefs_from_table of_weak_ranking_Cons of_weak_ranking_Nil
         list.set Union_insert Union_empty 
         Un_empty Un_empty_right empty_iff Un_insert_left Un_insert_right
         agents.simps alts.simps)
done


lemma
  assumes "sd_efficient_sds {A1,A2,A3,A4} {a,b,c,d} sds"
  shows   "\<exists>x\<in>{c,d}. pmf (sds R1) x = 0"
proof -
  from assms interpret sd_efficient_sds "{A1,A2,A3,A4}" "{a,b,c,d}" sds .
  show ?thesis
apply (rule SD_inefficient_support'[OF R1_wf, where p = "pmf_of_list [(a, 1/2), (b, 1/2)]" and i = A3])
apply (simp_all only: pmf_of_list_wfI' pmf_of_list_lottery list.map list.set fst_conv snd_conv 
         Set.ball_simps HOL.simp_thms listsum.Cons listsum.Nil insert_subset empty_subsetI 
         insert_iff insert_not_empty)
apply (subst (1 2 3 4) pref_profile_wf.SD_pref_profile[OF R1_wf])
apply (simp_all only: pmf_of_list_wfI' pmf_of_list_lottery list.map list.set fst_conv snd_conv 
         Set.ball_simps HOL.simp_thms listsum.Cons listsum.Nil insert_subset empty_subsetI 
         insert_iff insert_not_empty)
apply (simp_all only: pmf_of_list_wfI' pmf_of_list_lottery list.map list.set fst_conv snd_conv 
         Set.ball_simps HOL.simp_thms listsum.Cons listsum.Nil insert_subset empty_subsetI 
         insert_iff insert_not_empty finite_insert finite.emptyI pmf_of_set_lottery 
         card_insert_disjoint alts.simps empty_iff card_empty of_nat_Suc of_nat_0
         arith_simps one_add_one one_plus_numeral_commute one_plus_numeral)
apply (subst (1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32) R1_eval)
apply simp
apply (simp_all only: pmf_of_list_wfI' pmf_of_list_lottery list.map list.set fst_conv snd_conv 
         Set.ball_simps HOL.simp_thms listsum.Cons listsum.Nil insert_subset empty_subsetI 
         insert_iff insert_not_empty finite_insert finite.emptyI pmf_of_set_lottery 
         card_insert_disjoint alts.simps empty_iff card_empty of_nat_Suc of_nat_0
         arith_simps one_add_one one_plus_numeral_commute one_plus_numeral
         measure_pmf_of_list measure_pmf_of_set)
apply simp_all

apply (subst (1) pref_profile_wf.SD_pref_profile[OF R1_wf])
apply (simp_all only: pmf_of_list_wfI' pmf_of_list_lottery list.map list.set fst_conv snd_conv 
         Set.ball_simps HOL.simp_thms listsum.Cons listsum.Nil insert_subset empty_subsetI 
         insert_iff insert_not_empty)
apply (subst (1 2 3 4 5 6 7 8) R1_eval)
apply simp
apply (simp_all only: pmf_of_list_wfI' pmf_of_list_lottery list.map list.set fst_conv snd_conv 
         Set.ball_simps HOL.simp_thms listsum.Cons listsum.Nil insert_subset empty_subsetI 
         insert_iff insert_not_empty finite_insert finite.emptyI pmf_of_set_lottery 
         card_insert_disjoint alts.simps empty_iff card_empty of_nat_Suc of_nat_0
         arith_simps one_add_one one_plus_numeral_commute one_plus_numeral
         measure_pmf_of_list measure_pmf_of_set)
apply simp_all
done


find_theorems measure_pmf_of_set
find_theorems agenda A1
find_theorems "1 + numeral _"
apply (subst card_insert_disjoint)
apply (simp_all only: finite_insert finite.emptyI insert_iff empty_iff)
find_theorems "card (insert _ _)"
apply (subst pmf_of_set_lottery)
find_theorems "finite {}"
find_theorems measure pmf_of_set

find_theorems "_ \<in> insert _ _"
find_theorems "_ \<and> True"
find_theorems "insert _ _ \<subseteq> _"

locale strategyproof_an_sds =
  strategyproof_sds agents alts sds + an_sds agents alts sds
  for agents :: "'agent set" and alts :: "'alt set" and sds






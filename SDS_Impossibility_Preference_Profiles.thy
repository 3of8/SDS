theory SDS_Impossibility_Preference_Profiles
imports
  SDS_Automation
  SDS_Impossibility_Definitions
  SDS_Lowering
begin

context sds_impossibility_4_4
begin

preference_profile 
  agents: agents
  alts:   alts
where R1  = A1: [c, d], [a, b]    A2: [b, d], a, c      A3: a, b, [c, d]      A4: [a, c], [b, d]
  and R2  = A1: [a, c], [b, d]    A2: [c, d], a, b      A3: [b, d], a, c      A4: a, b, [c, d]
  and R3  = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: d, [a, b], c      A4: c, a, [b, d]
  and R4  = A1: [a, b], [c, d]    A2: [a, d], [b, c]    A3: c, [a, b], d      A4: d, c, [a, b]
  and R5  = A1: [c, d], [a, b]    A2: [a, b], [c, d]    A3: [a, c], d, b      A4: d, [a, b], c
  and R6  = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: [a, c], [b, d]    A4: d, b, a, c
  and R7  = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: a, c, d, b        A4: d, [a, b], c
  and R8  = A1: [a, b], [c, d]    A2: [a, c], [b, d]    A3: d, [a, b], c      A4: d, c, [a, b]
  and R9  = A1: [a, b], [c, d]    A2: [a, d], c, b      A3: d, c, [a, b]      A4: [a, b, c], d
  and R10 = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: [a, c], d, b      A4: [b, d], a, c
  and R11 = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: d, [a, b], c      A4: c, a, b, d
  and R12 = A1: [c, d], [a, b]    A2: [a, b], [c, d]    A3: [a, c], d, b      A4: [a, b, d], c
  and R13 = A1: [a, c], [b, d]    A2: [c, d], a, b      A3: [b, d], a, c      A4: a, b, d, c
  and R14 = A1: [a, b], [c, d]    A2: d, c, [a, b]      A3: [a, b, c], d      A4: a, d, c, b
  and R15 = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: [b, d], a, c      A4: a, c, d, b
  and R16 = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: a, c, d, b        A4: [a, b, d], c
  and R17 = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: [a, c], [b, d]    A4: d, [a, b], c
  and R18 = A1: [a, b], [c, d]    A2: [a, d], [b, c]    A3: [a, b, c], d      A4: d, c, [a, b]
  and R19 = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: [b, d], a, c      A4: [a, c], [b, d]
  and R20 = A1: [b, d], a, c      A2: b, a, [c, d]      A3: a, c, [b, d]      A4: d, c, [a, b]
  and R21 = A1: [a, d], c, b      A2: d, c, [a, b]      A3: c, [a, b], d      A4: a, b, [c, d]
  and R22 = A1: [a, c], d, b      A2: d, c, [a, b]      A3: d, [a, b], c      A4: a, b, [c, d]
  and R23 = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: [a, c], [b, d]    A4: [a, b, d], c
  and R24 = A1: [c, d], [a, b]    A2: d, b, a, c        A3: c, a, [b, d]      A4: b, a, [c, d]
  and R25 = A1: [c, d], [a, b]    A2: [b, d], a, c      A3: a, b, [c, d]      A4: a, c, [b, d]
  and R26 = A1: [b, d], [a, c]    A2: [c, d], [a, b]    A3: a, b, [c, d]      A4: a, c, [b, d]
  and R27 = A1: [a, b], [c, d]    A2: [b, d], a, c      A3: [a, c], [b, d]    A4: [c, d], a, b
  and R28 = A1: [c, d], a, b      A2: [b, d], a, c      A3: a, b, [c, d]      A4: a, c, [b, d]
  and R29 = A1: [a, c], d, b      A2: [b, d], a, c      A3: a, b, [c, d]      A4: d, c, [a, b]
  and R30 = A1: [a, d], c, b      A2: d, c, [a, b]      A3: c, [a, b], d      A4: [a, b], d, c
  and R31 = A1: [b, d], a, c      A2: [a, c], d, b      A3: c, d, [a, b]      A4: [a, b], c, d
  and R32 = A1: [a, c], d, b      A2: d, c, [a, b]      A3: d, [a, b], c      A4: [a, b], d, c
  and R33 = A1: [c, d], [a, b]    A2: [a, c], d, b      A3: a, b, [c, d]      A4: d, [a, b], c
  and R34 = A1: [a, b], [c, d]    A2: a, c, d, b        A3: b, [a, d], c      A4: c, d, [a, b]
  and R35 = A1: [a, d], c, b      A2: a, b, [c, d]      A3: [a, b, c], d      A4: d, c, [a, b]
  and R36 = A1: [c, d], [a, b]    A2: [a, c], d, b      A3: [b, d], a, c      A4: a, b, [c, d]
  and R37 = A1: [a, c], [b, d]    A2: [b, d], [a, c]    A3: a, b, [c, d]      A4: c, d, [a, b]
  and R38 = A1: [c, d], a, b      A2: [b, d], a, c      A3: a, b, [c, d]      A4: [a, c], b, d
  and R39 = A1: [a, c], d, b      A2: [b, d], a, c      A3: a, b, [c, d]      A4: [c, d], a, b
  and R40 = A1: [a, d], c, b      A2: [a, b], c, d      A3: [a, b, c], d      A4: d, c, [a, b]
  and R41 = A1: [a, d], c, b      A2: [a, b], d, c      A3: [a, b, c], d      A4: d, c, [a, b]
  and R42 = A1: [c, d], [a, b]    A2: [a, b], [c, d]    A3: d, b, a, c        A4: c, a, [b, d]
  and R43 = A1: [a, b], [c, d]    A2: [c, d], [a, b]    A3: d, [a, b], c      A4: a, [c, d], b
  and R44 = A1: [c, d], [a, b]    A2: [a, c], d, b      A3: [a, b], d, c      A4: [a, b, d], c
  and R45 = A1: [a, c], d, b      A2: [b, d], a, c      A3: [a, b], c, d      A4: [c, d], b, a
  and R46 = A1: [b, d], a, c      A2: d, c, [a, b]      A3: [a, c], [b, d]    A4: b, a, [c, d]
  and R47 = A1: [a, b], [c, d]    A2: [a, d], c, b      A3: d, c, [a, b]      A4: c, [a, b], d
  by (simp_all add: agents alts)

          
derive_orbit_equations (an_sds)
  R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20
  R21 R22 R23 R24 R25 R26 R27 R28 R29 R30 R31 R32 R33 R34 R35 R36 R37 R38 R39 R40
  R41 R42 R43 R44 R45 R46 R47
  by simp_all

print_theorems

derive_support_conditions (ex_post_efficient_sds sd_efficient_sds)
  R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20
  R21 R22 R23 R24 R25 R26 R27 R28 R29 R30 R31 R32 R33 R34 R35 R36 R37 R38 R39 R40
  R41 R42 R43 R44 R45 R46 R47
  by (simp_all add: agent_iff alt_iff)

print_theorems

derive_strategyproofness_conditions (strategyproof_an_sds)
  R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20
  R21 R22 R23 R24 R25 R26 R27 R28 R29 R30 R31 R32 R33 R34 R35 R36 R37 R38 R39 R40
  R41 R42 R43 R44 R45 R46 R47
  by (simp_all add: agent_iff alt_iff)


lemma pmf_sds_nonneg: "is_pref_profile R \<Longrightarrow> \<forall>x\<in>alts. pmf (sds R) x \<ge> 0" by (simp_all add: pmf_nonneg)

lemmas lottery_conditions = 
  pmf_sds_nonneg [unfolded alt_iff] lottery_prob_alts'[OF sds_wf]

lemmas R_wfs = 
  R1_wf R2_wf R3_wf R4_wf R5_wf R6_wf R7_wf R8_wf R9_wf R10_wf R11_wf R12_wf R13_wf R14_wf R15_wf 
  R16_wf R17_wf R18_wf R19_wf R20_wf R21_wf R22_wf R23_wf R24_wf R25_wf R26_wf R27_wf R28_wf 
  R29_wf R30_wf R31_wf R32_wf R33_wf R34_wf R35_wf R36_wf R37_wf R38_wf R39_wf R40_wf R41_wf 
  R42_wf R43_wf R44_wf R45_wf R46_wf R47_wf

lemma foo: "(\<And>x. P x) \<Longrightarrow> P (pmf (sds R) x)"
  by simp

ML \<open>
val foo =
  let
    val eq = op aconv o apply2 Thm.term_of
    fun go acc ct =
      case Thm.term_of ct of
        Const (@{const_name pmf}, _) $ _ $ _ => insert eq ct acc
      | _ $ _ => go (go acc (Thm.dest_arg ct)) (Thm.dest_fun ct)
      | Abs (_, _, _) => go acc (Thm.dest_abs NONE ct |> snd)
      | _ => acc
  in
    go []
  end
  
\<close>

lemma meta_spec_pmf:
  "(\<And>x. x \<ge> 0 \<Longrightarrow> P x) \<Longrightarrow> P (pmf p (x :: 'alt))"
  by (simp add: pmf_nonneg)

ML \<open>

fun foo_tac ctxt i =
  let
    fun tac {concl, context = ctxt, ...} =
      let
        val ts = foo concl
        fun generalise_tac ct =
          let
            val (ct1, ct2) = ct |> Thm.dest_comb |> apfst Thm.dest_arg
            val thm = Thm.instantiate' [] [NONE, SOME ct1, SOME ct2] @{thm meta_spec_pmf}
          in
            DETERM (HEADGOAL (resolve_tac ctxt [thm]))
          end
      in
        FIRST (map generalise_tac ts)
      end
  in
    Subgoal.FOCUS_PARAMS tac ctxt i
  end

\<close>

lemma R10_bc [simp]: "pmf (sds R10) b = 0" "pmf (sds R10) c = 0"
  using R10.support R10.orbits by auto

lemma R10_ad [simp]: "pmf (sds R10) a = 1/2" "pmf (sds R10) d = 1/2"
  using lottery_conditions[OF R10_wf] R10_bc R10.orbits by simp_all


lemma R26_bc [simp]: "pmf (sds R26) b = 0" "pmf (sds R26) c = 0"
  using R26.support R26.orbits by auto

lemma R26_d [simp]: "pmf (sds R26) d = 1 - pmf (sds R26) a"
  using lottery_conditions[OF R26_wf] R26_bc by simp


lemma R27_bc [simp]: "pmf (sds R27) b = 0" "pmf (sds R27) c = 0"
  using R27.support R27.orbits by auto

lemma R27_d [simp]: "pmf (sds R27) d = 1 - pmf (sds R27) a"
  using lottery_conditions[OF R27_wf] R27_bc by simp


lemma R28_bc [simp]: "pmf (sds R28) b = 0" "pmf (sds R28) c = 0"
  using R28.support R28.orbits by auto

lemma R28_d [simp]: "pmf (sds R28) d = 1 - pmf (sds R28) a"
  using lottery_conditions[OF R28_wf] R28_bc by simp


lemma R29_bc [simp]: "pmf (sds R29) b = 0" "pmf (sds R29) c = 0"
  using R29.support R29.orbits by auto

lemma R29_ac [simp]: "pmf (sds R29) a = 1/2" "pmf (sds R29) d = 1/2"
  using lottery_conditions[OF R29_wf] R29_bc R29.orbits by simp_all


lemmas R43_bc [simp] = R43.support

lemma R43_ad [simp]: "pmf (sds R43) a = 1/2" "pmf (sds R43) d = 1/2"
  using lottery_conditions[OF R43_wf] R43_bc R43.orbits by simp_all

lemma R45 [simp]: "pmf (sds R45) a = 1/4" "pmf (sds R45) b = 1/4" 
           "pmf (sds R45) c = 1/4" "pmf (sds R45) d = 1/4"
  using R45.orbits lottery_conditions[OF R45_wf] by simp_all


lemma R39_b [simp]: "pmf (sds R39) b = 0"
  using R39_R29.strategyproofness R29_R39.strategyproofness R39.support
        lottery_conditions[OF R39_wf] by auto

lemma R39_a_le_onehalf: "pmf (sds R39) a \<le> 1/2"
  using R39_R29.strategyproofness R29_R39.strategyproofness
        lottery_conditions[OF R39_wf] by auto

lemma R36_a_R39_a: "pmf (sds R36) a \<le> pmf (sds R39) a"
  using R36_R39.strategyproofness lottery_conditions[OF R39_wf] lottery_conditions[OF R36_wf]
  by simp

lemma R36_a_le_onehalf: "pmf (sds R36) a \<le> 1/2"
  using R36_a_R39_a R39_a_le_onehalf by simp

lemma R36_a [simp]: "pmf (sds R36) a = 1/2" and R36_b [simp]: "pmf (sds R36) b = 0"
  using R10_R36.strategyproofness R36_R10.strategyproofness R36.support R36_a_le_onehalf
  by auto

lemma R36_d [simp]: "pmf (sds R36) d = 1/2 - pmf (sds R36) c"
  using lottery_conditions[OF R36_wf] by simp

lemma R39_a [simp]: "pmf (sds R39) a = 1/2"
  using R36_R39.strategyproofness R39_R36.strategyproofness lottery_conditions[OF R39_wf] 
  by auto

lemma R39_d [simp]: "pmf (sds R39) d = 1/2 - pmf (sds R39) c"
  using lottery_conditions[OF R39_wf] by simp


lemma R15_c [simp]: "pmf (sds R15) c = 0"
  using R10_R15.strategyproofness R15_R10.strategyproofness R15.support
        lottery_conditions[OF R15_wf]
  by auto

lemma R15_a_ge_onehalf: "pmf (sds R15) a \<ge> 1/2"
  using R10_R15.strategyproofness R15_R10.strategyproofness R15.support
        lottery_conditions[OF R15_wf]
  by auto


lemma R28_a_R39_c: "pmf (sds R28) a \<le> pmf (sds R39) c + 1/2"
  using R28_R39.strategyproofness R39_R28.strategyproofness 
  by auto

lemma R19_R1: "(pmf (sds R1) b = 0 \<and> pmf (sds R19) b = 0) \<or> 
               (pmf (sds R19) c = 0)"
  using R19_R1.strategyproofness R1_R19.strategyproofness R19.support R1.support
        lottery_conditions[OF R1_wf] lottery_conditions[OF R19_wf]
  [[smt_oracle]]  by smt

lemma R19_aux: 
  "pmf (sds R19) d = 1/2 \<or> 
   (pmf (sds R19) a \<ge> 1/2 \<and> pmf (sds R19) c = 0 \<and> pmf (sds R19) b > 0)"
  using R19_R10.strategyproofness R10_R19.strategyproofness R19.support
        lottery_conditions[OF R19_wf]
  by force



(*
lemma P
proof (rule disjE[OF R19_aux], goal_cases)
  case 1
  have P

  using R15_R19.strategyproofness R19_R15.strategyproofness R19_aux
        R15_a_ge_onehalf lottery_conditions[OF R19_wf] lottery_conditions[OF R15_wf]
    apply (auto simp: 1)
next
  case 2
  hence "pmf (sds R19) b = 0"
  using R15_R19.strategyproofness R19_R15.strategyproofness R19_aux
        R15_a_ge_onehalf lottery_conditions[OF R19_wf] lottery_conditions[OF R15_wf]
    apply auto
*)

find_theorems R19
find_theorems R19 name:strat


lemmas R12_b [simp] = R12.support

lemma R12_c [simp]: "pmf (sds R12) c = 0"
  using R12_R10.strategyproofness lottery_conditions[OF R12_wf] by auto

lemma R12_d [simp]: "pmf (sds R12) d = 1 - pmf (sds R12) a"
  using lottery_conditions[OF R12_wf] by simp

lemma R12_a_ge_one_half: "pmf (sds R12) a \<ge> 1/2"
  using R10_R12.strategyproofness lottery_conditions[OF R12_wf]
  by auto




lemma pmf_sum_eq_1_iff: "pmf p x + pmf p y = 1 \<longleftrightarrow> pmf p y = 1 - pmf p x"
  by linarith

lemma less_or_eq: 
  "x < y \<or> x = y \<longleftrightarrow> x \<le> (y::real)"
  "x < y \<or> y = x \<longleftrightarrow> x \<le> (y::real)" by linarith+



(*

lemmas strategyproofness =
  R10_R19.strategyproofness(2) R36_R39.strategyproofness R36_R10.strategyproofness(2)
  R19_R1.strategyproofness R19_R27.strategyproofness(2) R15_R13.strategyproofness
  R15_R7.strategyproofness R15_R5.strategyproofness R17_R3.strategyproofness(2)
  R2_R38.strategyproofness R2_R1.strategyproofness R13_R15.strategyproofness 
  R5_R17.strategyproofness R1_R2.strategyproofness R1_R19.strategyproofness
  R39_R2.strategyproofness R44_R40.strategyproofness R44_R12.strategyproofness
  R7_R43.strategyproofness(1) R27_R19.strategyproofness(1) R23_R18.strategyproofness
  R23_R12.strategyproofness(2) R42_R24.strategyproofness R42_R3.strategyproofness
  R47_R30.strategyproofness R6_R42.strategyproofness R6_R19.strategyproofness(2)
  R12_R16.strategyproofness(2) R9_R40.strategyproofness R9_R18.strategyproofness(2)
  R33_R22.strategyproofness R33_R5.strategyproofness R25_R26.strategyproofness(1)
  R17_R7.strategyproofness(2) R17_R11.strategyproofness(2) R20_R21.strategyproofness
  R34_R24.strategyproofness R5_R10.strategyproofness(2) R31_R38.strategyproofness
  R30_R41.strategyproofness R30_R21.strategyproofness R21_R35.strategyproofness
  R41_R31.strategyproofness R32_R28.strategyproofness(1) R32_R22.strategyproofness
  R35_R9.strategyproofness R22_R29.strategyproofness(2) R23_R19.strategyproofness(2)
  R42_R11.strategyproofness R12_R10.strategyproofness(1) R24_R34.strategyproofness
  R25_R36.strategyproofness R37_R42.strategyproofness(1) R13_R27.strategyproofness(2)
  R27_R13.strategyproofness(2) R14_R16.strategyproofness R14_R34.strategyproofness
  R14_R9.strategyproofness(2) R45_R31.strategyproofness(2) R39_R29.strategyproofness(2)
  R46_R37.strategyproofness(1) R46_R20.strategyproofness R8_R26.strategyproofness(1)
  R28_R39.strategyproofness(1) R4_R47.strategyproofness(2) R4_R18.strategyproofness
  R4_R8.strategyproofness*)

(*lemma plus_eq_1_iff: "pmf p x + pmf p y = 1 \<longleftrightarrow> pmf p y = 1 - (pmf p x::real)" 
  by linarith*)


lemmas strategyproofness =
  R10_R19.strategyproofness(2) 
  R19_R1.strategyproofness R19_R27.strategyproofness(2) R15_R13.strategyproofness
  R15_R7.strategyproofness R15_R5.strategyproofness R17_R3.strategyproofness(2)
  R2_R38.strategyproofness R2_R1.strategyproofness R13_R15.strategyproofness 
  R5_R17.strategyproofness R1_R2.strategyproofness R1_R19.strategyproofness
  R39_R2.strategyproofness R44_R40.strategyproofness R44_R12.strategyproofness
  R7_R43.strategyproofness(1) R27_R19.strategyproofness(1) R23_R18.strategyproofness
  R23_R12.strategyproofness(2) R42_R24.strategyproofness R42_R3.strategyproofness
  R47_R30.strategyproofness R6_R42.strategyproofness R6_R19.strategyproofness(2)
  R12_R16.strategyproofness(2) R9_R40.strategyproofness R9_R18.strategyproofness(2)
  R33_R22.strategyproofness R33_R5.strategyproofness R25_R26.strategyproofness(1)
  R17_R7.strategyproofness(2) R17_R11.strategyproofness(2) R20_R21.strategyproofness

  R34_R24.strategyproofness R5_R10.strategyproofness(2) R31_R38.strategyproofness
  R30_R41.strategyproofness R30_R21.strategyproofness R21_R35.strategyproofness
  R41_R31.strategyproofness R32_R28.strategyproofness(1) R32_R22.strategyproofness
  R35_R9.strategyproofness R22_R29.strategyproofness(2) R23_R19.strategyproofness(2)
  R42_R11.strategyproofness R24_R34.strategyproofness
  R25_R36.strategyproofness R37_R42.strategyproofness(1) R13_R27.strategyproofness(2)
  R27_R13.strategyproofness(2) R14_R16.strategyproofness R14_R34.strategyproofness
  R14_R9.strategyproofness(2) R45_R31.strategyproofness(2)
  R46_R37.strategyproofness(1) R46_R20.strategyproofness R8_R26.strategyproofness(1)
  R28_R39.strategyproofness(1) R4_R47.strategyproofness(2) R4_R18.strategyproofness
  R4_R8.strategyproofness

lemmas additional_equations = 
  R10_bc R10_ad R26_bc R27_bc R28_bc R29_bc R29_ac R43_bc R43_ad R45
  R39_b R36_a R36_d R39_a R39_d R15_c R12_c R12_d R12_b

lemmas orbits = R37.orbits

lemmas supports =
  R3.support R9.support R11.support R16.support R17.support R18.support R47.support

lemmas additional_inequalities = R19_R1 (* R12_a_ge_one_half *)

declare [[smt_certificates = "SDS_Impossibility.certs"]]

lemma absurd: False
  using R_wfs [THEN lottery_conditions(1)] R_wfs [THEN lottery_conditions(2)]
        orbits supports strategyproofness additional_equations additional_inequalities
(*  using [[smt_oracle]] by smt*)

apply -
apply (tactic \<open>Object_Logic.rulify_tac @{context} 1\<close>)
(* apply (atomize (full)) *)
apply (elim conjE) 
apply (simp only: HOL.simp_thms True_implies_equals triv_forall_equality order.refl add_0_left
   add_0_right pmf_sum_eq_1_iff less_or_eq_real)
apply (atomize (full))
apply (tactic \<open>foo_tac @{context} 1\<close>)+
apply (tactic \<open>Object_Logic.rulify_tac @{context} 1\<close>)
apply hypsubst
apply (simp only: HOL.simp_thms True_implies_equals triv_forall_equality order.refl 
  add_0_left add_0_right less_or_eq_real)
apply (atomize (full))
apply (intro allI)
(*apply (tactic \<open>Object_Logic.rulify_tac @{context} 1\<close>)*)
proof -
  case goal1
  thus ?case
    using [[smt_oracle]] 
      by smt
qed

(*
apply -
(*apply (atomize (full))*)
apply (elim conjE)
apply (simp only: HOL.simp_thms True_implies_equals triv_forall_equality order.refl add_0_left
   add_0_right plus_eq_1_iff )
apply (atomize (full))
apply (tactic \<open>foo_tac @{context} 1\<close>)+
apply (tactic \<open>Object_Logic.rulify_tac @{context} 1\<close>)
apply hypsubst
apply (simp only: HOL.simp_thms True_implies_equals triv_forall_equality order.refl 
  add_0_left add_0_right)
apply linarith*)


declare [[smt_certificates = ""]]

end


subsection \<open>Lifting to more than 4 agents and alternatives\<close>

(* TODO: Move? *)
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

lemma absurd: False
proof -
  from card_ge_4E[OF finite_agents agents_ge_4] guess A1 A2 A3 A4 .
  note agents = this
  from card_ge_4E[OF finite_alts alts_ge_4] guess a b c d .
  note alts = this
  def agents' \<equiv> "{A1,A2,A3,A4}" and alts' \<equiv> "{a,b,c,d}"
  from agents alts 
    interpret sds_lowering_anonymous_neutral_sdeff_stratproof agents alts sds agents' alts'
    unfolding agents'_def alts'_def by unfold_locales simp_all
  from agents alts 
    interpret sds_impossibility_4_4 agents' alts' lowered A1 A2 A3 A4 a b c d
    by unfold_locales (simp_all add: agents'_def alts'_def)
  from absurd show False .
qed

end

end
*)
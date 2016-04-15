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
  "(pmf (sds R19) d = 1/2 \<and> pmf (sds R19) b = 0) \<or> 
   (pmf (sds R19) a \<ge> 1/2 \<and> pmf (sds R19) c = 0 \<and> pmf (sds R19) b > 0)"
  using R19_R10.strategyproofness R10_R19.strategyproofness R19.support
        lottery_conditions[OF R19_wf]
  by force

lemma R22_d_ge_one_half: "pmf (sds R22) d \<ge> 1/2"
  using R22_R29.strategyproofness R22.support lottery_conditions[OF R22_wf]
  by auto

lemma R5_d_ge_one_half: "pmf (sds R5) d \<ge> 1/2"
  using R5_R10.strategyproofness(2) R5.support lottery_conditions[OF R5_wf] by auto

lemma R5_aux: "pmf (sds R5) d = 1/2 \<Longrightarrow> pmf (sds R5) c = 0"
  using R5.support R5_R10.strategyproofness(2) lottery_conditions[OF R5_wf] R5_d_ge_one_half
  by auto

lemma R5_R17: "pmf (sds R17) d \<ge> pmf (sds R5) d"
proof -
  from R5_R17.strategyproofness R17.support
    lottery_conditions[OF R5_wf] lottery_conditions[OF R17_wf]
    show "pmf (sds R17) d \<ge> pmf (sds R5) d" by smt
qed

lemma R5_R33: "pmf (sds R5) a \<le> pmf (sds R33) a"
  using R33_R5.strategyproofness R5.support R33.support by auto

lemma R33_R22: "pmf (sds R33) d \<le> pmf (sds R22) d" "pmf (sds R22) c \<le> pmf (sds R33) c"
  using R33_R22.strategyproofness R22_R33.strategyproofness by auto

lemma R7_aux: "pmf (sds R7) d \<le> 1/2" "pmf (sds R7) d < 1/2 \<or> (pmf (sds R7) a = 1/2 \<and> pmf (sds R7) c = 0)"
  using R7_R43.strategyproofness(1) R7.support lottery_conditions[OF R7_wf] by auto

lemma R32_d [simp]: "pmf (sds R32) d = pmf (sds R28) a"
proof -
  have "pmf (sds R28) a \<le> pmf (sds R32) d"
    using R32_R28.strategyproofness
          lottery_conditions[OF R32_wf] lottery_conditions[OF R28_wf] by auto
  thus "pmf (sds R32) d = pmf (sds R28) a"
    using R28_R32.strategyproofness lottery_conditions[OF R32_wf] lottery_conditions[OF R28_wf] 
    by auto
qed



lemma R22_aux: "pmf (sds R22) d = 1/2 \<longrightarrow> pmf (sds R22) c = 0"
proof -
  from R22_R29.strategyproofness R22.support R29_R22.strategyproofness lottery_conditions[OF R22_wf]
    show "pmf (sds R22) d = 1/2 \<longrightarrow> pmf (sds R22) c = 0" by auto
qed

lemma R2_R1: "pmf (sds R2) b \<le> pmf (sds R1) b" "pmf (sds R2) a \<ge> pmf (sds R1) a"
proof -
  from R2_R1.strategyproofness R1_R2.strategyproofness
       lottery_conditions[OF R2_wf] lottery_conditions[OF R1_wf]
    show "pmf (sds R2) b \<le> pmf (sds R1) b" "pmf (sds R2) a \<ge> pmf (sds R1) a" by auto
qed

lemma R2_R38: "pmf (sds R2) d \<ge> pmf (sds R38) d" "pmf (sds R2) b \<le> pmf (sds R38) b"
proof -
  from R2_R38.strategyproofness R38_R2.strategyproofness
       lottery_conditions[OF R2_wf] lottery_conditions[OF R38_wf] 
    show "pmf (sds R2) d \<ge> pmf (sds R38) d" "pmf (sds R2) b \<le> pmf (sds R38) b" by auto
qed

lemma R27_R19:
  "pmf (sds R27) d \<le> pmf (sds R19) d + pmf (sds R19) c"
  using R19_R27.strategyproofness by simp

lemma R13_aux: "pmf (sds R13) b = 0" "pmf (sds R13) c = 0" "pmf (sds R13) d = 1 - pmf (sds R13) a"
  and R27_R13 [simp]: "pmf (sds R27) a = pmf (sds R13) a" 
proof -
  from R27_R13.strategyproofness R13_R27.strategyproofness
       lottery_conditions[OF R13_wf]
    show "pmf (sds R13) b = 0" "pmf (sds R13) c = 0" "pmf (sds R13) d = 1 - pmf (sds R13) a"
         "pmf (sds R27) a = pmf (sds R13) a" by auto
qed

lemma R15_aux: "pmf (sds R15) b > 0 \<or> (pmf (sds R15) b = 0 \<and> pmf (sds R15) a = pmf (sds R13) a \<and> pmf (sds R15) d = 1 - pmf (sds R13) a)"
proof -
  from R15_R13.strategyproofness R13_R15.strategyproofness 
       lottery_conditions[OF R15_wf] lottery_conditions[OF R13_wf]
    show "pmf (sds R15) b > 0 \<or> (pmf (sds R15) b = 0 \<and> pmf (sds R15) a = pmf (sds R13) a \<and> pmf (sds R15) d = 1 - pmf (sds R13) a)"
    by auto
qed


lemma R17_R11: "pmf (sds R17) c \<le> pmf (sds R11) c" "pmf (sds R17) a \<ge> pmf (sds R11) a"
proof -
find_theorems R11
  from R17_R11.strategyproofness(2) R11_R17.strategyproofness(2) R17.support R11.support 
    show "pmf (sds R17) c \<le> pmf (sds R11) c" "pmf (sds R17) a \<ge> pmf (sds R11) a" by auto
qed

lemmas R12_b [simp] = R12.support

lemma R12_c [simp]: "pmf (sds R12) c = 0"
  using R12_R10.strategyproofness lottery_conditions[OF R12_wf] by auto

lemma R12_d [simp]: "pmf (sds R12) d = 1 - pmf (sds R12) a"
  using lottery_conditions[OF R12_wf] by simp

lemma R12_a_ge_one_half: "pmf (sds R12) a \<ge> 1/2"
  using R10_R12.strategyproofness lottery_conditions[OF R12_wf]
  by auto

lemmas R37_bd [simp] = R37.orbits

lemma R37_b [simp]: "pmf (sds R37) b = 1/2 - pmf (sds R37) a"
  using lottery_conditions[OF R37_wf] by simp

lemma R44 [simp]: 
  "pmf (sds R44) a = pmf (sds R12) a" "pmf (sds R44) d = 1 - pmf (sds R12) a"
  "pmf (sds R44) b = 0" "pmf (sds R44) c = 0"
proof -
  from R44_R12.strategyproofness R12_R44.strategyproofness R44.support lottery_conditions[OF R44_wf]
    show "pmf (sds R44) a = pmf (sds R12) a" "pmf (sds R44) c = 0"
         "pmf (sds R44) d = 1 - pmf (sds R12) a" by auto
qed (insert R44.support, simp_all)

lemma R9_a [simp]: "pmf (sds R9) a = pmf (sds R35) a"
 using R9_R35.strategyproofness R35_R9.strategyproofness R9.support R35.support by auto


lemma R9_R14: "pmf (sds R9) a \<le> pmf (sds R14) a" "pmf (sds R9) d \<ge> pmf (sds R14) d"
proof -
  from R9_R14.strategyproofness(2) R14_R9.strategyproofness(2) lottery_conditions[OF R9_wf] lottery_conditions[OF R14_wf] R9.support R14.support
    show "pmf (sds R9) a \<le> pmf (sds R14) a" "pmf (sds R9) d \<ge> pmf (sds R14) d"
    by linarith+
qed

lemma R35_R21: "pmf (sds R35) c \<le> pmf (sds R21) c" "pmf (sds R35) a \<ge> pmf (sds R21) a"
               "pmf (sds R35) c = pmf (sds R21) c \<longrightarrow> pmf (sds R35) a = pmf (sds R21) a"
proof -
  from R21_R35.strategyproofness R35_R21.strategyproofness R35.support R21.support
         lottery_conditions[OF R21_wf] lottery_conditions[OF R35_wf]
    show "pmf (sds R35) c \<le> pmf (sds R21) c" "pmf (sds R35) a \<ge> pmf (sds R21) a"
         "pmf (sds R35) c = pmf (sds R21) c \<longrightarrow> pmf (sds R35) a = pmf (sds R21) a" by auto
qed

lemma R20_R21: "pmf (sds R21) c \<le> pmf (sds R20) a + pmf (sds R20) c"
proof -
  from R20_R21.strategyproofness R21.support lottery_conditions[OF R20_wf]
    show "pmf (sds R21) c \<le> pmf (sds R20) a + pmf (sds R20) c" by auto
qed

lemma R30_R41: "pmf (sds R41) c \<le> pmf (sds R30) c" "pmf (sds R41) a \<ge> pmf (sds R30) a"
proof -
  from R30_R41.strategyproofness R41_R30.strategyproofness R30.support R41.support
    show "pmf (sds R41) c \<le> pmf (sds R30) c" "pmf (sds R41) a \<ge> pmf (sds R30) a" by auto
qed

lemma R41_R31: "pmf (sds R31) c \<ge> pmf (sds R41) b + pmf (sds R41) d"
proof -
  from R41_R31.strategyproofness R41.support lottery_conditions[OF R31_wf] lottery_conditions[OF R41_wf]
    show "pmf (sds R31) c \<ge> pmf (sds R41) b + pmf (sds R41) d" by auto
qed

lemma R5_R15: "pmf (sds R5) d \<le> pmf (sds R15) a \<or> pmf (sds R5) a < pmf (sds R15) d"
proof -
  from R15_R5.strategyproofness R5_R15.strategyproofness 
    show "pmf (sds R5) d \<le> pmf (sds R15) a \<or> pmf (sds R5) a < pmf (sds R15) d"
   apply auto
   using R15_c R5.support R15_a_ge_onehalf lottery_conditions[OF R5_wf] lottery_conditions[OF R15_wf]
   R5_d_ge_one_half
   apply auto
   done
qed

lemma R23_R19: "pmf (sds R19) a \<ge> pmf (sds R23) c" "pmf (sds R19) c \<ge> pmf (sds R23) c"
proof - 
  from R23_R19.strategyproofness R23.support
       lottery_conditions[OF R19_wf] lottery_conditions[OF R23_wf] 
    show "pmf (sds R19) a \<ge> pmf (sds R23) c" "pmf (sds R19) c \<ge> pmf (sds R23) c"
    by auto
qed

lemma R23_R18: "pmf (sds R23) c \<le> pmf (sds R18) d" "pmf (sds R23) d \<ge> pmf (sds R18) c"
proof -
  from R23_R18.strategyproofness R18_R23.strategyproofness R18.support R23.support
    show "pmf (sds R23) c \<le> pmf (sds R18) d" "pmf (sds R23) d \<ge> pmf (sds R18) c" by auto
qed

lemma R23_R12: "pmf (sds R12) a \<le> pmf (sds R23) c + pmf (sds R23) a"
  using R23_R12.strategyproofness(2) by simp

lemma R16_R12: "pmf (sds R16) c + pmf (sds R16) a \<le> pmf (sds R12) a"
  using R12_R16.strategyproofness(2) R16.support lottery_conditions[OF R16_wf] by auto

lemma R40_R35: "pmf (sds R40) a \<le> pmf (sds R35) a"
proof -
  from R9_R40.strategyproofness R9.support R40.support show ?thesis by auto
qed

lemma R18_c [simp]: "pmf (sds R18) c = pmf (sds R9) c"
proof -
  from R9_R18.strategyproofness(2) R18_R9.strategyproofness(2) R18.support R9.support
       lottery_conditions[OF R9_wf] lottery_conditions[OF R18_wf]
    show "pmf (sds R18) c = pmf (sds R9) c" by auto
qed

lemma R7_a_le_one_half: "pmf (sds R7) a \<le> 1/2"
proof -
  from R43_R7.strategyproofness(1) R7.support R43.support lottery_conditions[OF R7_wf]
    show "pmf (sds R7) a \<le> 1/2" by auto
qed

lemma R45_R31: "pmf (sds R31) c \<ge> 1/4 \<or> pmf (sds R31) a > 1/4"
proof -
  from R45_R31.strategyproofness(2) R31_R45.strategyproofness(2) lottery_conditions[OF R31_wf] 
  show "pmf (sds R31) c \<ge> 1/4 \<or> pmf (sds R31) a > 1/4"
    by auto
qed

lemma R30_R21: "pmf (sds R21) a + pmf (sds R21) d \<le> pmf (sds R30) a + pmf (sds R30) d"
using R30_R21.strategyproofness R21_R30.strategyproofness R30.support R21.support
    by auto

lemma R32_R22: "pmf (sds R32) a \<le> pmf (sds R22) a" "pmf (sds R22) d \<le> pmf (sds R28) a"
proof -
  from R32_R22.strategyproofness R22_R32.strategyproofness R32.support R22.support 
    show "pmf (sds R32) a \<le> pmf (sds R22) a" "pmf (sds R22) d \<le> pmf (sds R28) a"
    by auto
qed

lemma R11_R42: "pmf (sds R11) d \<le> pmf (sds R42) c + pmf (sds R42) a"
proof -
  from R42_R11.strategyproofness R11.support lottery_conditions[OF R42_wf]
    show "pmf (sds R11) d \<le> pmf (sds R42) c + pmf (sds R42) a" by auto
qed

lemma R25_a_ge_one_half: "pmf (sds R25) a \<ge> 1/2" and R36_c_le_one_half: "pmf (sds R36) c \<le> 1/2"
proof -
  from R25_R36.strategyproofness R36_R25.strategyproofness R25.support 
    show "pmf (sds R25) a \<ge> 1/2" "pmf (sds R36) c \<le> 1/2"
    apply auto
    using lottery_conditions[OF R25_wf] lottery_conditions[OF R36_wf]
    apply auto
    done
qed

lemma R14_R16: "pmf (sds R16) c \<le> pmf (sds R14) d" "pmf (sds R16) d \<ge> pmf (sds R14) c"
proof -
  from R14_R16.strategyproofness R16_R14.strategyproofness R14.support R16.support
    show "pmf (sds R16) c \<le> pmf (sds R14) d" "pmf (sds R16) d \<ge> pmf (sds R14) c"
    by auto
qed

lemma R14_R34: "pmf (sds R34) c \<ge> pmf (sds R14) b + pmf (sds R14) d"
proof -
  from R14_R34.strategyproofness R14.support lottery_conditions[OF R34_wf] lottery_conditions[OF R14_wf]
    show "pmf (sds R34) c \<ge> pmf (sds R14) b + pmf (sds R14) d"
    by auto
qed

lemma R46_R37: "pmf (sds R46) c \<le> 1 / 2 - pmf (sds R37) a"
proof -
  (* useless? *)
  from R46_R37.strategyproofness(2) R37_R46.strategyproofness(2) lottery_conditions[OF R46_wf]
   show "pmf (sds R46) c \<le> 1 / 2 - pmf (sds R37) a" by auto
qed

lemma R46_R20: "pmf (sds R46) a \<le> pmf (sds R20) a" "pmf (sds R46) c \<ge> pmf (sds R20) c"
proof -
  (* useless? *)
  from R46_R20.strategyproofness R20_R46.strategyproofness R20.support R46.support
    show "pmf (sds R46) a \<le> pmf (sds R20) a" "pmf (sds R46) c \<ge> pmf (sds R20) c"
    by auto
qed

(* Should be redundant, but isn't - why? *)
lemma R8_d [simp]: "pmf (sds R8) d = 1 - pmf (sds R8) a"
  using R8_R26.strategyproofness(2) R26_R8.strategyproofness(2) R8.support
  apply auto
  using lottery_conditions[OF R8_wf]
  apply auto
  done

lemma R8_c [simp]: "pmf (sds R8) c = 0"
  using lottery_conditions[OF R8_wf] R8.support by auto

lemma R26_R8: "pmf (sds R26) a \<le> 1 - pmf (sds R8) a"
  using R8_R26.strategyproofness R8.support by auto

lemma R4_R18: "pmf (sds R18) c \<le> pmf (sds R4) c" "pmf (sds R18) a \<ge> pmf (sds R4) a"
proof -
  (* Useless? *)
  from R4_R18.strategyproofness R18_R4.strategyproofness R18.support R4.support 
    show "pmf (sds R18) c \<le> pmf (sds R4) c" "pmf (sds R18) a \<ge> pmf (sds R4) a"
    by auto
qed



lemma R7 [simp]: "pmf (sds R7) a = 1/2" "pmf (sds R7) b = 0" "pmf (sds R7) c = 0" "pmf (sds R7) d = 1/2"
proof -
  from R5_d_ge_one_half have "1/2 \<le> pmf (sds R5) d" by simp
  also from R5_R17 have "\<dots> \<le> pmf (sds R17) d" by simp
  also from R17_R7.strategyproofness(2) lottery_conditions[OF R7_wf] lottery_conditions[OF R17_wf]
       R7.support R17.support
    have "pmf (sds R17) d \<le> pmf (sds R7) d" by auto
  finally have "pmf (sds R7) d \<ge> 1/2" .
  with R7_R43.strategyproofness(1) lottery_conditions[OF R7_wf] R7.support
    show "pmf (sds R7) a = 1/2" "pmf (sds R7) b = 0" "pmf (sds R7) c = 0" "pmf (sds R7) d = 1/2"
    by auto
qed

(* This looks like some real progress *)
lemma R5 [simp]: "pmf (sds R5) a = 1/2" "pmf (sds R5) b = 0" "pmf (sds R5) c = 0" "pmf (sds R5) d = 1/2"
proof -
  from R5_R17 have "pmf (sds R5) d \<le> pmf (sds R17) d" .
  also from R17_R7.strategyproofness(2) lottery_conditions[OF R17_wf] lottery_conditions[OF R7_wf]
    have "pmf (sds R17) d \<le> pmf (sds R7) d" using R7.support R17.support by auto
  also have "\<dots> \<le> 1/2" using R7_aux by simp
  finally have "pmf (sds R5) d \<le> 1/2" .
  with R5_d_ge_one_half show d: "pmf (sds R5) d = 1 / 2" by simp
  with R5_aux show "pmf (sds R5) c = 0" by simp
  with d R5.support lottery_conditions[OF R5_wf] 
    show "pmf (sds R5) a = 1/2" by simp
qed (simp_all add: R5.support)



lemma R15 [simp]: "pmf (sds R15) a = 1/2" "pmf (sds R15) d = 1/2" "pmf (sds R15) b = 0" "pmf (sds R15) c = 0"
proof -
  from R15_R5.strategyproofness lottery_conditions[OF R15_wf] 
    have "pmf (sds R15) a \<ge> 1/2" by auto
  moreover from R15_R7.strategyproofness lottery_conditions[OF R15_wf]
    have "pmf (sds R15) b + pmf (sds R15) d \<ge> 1/2"
    by auto
  ultimately show "pmf (sds R15) a = 1/2" using lottery_conditions[OF R15_wf] by auto
  with R15_R5.strategyproofness lottery_conditions[OF R15_wf]
    show "pmf (sds R15) d = 1/2" "pmf (sds R15) b = 0" "pmf (sds R15) c = 0" by auto
qed

lemma R13 [simp]: "pmf (sds R13) a = 1/2" "pmf (sds R13) b = 0" "pmf (sds R13) c = 0" "pmf (sds R13) d = 1/2"
  using R15_aux R13_aux by simp_all

lemma R27 [simp]: "pmf (sds R27) a = 1/2" "pmf (sds R27) b = 0" "pmf (sds R27) c = 0" "pmf (sds R27) d = 1/2"
  by simp_all

lemma R19 [simp]: "pmf (sds R19) a = 1/2" "pmf (sds R19) b = 0" "pmf (sds R19) c = 0" "pmf (sds R19) d = 1/2"
proof -
  show "pmf (sds R19) b = 0" "pmf (sds R19) d = 1/2"
    using R27_R19 lottery_conditions[OF R19_wf] R19_aux by auto
  with R27_R19.strategyproofness(1) lottery_conditions[OF R19_wf]
    show "pmf (sds R19) c = 0" "pmf (sds R19) a = 1/2"
    by simp_all
qed

lemma R1 [simp]: "pmf (sds R1) a = 1/2" "pmf (sds R1) b = 0"
proof -
  from R19_R1.strategyproofness lottery_conditions[OF R1_wf]
    have "pmf (sds R1) a + pmf (sds R1) b \<le> 1/2" by simp
  with R1_R19.strategyproofness lottery_conditions[OF R1_wf]
    show "pmf (sds R1) a = 1/2" "pmf (sds R1) b = 0" by auto
qed

lemma R2_b [simp]: "pmf (sds R2) b = 0"
  using R2_R1 by simp

lemma R2_a_ge_one_half: "pmf (sds R2) a \<ge> 1/2"
  using R2_R1 by simp


lemma R22 [simp]: "pmf (sds R22) a = 1/2" "pmf (sds R22) b = 0" "pmf (sds R22) c = 0" "pmf (sds R22) d = 1/2"
proof -
  from R5_R33 have "1/2 \<le> pmf (sds R33) a" by simp
  also from R33_R22.strategyproofness R22.support R33.support 
    lottery_conditions[OF R22_wf] lottery_conditions[OF R33_wf]
    have "\<dots> \<le> pmf (sds R22) a" by simp
  finally show "pmf (sds R22) a = 1/2" "pmf (sds R22) b = 0" "pmf (sds R22) c = 0" "pmf (sds R22) d = 1/2"
    using R22_d_ge_one_half lottery_conditions[OF R22_wf] by auto
qed

lemma R28 [simp]: "pmf (sds R28) a = 1/2" "pmf (sds R28) b = 0" "pmf (sds R28) c = 0" "pmf (sds R28) d = 1/2"
proof -
  from R32_R22.strategyproofness R22_R32.strategyproofness 
       lottery_conditions[OF R32_wf] lottery_conditions[OF R22_wf] R32.support
    show "pmf (sds R28) a = 1/2" "pmf (sds R28) b = 0" "pmf (sds R28) c = 0" "pmf (sds R28) d = 1/2" by auto
qed

lemma R39 [simp]: "pmf (sds R39) a = 1/2" "pmf (sds R39) b = 0" "pmf (sds R39) c = 0" "pmf (sds R39) d = 1/2"
proof -
  from R28_R39.strategyproofness(1) show "pmf (sds R39) c = 0" by simp
  thus "pmf (sds R39) a = 1/2" "pmf (sds R39) b = 0" "pmf (sds R39) d = 1/2"
    by simp_all
qed

lemma R2 [simp]: "pmf (sds R2) a = 1/2" "pmf (sds R2) b = 0" "pmf (sds R2) c = 0" "pmf (sds R2) d = 1/2"
proof -
  from R39_R2.strategyproofness lottery_conditions[OF R2_wf] R2_a_ge_one_half
    show "pmf (sds R2) a = 1/2" "pmf (sds R2) b = 0" "pmf (sds R2) c = 0" "pmf (sds R2) d = 1/2"
    by auto
qed



lemma R17_d [simp]: "pmf (sds R17) d = 1/2"
proof -
  from R17_R11.strategyproofness(2) R11.support R17.support
       lottery_conditions[OF R11_wf] lottery_conditions[OF R17_wf]
    have "pmf (sds R17) d \<le> pmf (sds R11) d" by simp
  also {
    from R6_R42.strategyproofness 
      have "pmf (sds R42) a + pmf (sds R42) c \<le> pmf (sds R6) a + pmf (sds R6) c" by simp
    also from R6_R19.strategyproofness(2) lottery_conditions[OF R6_wf] 
      have "pmf (sds R6) a + pmf (sds R6) c \<le> 1/2" by auto
    finally have "pmf (sds R11) d \<le> 1/2"
      using R42_R11.strategyproofness lottery_conditions[OF R11_wf] lottery_conditions[OF R42_wf]
      by auto
  }
  finally have "pmf (sds R17) d \<le> 1/2" .
  with R5_R17 R5_d_ge_one_half show "pmf (sds R17) d = 1/2" by simp
  
  find_theorems R17
qed

lemma R3 [simp]: "pmf (sds R3) a = 0" "pmf (sds R3) b = 0" "pmf (sds R3) c = 1/2" "pmf (sds R3) d = 1/2"
  and R42 [simp]: "pmf (sds R42) a = 0" "pmf (sds R42) b = 0" "pmf (sds R42) c = 1/2" "pmf (sds R42) d = 1/2"
proof -
  (* TODO: Simplify? *)
  from R6_R42.strategyproofness 
    have A: "pmf (sds R42) a + pmf (sds R42) c \<le> pmf (sds R6) a + pmf (sds R6) c" by simp
  also from R6_R19.strategyproofness(2) lottery_conditions[OF R6_wf] 
    have B: "pmf (sds R6) a + pmf (sds R6) c \<le> 1/2" by auto
  finally have AB: "pmf (sds R42) a + pmf (sds R42) c \<le> 1 / 2" .
  from R17_R3.strategyproofness(2) R3.support R17.support
       lottery_conditions[OF R17_wf] lottery_conditions[OF R3_wf] 
    have C: "pmf (sds R3) d \<ge> 1/2" by auto
  from R17_R11.strategyproofness(2) R5_R17 R17.support R11.support lottery_conditions[OF R11_wf] lottery_conditions[OF R17_wf]
    have D: "pmf (sds R11) d \<ge> 1/2" by auto
  from R42_R11.strategyproofness R11.support AB D 
    have E: "pmf (sds R11) d \<le> pmf (sds R42) c" by auto
  with D have F: "pmf (sds R42) c \<ge> 1/2" by simp
  
  from R42_R3.strategyproofness C F lottery_conditions[OF R3_wf] lottery_conditions[OF R42_wf] R3.support
    show "pmf (sds R3) a = 0" "pmf (sds R3) b = 0" "pmf (sds R3) c = 1/2" "pmf (sds R3) d = 1/2"
         "pmf (sds R42) a = 0" "pmf (sds R42) b = 0" "pmf (sds R42) c = 1/2" "pmf (sds R42) d = 1/2"
    by auto
qed

lemma R37 [simp]: "pmf (sds R37) a = 1/2" "pmf (sds R37) b = 0" "pmf (sds R37) c = 1/2" "pmf (sds R37) d = 0"
  using R37_R42.strategyproofness lottery_conditions[OF R37_wf] by simp_all

lemma R24[simp]: "pmf (sds R24) a = 0" "pmf (sds R24) b = 0" "pmf (sds R24) d = 1 - pmf (sds R24) c"
proof -
  from R42_R24.strategyproofness lottery_conditions[OF R24_wf] 
    show "pmf (sds R24) a = 0" "pmf (sds R24) b = 0" "pmf (sds R24) d = 1 - pmf (sds R24) c" by auto
qed

lemma R34 [simp]:
  "pmf (sds R34) a = 1 - pmf (sds R24) c" "pmf (sds R34) b = pmf (sds R24) c"
  "pmf (sds R34) c = 0" "pmf (sds R34) d = 0"
proof -
  from R34_R24.strategyproofness R24_R34.strategyproofness
  show "pmf (sds R34) a = 1 - pmf (sds R24) c"
       "pmf (sds R34) b = pmf (sds R24) c"
       "pmf (sds R34) c = 0"
       "pmf (sds R34) d = 0"
      apply auto
      using lottery_conditions[OF R34_wf]
      apply auto
      done
qed

lemma R46 [simp]: "pmf (sds R46) a = 0" "pmf (sds R46) c = 0" "pmf (sds R46) d = 1 - pmf (sds R46) b"
  using R46_R37.strategyproofness(1) lottery_conditions[OF R46_wf] by auto

lemma R20 [simp]: "pmf (sds R20) a = 0" "pmf (sds R20) c = 0" "pmf (sds R20) d = 1 - pmf (sds R20) b" 
  using R46_R20.strategyproofness lottery_conditions[OF R20_wf] by auto

lemma R21 [simp]: "pmf (sds R21) d = 1 - pmf (sds R21) a" "pmf (sds R21) b = 0" "pmf (sds R21) c = 0"
proof -
  from R20_R21.strategyproofness lottery_conditions[OF R21_wf]
    show "pmf (sds R21) d = 1 - pmf (sds R21) a" "pmf (sds R21) b = 0" "pmf (sds R21) c = 0" by auto
qed

lemma R14 [simp]: "pmf (sds R14) b = 0" "pmf (sds R14) d = 0" "pmf (sds R14) c = 1 - pmf (sds R14) a"
proof -
  from R14_R34 lottery_conditions[OF R14_wf] 
    show "pmf (sds R14) b = 0" "pmf (sds R14) d = 0" "pmf (sds R14) c = 1 - pmf (sds R14) a" by auto
qed



(*
lemma P
proof -
  from R12_a_ge_one_half have "1/2 \<le> pmf (sds R12) a" by simp
  also from R23_R12 have "pmf (sds R12) a \<le> pmf (sds R23) c + pmf (sds R23) a" by simp
  also from R23_R18.strategyproofness R18.support R23.support 
       lottery_conditions[OF R18_wf] lottery_conditions[OF R23_wf]
    have "pmf (sds R23) a \<le> pmf (sds R18) a" by simp
  finally have P
   using R4_R18.strategyproofness 
apply auto
find_theorems R9

  finally have P
apply auto
find_theorems R12
  thm R23_R19 R23_R12

  from R4_R18.strategyproofness R18.support R4.support have P
apply auto

qed


lemma R35_a_ge_one_half: "1 / 2 \<le> pmf (sds R35) a"
proof -
  from R12_a_ge_one_half have "1/2 \<le> pmf (sds R12) a" by simp
  also from R44_R40.strategyproofness R40.support lottery_conditions[OF R40_wf] 
    have "pmf (sds R12) a \<le> pmf (sds R40) a" by auto
  also from R9_R40.strategyproofness R40.support R9.support 
    have "pmf (sds R40) a \<le> pmf (sds R35) a" by simp
  finally show "1 / 2 \<le> pmf (sds R35) a" by simp
qed*)
  

(*
lemma P
proof -
  from R2_R38.strategyproofness 
    have "pmf (sds R38) c + pmf (sds R38) a \<le> 1/2" by auto
  from R31_R38.strategyproofness have P
apply auto*)


lemma pmf_sum_eq_1_iff: "pmf p x + pmf p y = 1 \<longleftrightarrow> pmf p y = 1 - pmf p x"
  by linarith

lemma less_or_eq: 
  "x < y \<or> x = y \<longleftrightarrow> x \<le> (y::real)"
  "x < y \<or> y = x \<longleftrightarrow> x \<le> (y::real)" by linarith+



lemma R16 [simp]: "pmf (sds R16) b = 0" "pmf (sds R16) c = 0" "pmf (sds R16) d = 1 - pmf (sds R16) a"
proof -
  from R14_R16.strategyproofness R16.support lottery_conditions[OF R16_wf] 
    have B: "pmf (sds R16) a \<ge> pmf (sds R14) a" by auto

  from R16_R12 have "pmf (sds R16) c + pmf (sds R16) a \<le> pmf (sds R12) a" by simp
  also from R44_R40.strategyproofness lottery_conditions[OF R40_wf] R40.support
    have "pmf (sds R12) a \<le> pmf (sds R40) a" by auto
  also from R9_R40.strategyproofness R9.support R40.support 
    have "pmf (sds R40) a \<le> pmf (sds R9) a" by auto
  finally have A: "pmf (sds R16) c + pmf (sds R16) a \<le> pmf (sds R9) a" by simp
  
  from A B have C: "pmf (sds R16) c \<le> pmf (sds R9) a - pmf (sds R14) a" by simp
  also from R14_R9.strategyproofness(2) R9.support R14 lottery_conditions[OF R9_wf]
    have "pmf (sds R9) a - pmf (sds R14) a \<le> 0" by auto
  finally show "pmf (sds R16) b = 0" "pmf (sds R16) c = 0" "pmf (sds R16) d = 1 - pmf (sds R16) a"
    using lottery_conditions[OF R16_wf] R16.support by auto
qed

lemma R12_R14: "pmf (sds R14) a \<le> pmf (sds R12) a"
  using R14_R16.strategyproofness R16_R12 by auto


lemma R12_a [simp]: "pmf (sds R12) a = pmf (sds R9) a"
proof -
  from R44_R40.strategyproofness R40.support lottery_conditions[OF R40_wf] 
    have A: "pmf (sds R12) a \<le> pmf (sds R40) a" by auto
  also from R9_R40.strategyproofness R9.support R40.support 
    have "pmf (sds R40) a \<le> pmf (sds R9) a" by auto
  finally have B: "pmf (sds R12) a \<le> pmf (sds R9) a" by simp
  moreover from R9_R14 R12_R14 have "pmf (sds R9) a \<le> pmf (sds R12) a" by simp
  ultimately show "pmf (sds R12) a = pmf (sds R9) a" by simp
qed

lemma R23 [simp]: "pmf (sds R23) b = 0" "pmf (sds R23) c = 0" "pmf (sds R23) d = 1 - pmf (sds R23) a"
  using R23_R19 lottery_conditions[OF R23_wf] R23.support by simp_all

lemma R35 [simp]: "pmf (sds R35) a = pmf (sds R21) a" "pmf (sds R35) b = 0" "pmf (sds R35) c = 0" "pmf (sds R35) d = 1 - pmf (sds R21) a"
  using R35_R21 lottery_conditions[OF R35_wf] R35.support by auto

lemma R21_R23: "pmf (sds R21) a \<le> pmf (sds R23) a"
  using R23_R12 by auto

lemma R4_R47: "pmf (sds R4) c \<le> pmf (sds R47) c"
  using R4_R47.strategyproofness(2) R4.support R47.support
         lottery_conditions[OF R4_wf] lottery_conditions[OF R47_wf] 
  by auto

lemma R47_R30: "pmf (sds R30) a \<le> pmf (sds R47) a"
  using R47_R30.strategyproofness R30.support R47.support 
         lottery_conditions[OF R4_wf] lottery_conditions[OF R47_wf] by auto

lemma bar: "pmf (sds R4) c + pmf (sds R30) a \<le> 1 - pmf (sds R47) d"
proof -
  (* We don't need the previous two lemmas, just this one *)
  from R4_R47 R47_R30 lottery_conditions[OF R47_wf] R47.support
    show "pmf (sds R4) c + pmf (sds R30) a \<le> 1 - pmf (sds R47) d"
    by auto
qed

lemma R9 [simp]: "pmf (sds R9) b = 0" "pmf (sds R9) d = 0" "pmf (sds R9) a = pmf (sds R14) a" "pmf (sds R9) c = 1 - pmf (sds R14) a"
  using R12_R14 R14_R9.strategyproofness(2) lottery_conditions[OF R9_wf] R9.support
  by auto

lemma R21_a [simp]: "pmf (sds R21) a = pmf (sds R14) a"
  by (subst R9 [symmetric], subst R35 [symmetric], subst R9_a) (rule refl)

lemma R23_a [simp]: "pmf (sds R23) a = pmf (sds R14) a"
  and R18 [simp]: "pmf (sds R18) a = pmf (sds R14) a" "pmf (sds R18) b = 0"
                  "pmf (sds R18) d = 0" "pmf (sds R18) c = 1 - pmf (sds R14) a"
proof -
  from R23_R18.strategyproofness R21_R23 lottery_conditions[OF R18_wf]
    show "pmf (sds R18) d = 0" by auto
  with R23_R18.strategyproofness R21_R23 lottery_conditions[OF R18_wf] R18.support
    show "pmf (sds R23) a = pmf (sds R14) a" "pmf (sds R18) a = pmf (sds R14) a"
         "pmf (sds R18) c = 1 - pmf (sds R14) a" by auto
qed (insert R18.support, simp_all)

lemma R4 [simp]: "pmf (sds R4) a = pmf (sds R14) a" "pmf (sds R4) b = 0"
                 "pmf (sds R4) c = 1 - pmf (sds R4) a" "pmf (sds R4) d = 0"
proof -
  from R30_R21.strategyproofness R30.support lottery_conditions[OF R30_wf] 
    have "pmf (sds R4) c + pmf (sds R21) a \<le> pmf (sds R4) c + pmf (sds R30) a" by auto
  also from bar have "pmf (sds R4) c + pmf (sds R30) a \<le> 1 - pmf (sds R47) d" by simp
  finally have "pmf (sds R4) c + pmf (sds R14) a \<le> 1"
    using lottery_conditions[OF R47_wf]  by simp
  with R4_R18.strategyproofness lottery_conditions[OF R4_wf] R4.support
    show "pmf (sds R4) a = pmf (sds R14) a" "pmf (sds R4) b = 0"
         "pmf (sds R4) c = 1 - pmf (sds R4) a" "pmf (sds R4) d = 0" by auto
qed

lemma R14_R8: "pmf (sds R14) a \<le> pmf (sds R8) a"
  using R4_R8.strategyproofness by auto

lemma narf: "pmf (sds R26) a + pmf (sds R14) a \<le> 1" 
proof -
  from R14_R8 R26_R8
    show "pmf (sds R26) a + pmf (sds R14) a \<le> 1" by simp
qed

notepad
begin
  from R41_R31 R25_a_ge_one_half R4_R47 R47_R30 narf
    R25_R26.strategyproofness(1) lottery_conditions[OF R25_wf] lottery_conditions[OF R26_wf]
    R25.support R26.support
have P
apply (auto simp: algebra_simps)

qed

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
  R2_R38.strategyproofness 
  R25_R26.strategyproofness(1)
  R31_R38.strategyproofness
  R30_R41.strategyproofness R30_R21.strategyproofness
  R45_R31.strategyproofness(2)

lemmas additional_equations = 
  R10_bc R10_ad R26_bc R27_bc R28_bc R29_bc R29_ac R43_bc R43_ad R45
  R39_b R36_a R36_d R39_a R39_d R12_c R12_d R12_b R32_d R13 R27_R13 R44 R9_a
  R18_c R8_d R5 R7 R15 R13 R19 R1 R22 R28 R2 R3 R42 R37 R34 R46 R20 R21 R12_a R23 R35 R4
  R21_a R23_a R18

lemmas supports =
  R3.support R9.support R11.support R16.support R17.support R18.support R30.support R47.support

lemmas additional_inequalities = 
   R41_R31 R25_a_ge_one_half R4_R47 R47_R30 narf

declare [[smt_certificates = "SDS_Impossibility.certs"]]


lemma absurd: False
  using R_wfs [THEN lottery_conditions(1)] R_wfs [THEN lottery_conditions(2)]
        supports strategyproofness additional_inequalities  additional_equations
  using [[smt_oracle]] by smt
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
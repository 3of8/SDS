theory SDS_Impossibility_Preference_Profiles
imports
  SDS_Automation
  SDS_Impossibility_Definitions
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

derive_support_conditions (ex_post_efficient_sds sd_efficient_sds)
  R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20
  R21 R22 R23 R24 R25 R26 R27 R28 R29 R30 R31 R32 R33 R34 R35 R36 R37 R38 R39 R40
  R41 R42 R43 R44 R45 R46 R47
  by (simp_all add: agent_iff alt_iff)

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

lemma False
  using 
    R_wfs [THEN lottery_conditions(1)] R_wfs [THEN lottery_conditions(2)]
    R1.orbits R2.orbits R3.orbits R4.orbits R5.orbits R6.orbits R7.orbits R8.orbits R9.orbits
    R10.orbits R11.orbits R12.orbits R13.orbits R14.orbits R15.orbits R16.orbits R17.orbits R18.orbits
    R19.orbits R20.orbits R21.orbits R22.orbits R23.orbits R24.orbits R25.orbits R26.orbits R27.orbits
    R28.orbits R29.orbits R30.orbits R31.orbits R32.orbits R33.orbits R34.orbits R35.orbits R36.orbits
    R37.orbits R38.orbits R39.orbits R40.orbits R41.orbits R42.orbits R43.orbits R44.orbits R45.orbits
    R46.orbits R47.orbits
    R1.support R2.support R3.support R4.support R5.support R6.support R7.support R8.support R9.support
    R10.support R11.support R12.support R13.support R14.support R15.support R16.support R17.support R18.support
    R19.support R20.support R21.support R22.support R23.support R24.support R25.support R26.support R27.support
    R28.support R29.support R30.support R31.support R32.support R33.support R34.support R35.support R36.support
    R37.support R38.support R39.support R40.support R41.support R42.support R43.support R44.support R45.support
    R46.support R47.support
    R10_R19.strategyproofness(2)
    R36_R39.strategyproofness
    R36_R10.strategyproofness(2)
    R19_R1.strategyproofness
    R19_R27.strategyproofness(2)
    R15_R13.strategyproofness
    R15_R7.strategyproofness
    R15_R5.strategyproofness
    R17_R3.strategyproofness(2)
    R2_R38.strategyproofness
    R2_R1.strategyproofness
    R13_R15.strategyproofness
    R5_R17.strategyproofness
    R1_R2.strategyproofness
    R1_R19.strategyproofness
    R39_R2.strategyproofness
    R44_R40.strategyproofness
    R44_R12.strategyproofness
    R7_R43.strategyproofness(1)
    R27_R19.strategyproofness(1)
    R23_R18.strategyproofness
    R23_R12.strategyproofness(2)
    R42_R24.strategyproofness
    R42_R3.strategyproofness
    R47_R30.strategyproofness
    R6_R42.strategyproofness
    R6_R19.strategyproofness(2)
    R12_R16.strategyproofness(2)
    R9_R40.strategyproofness
    R9_R18.strategyproofness(2)
    R33_R22.strategyproofness
    R33_R5.strategyproofness
    R25_R26.strategyproofness(1)
    R17_R7.strategyproofness(2)
    R17_R11.strategyproofness(2)
    R20_R21.strategyproofness
    R34_R24.strategyproofness
    R5_R10.strategyproofness(2)
    R31_R38.strategyproofness
    R30_R41.strategyproofness
    R30_R21.strategyproofness
    R21_R35.strategyproofness
    R41_R31.strategyproofness
    R32_R28.strategyproofness(1)
    R32_R22.strategyproofness
    R35_R9.strategyproofness
    R22_R29.strategyproofness(2)
    R23_R19.strategyproofness(2)
    R42_R11.strategyproofness
    R12_R10.strategyproofness(1)
    R24_R34.strategyproofness
    R25_R36.strategyproofness
    R37_R42.strategyproofness(1)
    R13_R27.strategyproofness(2)
    R27_R13.strategyproofness(2)
    R14_R16.strategyproofness
    R14_R34.strategyproofness
    R14_R9.strategyproofness(2)
    R45_R31.strategyproofness(2)
    R39_R29.strategyproofness(2)
    R46_R37.strategyproofness(1)
    R46_R20.strategyproofness
    R8_R26.strategyproofness(1)
    R28_R39.strategyproofness(1)
    R4_R47.strategyproofness(2)
    R4_R18.strategyproofness
    R4_R8.strategyproofness
  using [[smt_oracle]] by smt
(*
apply -
apply (atomize (full))
apply (tactic \<open>foo_tac @{context} 1\<close>)+
apply (tactic \<open>Object_Logic.rulify_tac @{context} 1\<close>)
apply hypsubst
apply (simp only: HOL.simp_thms add_0_left add_0_right order.refl True_implies_equals triv_forall_equality)
apply hypsubst
apply (simp only: HOL.simp_thms add_0_left add_0_right order.refl True_implies_equals triv_forall_equality)
apply smt
done*)


end
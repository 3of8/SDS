theory SDS_Impossibility
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


lemma R45 [simp]: "pmf (sds R45) a = 1/4" "pmf (sds R45) b = 1/4" 
           "pmf (sds R45) c = 1/4" "pmf (sds R45) d = 1/4"
  using R45.orbits lottery_conditions[OF R45_wf] by simp_all

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


lemma R39_b [simp]: "pmf (sds R39) b = 0"
  using R39_R29.strategyproofness(1) R29_R39.strategyproofness(1) R39.support
        lottery_conditions[OF R39_wf] by auto

lemma R36_a [simp]: "pmf (sds R36) a = 1/2" and R36_b [simp]: "pmf (sds R36) b = 0"
proof -
  from R10_R36.strategyproofness(1) lottery_conditions[OF R36_wf] 
    have "pmf (sds R36) a + pmf (sds R36) b \<le> 1/2" by auto
  with R36_R10.strategyproofness(1) lottery_conditions[OF R36_wf]
    show "pmf (sds R36) a = 1/2" "pmf (sds R36) b = 0" by auto
qed

lemma R36_d [simp]: "pmf (sds R36) d = 1/2 - pmf (sds R36) c"
  using lottery_conditions[OF R36_wf] by simp

lemma R39_a [simp]: "pmf (sds R39) a = 1/2"
proof -
  from R36_R39.strategyproofness lottery_conditions[OF R39_wf]
    have "pmf (sds R39) a \<ge> 1/2" by auto
  with R39_R36.strategyproofness lottery_conditions[OF R39_wf]
    show ?thesis by auto
qed

lemma R39_d [simp]: "pmf (sds R39) d = 1/2 - pmf (sds R39) c"
  using lottery_conditions[OF R39_wf] by simp



lemmas R12_b [simp] = R12.support

lemma R12_c [simp]: "pmf (sds R12) c = 0"
  using R12_R10.strategyproofness lottery_conditions[OF R12_wf] by auto

lemma R12_d [simp]: "pmf (sds R12) d = 1 - pmf (sds R12) a"
  using lottery_conditions[OF R12_wf] by simp

lemma R12_a_ge_one_half: "pmf (sds R12) a \<ge> 1/2"
  using R10_R12.strategyproofness(1) lottery_conditions[OF R12_wf]
  by auto


lemma R44 [simp]: 
  "pmf (sds R44) a = pmf (sds R12) a" "pmf (sds R44) d = 1 - pmf (sds R12) a"
  "pmf (sds R44) b = 0" "pmf (sds R44) c = 0"
proof -
  from R12_R44.strategyproofness R44.support have "pmf (sds R44) a \<le> pmf (sds R12) a" by simp
  with R44_R12.strategyproofness R44.support lottery_conditions[OF R44_wf]
    show "pmf (sds R44) a = pmf (sds R12) a" "pmf (sds R44) c = 0"
         "pmf (sds R44) d = 1 - pmf (sds R12) a" by auto
qed (insert R44.support, simp_all)

lemma R9_a [simp]: "pmf (sds R9) a = pmf (sds R35) a"
proof -
  from R9_R35.strategyproofness R35.support R9.support 
    have "pmf (sds R35) a \<le> pmf (sds R9) a" by simp
  with R35_R9.strategyproofness R9.support R35.support show ?thesis by simp
qed

lemma R18_c [simp]: "pmf (sds R18) c = pmf (sds R9) c"
proof -
  from R18_R9.strategyproofness(2) R18.support R9.support
    have "pmf (sds R18) d + pmf (sds R18) a \<ge> pmf (sds R9) d + pmf (sds R9) a" by auto
  with R9_R18.strategyproofness(2) R18.support R9.support
        lottery_conditions[OF R9_wf] lottery_conditions[OF R18_wf]
    show ?thesis by auto
qed

lemma R5_d_ge_one_half: "pmf (sds R5) d \<ge> 1/2"
  using R5_R10.strategyproofness(2) R5.support lottery_conditions[OF R5_wf] by auto

lemma R7 [simp]: "pmf (sds R7) a = 1/2" "pmf (sds R7) b = 0" "pmf (sds R7) c = 0" "pmf (sds R7) d = 1/2"
proof -
  from R5_d_ge_one_half have "1/2 \<le> pmf (sds R5) d" by simp
  also from R5_R17.strategyproofness(2) R17.support lottery_conditions[OF R5_wf] lottery_conditions[OF R17_wf] 
    have "\<dots> \<le> pmf (sds R17) d" by auto
  also from R17_R7.strategyproofness(2) lottery_conditions[OF R7_wf] lottery_conditions[OF R17_wf] R7.support
    have "pmf (sds R17) d \<le> pmf (sds R7) d" by auto
  finally have "pmf (sds R7) d \<ge> 1/2" .
  with R7_R43.strategyproofness(1) lottery_conditions[OF R7_wf] R7.support
    show "pmf (sds R7) a = 1/2" "pmf (sds R7) b = 0" "pmf (sds R7) c = 0" "pmf (sds R7) d = 1/2"
    by auto
qed

lemma R5 [simp]: "pmf (sds R5) a = 1/2" "pmf (sds R5) b = 0" "pmf (sds R5) c = 0" "pmf (sds R5) d = 1/2"
proof -
  from R5_R7.strategyproofness(2) lottery_conditions[OF R5_wf] R5.support 
    have "pmf (sds R5) d \<le> 1/2" by auto
  (*
  from R5_R17 have "pmf (sds R5) d \<le> pmf (sds R17) d" .
  also from R17_R7.strategyproofness(2) lottery_conditions[OF R17_wf] lottery_conditions[OF R7_wf]
    have "pmf (sds R17) d \<le> pmf (sds R7) d" using R7.support R17.support by auto
  also have "\<dots> \<le> 1/2" using R7_R43.strategyproofness(1) by simp
  finally have "pmf (sds R5) d \<le> 1/2" . *)
  with R5_d_ge_one_half show d: "pmf (sds R5) d = 1 / 2" by simp
  with R5_R10.strategyproofness(1) lottery_conditions[OF R5_wf] R5.support
    show "pmf (sds R5) c = 0" "pmf (sds R5) a = 1/2" by simp_all
qed (simp_all add: R5.support)

lemma R15 [simp]: "pmf (sds R15) a = 1/2" "pmf (sds R15) b = 0" "pmf (sds R15) c = 0" "pmf (sds R15) d = 1/2"
proof -
  {
    assume "pmf (sds R15) b = 0"
    with R10_R15.strategyproofness(1) lottery_conditions[OF R15_wf] R15.support
      have "pmf (sds R15) a + pmf (sds R15) c \<le> 1/2" by auto
    with R15_R10.strategyproofness(1) lottery_conditions[OF R15_wf] 
      have "pmf (sds R15) c = 0" by auto
  }
  with R15.support show [simp]: "pmf (sds R15) c = 0" by blast
  with R15_R5.strategyproofness lottery_conditions[OF R15_wf] 
    have "pmf (sds R15) a \<ge> 1/2" by auto
  moreover from R15_R7.strategyproofness lottery_conditions[OF R15_wf]
    have "pmf (sds R15) b + pmf (sds R15) d \<ge> 1/2" by auto
  ultimately show "pmf (sds R15) a = 1/2" using lottery_conditions[OF R15_wf] by auto
  with R15_R5.strategyproofness lottery_conditions[OF R15_wf]
    show "pmf (sds R15) d = 1/2" "pmf (sds R15) b = 0" by auto
qed

lemma R13_aux: "pmf (sds R13) b = 0" "pmf (sds R13) c = 0" "pmf (sds R13) d = 1 - pmf (sds R13) a"
  and R27_R13 [simp]: "pmf (sds R27) a = pmf (sds R13) a" 
  using R27_R13.strategyproofness(1) R13_R27.strategyproofness(1) lottery_conditions[OF R13_wf] by auto

lemma R13 [simp]: "pmf (sds R13) a = 1/2" "pmf (sds R13) b = 0" "pmf (sds R13) c = 0" "pmf (sds R13) d = 1/2"
  using R15_R13.strategyproofness R13_R15.strategyproofness R13_aux by simp_all

lemma R27 [simp]: "pmf (sds R27) a = 1/2" "pmf (sds R27) b = 0" "pmf (sds R27) c = 0" "pmf (sds R27) d = 1/2"
  by simp_all

lemma R19 [simp]: "pmf (sds R19) a = 1/2" "pmf (sds R19) b = 0" "pmf (sds R19) c = 0" "pmf (sds R19) d = 1/2"
proof -
  have "pmf (sds R19) a = 1/2 \<and> pmf (sds R19) b = 0 \<and> pmf (sds R19) c = 0 \<and> pmf (sds R19) d = 1/2"
  proof (rule disjE[OF R19.support]; safe)
    assume [simp]: "pmf (sds R19) b = 0"
    from R10_R19.strategyproofness(1) lottery_conditions[OF R19_wf] 
      have "pmf (sds R19) a + pmf (sds R19) c \<le> 1/2" by auto
    moreover from R19_R10.strategyproofness(1) 
      have "pmf (sds R19) a + pmf (sds R19) c \<ge> 1/2" by simp
    ultimately show "pmf (sds R19) d = 1/2" using lottery_conditions[OF R19_wf] by simp
    with R27_R19.strategyproofness(1) lottery_conditions[OF R19_wf] 
      show "pmf (sds R19) a = 1/2" "pmf (sds R19) c = 0" by auto
  next
    assume [simp]: "pmf (sds R19) c = 0"
    from R19_R10.strategyproofness(1) have "pmf (sds R19) a \<ge> 1/2" by auto
    moreover from R19_R27.strategyproofness(1) have "pmf (sds R19) d \<ge> 1/2" by auto
    ultimately show "pmf (sds R19) a = 1/2" "pmf (sds R19) d = 1/2" "pmf (sds R19) b = 0"
      using lottery_conditions[OF R19_wf] by auto
  qed
  thus "pmf (sds R19) a = 1/2" "pmf (sds R19) b = 0" "pmf (sds R19) c = 0" "pmf (sds R19) d = 1/2" 
    by blast+
qed

lemma R1 [simp]: "pmf (sds R1) a = 1/2" "pmf (sds R1) b = 0"
proof -
  from R19_R1.strategyproofness lottery_conditions[OF R1_wf]
    have "pmf (sds R1) a + pmf (sds R1) b \<le> 1/2" by simp
  with R1_R19.strategyproofness lottery_conditions[OF R1_wf]
    show "pmf (sds R1) a = 1/2" "pmf (sds R1) b = 0" by auto
qed

lemma R22 [simp]: "pmf (sds R22) a = 1/2" "pmf (sds R22) b = 0" "pmf (sds R22) c = 0" "pmf (sds R22) d = 1/2"
proof -
  from R33_R5.strategyproofness R33.support
    have "1/2 \<le> pmf (sds R33) a" by auto
  also from R33_R22.strategyproofness R22.support R33.support 
    lottery_conditions[OF R22_wf] lottery_conditions[OF R33_wf]
    have "\<dots> \<le> pmf (sds R22) a" by simp
  finally show "pmf (sds R22) a = 1/2" "pmf (sds R22) b = 0" "pmf (sds R22) c = 0" "pmf (sds R22) d = 1/2"
    using R22_R29.strategyproofness(1) lottery_conditions[OF R22_wf] by auto
qed

lemma R28 [simp]: "pmf (sds R28) a = 1/2" "pmf (sds R28) b = 0" "pmf (sds R28) c = 0" "pmf (sds R28) d = 1/2"
proof -
  have "pmf (sds R28) a \<le> pmf (sds R32) d"
    using R32_R28.strategyproofness lottery_conditions[OF R32_wf] by auto
  hence R32_d: "pmf (sds R32) d = pmf (sds R28) a"
    using R28_R32.strategyproofness lottery_conditions[OF R32_wf] by auto

  from R22_R32.strategyproofness lottery_conditions[OF R32_wf] R32.support 
    have "pmf (sds R32) a \<le> 1/2" by auto
  with R32_R22.strategyproofness lottery_conditions[OF R32_wf] R32.support 
    show "pmf (sds R28) a = 1/2" "pmf (sds R28) b = 0" "pmf (sds R28) c = 0" "pmf (sds R28) d = 1/2"
    by (auto simp: R32_d)
qed

lemma R39 [simp]: "pmf (sds R39) a = 1/2" "pmf (sds R39) b = 0" "pmf (sds R39) c = 0" "pmf (sds R39) d = 1/2"
proof -
  from R28_R39.strategyproofness(1) show "pmf (sds R39) c = 0" by simp
  thus "pmf (sds R39) a = 1/2" "pmf (sds R39) b = 0" "pmf (sds R39) d = 1/2"
    by simp_all
qed

lemma R2 [simp]: "pmf (sds R2) a = 1/2" "pmf (sds R2) b = 0" "pmf (sds R2) c = 0" "pmf (sds R2) d = 1/2"
proof -
  from R1_R2.strategyproofness R2_R1.strategyproofness lottery_conditions[OF R2_wf] lottery_conditions[OF R1_wf]
    have "pmf (sds R2) a = 1/2" "pmf (sds R2) c + pmf (sds R2) d = 1/2" by (auto simp: algebra_simps)
  with R39_R2.strategyproofness lottery_conditions[OF R2_wf]
    show "pmf (sds R2) a = 1/2" "pmf (sds R2) b = 0" "pmf (sds R2) c = 0" "pmf (sds R2) d = 1/2"
    by auto
qed

lemma R42 [simp]: "pmf (sds R42) a = 0" "pmf (sds R42) b = 0" "pmf (sds R42) c = 1/2" "pmf (sds R42) d = 1/2"
proof -
  from R17_R5.strategyproofness(2) lottery_conditions[OF R17_wf] R17.support 
    have "pmf (sds R17) d \<le> 1/2" by auto
  moreover from R5_R17.strategyproofness(2) R17.support lottery_conditions[OF R17_wf] 
    have "pmf (sds R17) d \<ge> 1/2" by auto
  ultimately have R17_d: "pmf (sds R17) d = 1/2" by simp

  from R6_R42.strategyproofness 
    have "pmf (sds R42) a + pmf (sds R42) c \<le> pmf (sds R6) a + pmf (sds R6) c" by simp
  also from R6_R19.strategyproofness(2) lottery_conditions[OF R6_wf] 
    have "pmf (sds R6) a + pmf (sds R6) c \<le> 1/2" by auto
  finally have "pmf (sds R42) a + pmf (sds R42) c \<le> 1 / 2" .
  moreover from R17_R11.strategyproofness(2) R11.support R17.support
       lottery_conditions[OF R11_wf] lottery_conditions[OF R17_wf]
    have "pmf (sds R11) d \<ge> 1/2" by (auto simp: R17_d)
  ultimately have "pmf (sds R42) a + pmf (sds R42) c \<le> pmf (sds R11) d" by simp
  with R42_R11.strategyproofness R11.support
    have E: "pmf (sds R11) d \<le> pmf (sds R42) c" by auto
  with \<open>pmf (sds R11) d \<ge> 1/2\<close> have "pmf (sds R42) c \<ge> 1/2" by simp
  moreover from R17_R3.strategyproofness(2) R3.support R17.support
       lottery_conditions[OF R17_wf] lottery_conditions[OF R3_wf] 
    have "pmf (sds R3) d \<ge> 1/2" by (auto simp: R17_d)
  ultimately show "pmf (sds R42) a = 0" "pmf (sds R42) b = 0" "pmf (sds R42) c = 1/2" "pmf (sds R42) d = 1/2"
    using R42_R3.strategyproofness lottery_conditions[OF R3_wf] lottery_conditions[OF R42_wf]
    by auto
qed

lemma R37 [simp]: "pmf (sds R37) a = 1/2" "pmf (sds R37) b = 0" "pmf (sds R37) c = 1/2" "pmf (sds R37) d = 0"
  using R37_R42.strategyproofness lottery_conditions[OF R37_wf] by auto

lemma R24 [simp]: "pmf (sds R24) a = 0" "pmf (sds R24) b = 0" "pmf (sds R24) d = 1 - pmf (sds R24) c"
  using R42_R24.strategyproofness lottery_conditions[OF R24_wf] by auto

lemma R34 [simp]:
  "pmf (sds R34) a = 1 - pmf (sds R24) c" "pmf (sds R34) b = pmf (sds R24) c"
  "pmf (sds R34) c = 0" "pmf (sds R34) d = 0"
proof -
  from R24_R34.strategyproofness lottery_conditions[OF R34_wf] 
    have "pmf (sds R34) b \<le> pmf (sds R24) c" by auto
  moreover from R34_R24.strategyproofness lottery_conditions[OF R34_wf] 
    have "pmf (sds R34) b \<ge> pmf (sds R24) c" by auto
  ultimately show bc: "pmf (sds R34) b = pmf (sds R24) c" by simp
  from R34_R24.strategyproofness bc lottery_conditions[OF R34_wf] 
    show "pmf (sds R34) c = 0" by auto
  moreover from R24_R34.strategyproofness bc show "pmf (sds R34) d = 0" by simp
  ultimately show "pmf (sds R34) a = 1 - pmf (sds R24) c"
    using bc lottery_conditions[OF R34_wf] by auto
qed

lemma R14 [simp]: "pmf (sds R14) b = 0" "pmf (sds R14) d = 0" "pmf (sds R14) c = 1 - pmf (sds R14) a"
  using R14_R34.strategyproofness R14.support lottery_conditions[OF R14_wf] by auto

lemma R46 [simp]: "pmf (sds R46) a = 0" "pmf (sds R46) c = 0" "pmf (sds R46) d = 1 - pmf (sds R46) b"
  using R46_R37.strategyproofness(1) lottery_conditions[OF R46_wf] by auto

lemma R20 [simp]: "pmf (sds R20) a = 0" "pmf (sds R20) c = 0" "pmf (sds R20) d = 1 - pmf (sds R20) b" 
  using R46_R20.strategyproofness lottery_conditions[OF R20_wf] by auto

lemma R21 [simp]: "pmf (sds R21) d = 1 - pmf (sds R21) a" "pmf (sds R21) b = 0" "pmf (sds R21) c = 0"
  using R20_R21.strategyproofness lottery_conditions[OF R21_wf] by auto


lemma R16_R12: "pmf (sds R16) c + pmf (sds R16) a \<le> pmf (sds R12) a"
  using R12_R16.strategyproofness(2) R16.support lottery_conditions[OF R16_wf] by auto

lemma R16 [simp]: "pmf (sds R16) b = 0" "pmf (sds R16) c = 0" "pmf (sds R16) d = 1 - pmf (sds R16) a"
proof -
  from R16_R12 have "pmf (sds R16) c + pmf (sds R16) a \<le> pmf (sds R12) a" by simp
  also from R44_R40.strategyproofness lottery_conditions[OF R40_wf] R40.support
    have "pmf (sds R12) a \<le> pmf (sds R40) a" by auto
  also from R9_R40.strategyproofness R9.support R40.support 
    have "pmf (sds R40) a \<le> pmf (sds R9) a" by auto
  finally have "pmf (sds R16) c + pmf (sds R16) a \<le> pmf (sds R9) a" by simp
  moreover from R14_R16.strategyproofness R16.support lottery_conditions[OF R16_wf] 
    have "pmf (sds R16) a \<ge> pmf (sds R14) a" by auto
  ultimately have "pmf (sds R16) c \<le> pmf (sds R9) a - pmf (sds R14) a" by simp
  also from R14_R9.strategyproofness(2) R9.support lottery_conditions[OF R9_wf]
    have "pmf (sds R9) a - pmf (sds R14) a \<le> 0" by auto
  finally show "pmf (sds R16) b = 0" "pmf (sds R16) c = 0" "pmf (sds R16) d = 1 - pmf (sds R16) a"
    using lottery_conditions[OF R16_wf] R16.support by auto
qed

lemma R12_R14: "pmf (sds R14) a \<le> pmf (sds R12) a"
  using R14_R16.strategyproofness R16_R12 by auto

lemma R12_a [simp]: "pmf (sds R12) a = pmf (sds R9) a"
proof -
  from R44_R40.strategyproofness R40.support lottery_conditions[OF R40_wf] 
    have "pmf (sds R12) a \<le> pmf (sds R40) a" by auto
  also from R9_R40.strategyproofness R9.support R40.support 
    have "pmf (sds R40) a \<le> pmf (sds R9) a" by auto
  finally have B: "pmf (sds R12) a \<le> pmf (sds R9) a" by simp
  moreover from R14_R9.strategyproofness(2) lottery_conditions[OF R9_wf] R9.support 
    have "pmf (sds R9) a \<le> pmf (sds R14) a" by auto
  with R12_R14 have "pmf (sds R9) a \<le> pmf (sds R12) a" by simp
  ultimately show "pmf (sds R12) a = pmf (sds R9) a" by simp
qed

lemma R9 [simp]: "pmf (sds R9) b = 0" "pmf (sds R9) d = 0" "pmf (sds R14) a = pmf (sds R35) a" "pmf (sds R9) c = 1 - pmf (sds R14) a"
  using R12_R14 R14_R9.strategyproofness(2) lottery_conditions[OF R9_wf] R9.support
  by auto

lemma R23 [simp]: "pmf (sds R23) b = 0" "pmf (sds R23) c = 0" "pmf (sds R23) d = 1 - pmf (sds R23) a"
  using R23_R19.strategyproofness lottery_conditions[OF R23_wf] R23.support by auto

lemma R35 [simp]: "pmf (sds R35) a = pmf (sds R21) a" "pmf (sds R35) b = 0" "pmf (sds R35) c = 0" "pmf (sds R35) d = 1 - pmf (sds R21) a"
proof -
  from R35_R21.strategyproofness R35.support
    have "pmf (sds R21) a \<le> pmf (sds R35) a + pmf (sds R35) c" by auto
  with R21_R35.strategyproofness R35.support lottery_conditions[OF R35_wf]
    show "pmf (sds R35) a = pmf (sds R21) a" "pmf (sds R35) b = 0" 
         "pmf (sds R35) c = 0" "pmf (sds R35) d = 1 - pmf (sds R21) a" by simp_all
qed

lemma R23_a [simp]: "pmf (sds R23) a = pmf (sds R14) a"
  and R18 [simp]: "pmf (sds R18) a = pmf (sds R14) a" "pmf (sds R18) b = 0"
                  "pmf (sds R18) d = 0" "pmf (sds R18) c = 1 - pmf (sds R14) a"
proof -
  from R23_R18.strategyproofness 
    have "pmf (sds R18) d \<le> pmf (sds R21) a - pmf (sds R23) a"
apply (simp del: R18_c)
apply (subst (asm) R18_c)
apply (subst (asm) R9)
    
  also from R23_R12.strategyproofness(2)
    have R21_R23: "pmf (sds R21) a - pmf (sds R23) a \<le> 0" by auto
  finally show "pmf (sds R18) d = 0" by auto
  with R23_R18.strategyproofness R21_R23 lottery_conditions[OF R18_wf] R18.support
    show "pmf (sds R23) a = pmf (sds R14) a" "pmf (sds R18) a = pmf (sds R14) a"
         "pmf (sds R18) c = 1 - pmf (sds R14) a" by auto
qed (insert R18.support, simp_all)


lemma R4 [simp]: "pmf (sds R4) a = pmf (sds R14) a" "pmf (sds R4) b = 0"
                 "pmf (sds R4) c = 1 - pmf (sds R4) a" "pmf (sds R4) d = 0"
proof -
  from R30_R21.strategyproofness R30.support lottery_conditions[OF R30_wf] 
    have "pmf (sds R4) c + pmf (sds R21) a \<le> pmf (sds R4) c + pmf (sds R30) a" by auto
  also {
    have "pmf (sds R30) a \<le> pmf (sds R47) a"
      using R47_R30.strategyproofness R30.support R47.support 
             lottery_conditions[OF R4_wf] lottery_conditions[OF R47_wf] by auto
      moreover from R4_R47.strategyproofness(2) R4.support R47.support
             lottery_conditions[OF R4_wf] lottery_conditions[OF R47_wf]
        have "pmf (sds R4) c \<le> pmf (sds R47) c" by simp
 
      ultimately have "pmf (sds R4) c + pmf (sds R30) a \<le> 1 - pmf (sds R47) d" 
        using lottery_conditions[OF R47_wf] R47.support by simp
  }
  finally have "pmf (sds R4) c + pmf (sds R14) a \<le> 1"
    using lottery_conditions[OF R47_wf]  by simp
  with R4_R18.strategyproofness lottery_conditions[OF R4_wf] R4.support
    show "pmf (sds R4) a = pmf (sds R14) a" "pmf (sds R4) b = 0"
         "pmf (sds R4) c = 1 - pmf (sds R4) a" "pmf (sds R4) d = 0" by auto
qed

lemma R8_d [simp]: "pmf (sds R8) d = 1 - pmf (sds R8) a"
  using R8_R26.strategyproofness(2) R26_R8.strategyproofness(2) R8.support
  apply auto
  using lottery_conditions[OF R8_wf]
  apply auto
  done

lemma R8_c [simp]: "pmf (sds R8) c = 0"
  using lottery_conditions[OF R8_wf] R8.support by auto

lemma R14_R8: "pmf (sds R14) a \<le> pmf (sds R8) a"
  using R4_R8.strategyproofness by auto

lemma R4_R47: "pmf (sds R4) c \<le> pmf (sds R47) c"
  using R4_R47.strategyproofness(2) R4.support R47.support
         lottery_conditions[OF R4_wf] lottery_conditions[OF R47_wf] 
  by auto

lemma R30 [simp]: "pmf (sds R30) a = pmf (sds R47) a" "pmf (sds R30) b = 0" 
  "pmf (sds R30) c = 0" "pmf (sds R30) d = 1 - pmf (sds R47) a"
proof -
  have "pmf (sds R30) a \<le> pmf (sds R47) a"
    using R47_R30.strategyproofness R30.support R47.support 
           lottery_conditions[OF R4_wf] lottery_conditions[OF R47_wf] by auto
  with R4_R47 R30_R21.strategyproofness R30.support
    lottery_conditions[OF R30_wf] lottery_conditions[OF R47_wf]
    show "pmf (sds R30) a = pmf (sds R47) a" "pmf (sds R30) b = 0" 
         "pmf (sds R30) c = 0" "pmf (sds R30) d = 1 - pmf (sds R47) a" by auto
qed

lemma R41_ac: "pmf (sds R41) a + pmf (sds R41) c \<le> pmf (sds R47) a"
  using R30_R41.strategyproofness R41.support by auto

lemma R25_a_ge_one_half: "pmf (sds R25) a \<ge> 1/2" and R36_c_le_one_half: "pmf (sds R36) c \<le> 1/2"
proof -
  from R25_R36.strategyproofness R36_R25.strategyproofness R25.support 
       lottery_conditions[OF R25_wf] lottery_conditions[OF R36_wf]
    show "pmf (sds R25) a \<ge> 1/2" "pmf (sds R36) c \<le> 1/2" by auto
qed

lemma R26_a_ge_one_half: "pmf (sds R26) a \<ge> 1/2"
  using R25_R26.strategyproofness(1) R25_a_ge_one_half lottery_conditions[OF R25_wf] 
  by auto

lemma R31_c_ge_one_half: "pmf (sds R31) c \<ge> 1/2"
proof -
  from R26_a_ge_one_half lottery_conditions[OF R47_wf]
    have "1/2 \<le> pmf (sds R26) a + pmf (sds R47) d" by simp
  also from R8_R26.strategyproofness R8.support
    have "pmf (sds R26) a \<le> 1 - pmf (sds R8) a" by auto
  with R4_R47 R14_R8
    have "pmf (sds R26) a + pmf (sds R47) d \<le> pmf (sds R47) c + pmf (sds R47) d" by simp
  also from R41_R31.strategyproofness R41.support lottery_conditions[OF R31_wf] 
            R41_ac lottery_conditions[OF R41_wf] lottery_conditions[OF R47_wf] 
    have "pmf (sds R47) c + pmf (sds R47) d \<le> pmf (sds R31) c" by simp
  finally show "pmf (sds R31) c \<ge> 1/2" by simp
qed

lemma R31: "pmf (sds R31) a = 0" "pmf (sds R31) c = 1/2" "pmf (sds R31) b + pmf (sds R31) d = 1/2"
  using R31_R38.strategyproofness R31_c_ge_one_half 
        lottery_conditions[OF R31_wf] lottery_conditions[OF R38_wf] R2_R38.strategyproofness by auto

lemma absurd: False
  using R31 R45_R31.strategyproofness(2) by auto

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
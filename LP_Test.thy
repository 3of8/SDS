theory LP_Test
imports 
  Complex_Main
  "~~/src/HOL/Matrix_LP/Cplex"
  Preference_Profile_Cmd
begin

preference_profile agents: "{A1,A2,A3,A4}" alts: "{a,b,c,d}" where
  R = A1: [a,b], [c,d] A2: [b,d], a, c A3: [a,c], [b,d] A4: [c,d], a, b
  by (simp_all add: insert_eq_iff)

preference_profile agents: "{A1,A2,A3,A4}" alts: "{a,b,c,d}" where
  R3 = A1: b,a,d,c A2: b,a,c,d A3: a,b,c,d A4: a,b,c,d
  by (simp_all add: insert_eq_iff)

ML_val \<open>
open Preference_Profiles;
let
val r3 = let val {raw = raw, ...} = get_info @{term R3} @{context} in raw end
in
  r3 |> pareto_pairs |> map (apply2 (Thm.cterm_of @{context}))
end
\<close>


ML \<open>

open Preference_Profiles;

local

open Cplex;

in

fun lp_constr_to_cplex_constr n (lhs, slack, rhs) =
  let
    fun times_n x = cplexProd (cplexNum (Int.toString n), x)
    val lhs' =  cplexSum (cplexNeg (cplexVar slack) :: map (times_n o cplexVar) lhs)
    val rhs' = cplexNum (Int.toString rhs)
  in
    cplexConstr (cplexEq, (lhs', rhs'))
  end

(*
fun mk_inefficiency_lp_cplex p lottery =
  let
    val constrs = mk_inefficiency_lp p lottery
    val alts = alts_of_profile p
    val alt_ids = alts ~~ List.tabulate (length alts, Int.toString);
    fun mk_lottery_var x = "q" ^ the (AList.lookup op aconv alt_ids x)
    val lottery_vars = map (cplexVar o mk_lottery_var) alts
    val slack_vars = map (fn (_,x,_) => cplexVar x) constrs
 
    val constrs' = constrs |> map (fn x => (NONE, lp_constr_to_cplex_constr x))
    val eq = (NONE, cplexConstr (cplexEq, (cplexSum lottery_vars, cplexNum "1")))
    val bnds = map (fn x => cplexBound (x, cplexGeq, cplexNum "0")) 
          (lottery_vars @ slack_vars)
    val goal = cplexMaximize (cplexSum slack_vars)
  in
    cplexProg ("foo", goal, eq :: constrs', bnds)
  end
*)

fun mk_inefficiency_lp_cplex p support =
  let
    val constrs = mk_inefficiency_lp p support
    val alts = alts_of_profile p
    val n = length support
    val alt_ids = alts ~~ List.tabulate (length alts, Int.toString);
    fun mk_lottery_var x = "q" ^ the (AList.lookup op aconv alt_ids x)
    val lottery_vars = map (cplexVar o mk_lottery_var) alts
    val slack_vars = map (fn (_,x,_) => cplexVar x) constrs
 
    val constrs' = constrs |> map (fn x => (NONE, lp_constr_to_cplex_constr n x))
    val eq = (NONE, cplexConstr (cplexEq, (cplexSum lottery_vars, cplexNum "1")))
    val bnds = map (fn x => cplexBound (x, cplexGeq, cplexNum "0")) (lottery_vars @ slack_vars)
    val goal = cplexMaximize (cplexSum slack_vars)
  in
    cplexProg ("foo", goal, eq :: constrs', bnds)
  end

fun find_inefficiency_witness p lottery =
  let
    val _ = set_solver SOLVER_GLPK
    val alts = alts_of_profile p
    val lottery_vars = List.tabulate (length alts, fn x => "q" ^ Int.toString x);

    fun process_solution (diff, assignments) = 
      if diff = "0" then 
        NONE 
      else
        SOME (alts ~~ map (the o AList.lookup op= assignments) lottery_vars)
  in 
    case solve (mk_inefficiency_lp_cplex p lottery) of
      Optimal x => process_solution x
    | _ => raise Match
  end

fun power_set xs =
  let
    fun go acc [] = [acc]
      | go acc (x::xs) = go acc xs @ go (x::acc) xs
  in
    go [] xs |> sort (int_ord o apply2 length)
  end


fun find_minimal_inefficient_supports p =
  let
    val alts = alts_of_profile p
    val n = length alts
    fun go supp acc =
      if List.null supp orelse length supp = n orelse
            member (fn (a, b) => subset op aconv (fst b, a)) acc supp then
        acc
      else 
        case find_inefficiency_witness p supp of
          NONE => acc
        | SOME lott => (supp, lott) :: acc
  in
    fold go (power_set alts) []
  end

end

val p = let val {raw = raw, ...} = get_info @{term R} @{context} in raw end

fun find_inefficiency_witness' p support =
  find_inefficiency_witness p support |> Option.map (map (apfst (Thm.cterm_of @{context})))


val prog = mk_inefficiency_lp_cplex p [@{term c}, @{term b}]
val _ = Cplex.save_cplexFile "/tmp/foo.lp" prog
val cterm = Thm.cterm_of @{context}
val find_minimal_inefficient_supports' =
  find_minimal_inefficient_supports #>
  map (fn (a, b) => (map cterm a, map (apfst cterm) b))

\<close>

ML_val \<open>
let
  val _ =  Cplex.set_solver Cplex.SOLVER_GLPK
in
  Cplex.solve prog
end
\<close>

ML_val \<open>
find_minimal_inefficient_supports' p
\<close>


(*
MAXIMIZE
 + r3_1 + r3_0 + r2_0 + r1_1 + r1_0 + r0_0

ST
 + q0 + q1 + q2 + q3 = 1
 - r3_1 + 2 q0 + 2 q2 + 2 q3 = 1
 - r3_0 + 2 q2 + 2 q3 = 1
 - r2_0 + 2 q0 + 2 q2 = 1
 - r1_1 + 2 q0 + 2 q1 + 2 q3 = 1
 - r1_0 + 2 q1 + 2 q3 = 1
 - r0_0 + 2 q0 + 2 q1 = 1

BOUNDS
q0 >= 0
q1 >= 0
q2 >= 0
q3 >= 0
r3_1 >= 0
r3_0 >= 0
r2_0 >= 0
r1_1 >= 0
r1_0 >= 0
r0_0 >= 0

END
*)

(*
ML_val \<open> SMT_Solver.smt_tac \<close>

lemma A:
  fixes p0 p1 p2 :: real
  defines "p3 \<equiv> 1 - (p0 + p1 + p2)"
  assumes "p0 \<ge> 0" "p1 > 0" "p2 > 0" "p3 \<ge> 0"
  shows "\<exists>r1 r2 r3 r4 r5 r6 q0 q1 q2 q3 :: real.
    q3 = 1 - (q0 + q1 + q2) \<and>
    r1 = q0 + q2 + q3 - ( p0 + p2 + p3 ) \<and>
    r2 = q2 + q3 - ( p2 + p3) \<and>
    r3 = q0 + q2 - ( p0 + p2) \<and>
    r4 = q0 + q1 + q3 - ( p0 + p1 + p3) \<and>
    r5 = q1 + q3 - ( p1 + p3) \<and>
    r6 = q0 + q1 - ( p0 + p1) \<and>
    q0 \<ge> 0 \<and> q1 \<ge> 0 \<and> q2 \<ge> 0 \<and> q3 \<ge> 0 \<and>
    r1 \<ge> 0 \<and> r2 \<ge> 0 \<and> r3 \<ge> 0 \<and> r4 \<ge> 0 \<and> r5 \<ge> 0 \<and> r6 \<ge> 0 \<and>
    r1 + r2 + r3 + r4 + r5 + r6 > 0"
using assms(2-) unfolding assms(1)
apply (simp_all del: ex_simps)
apply (simp add: algebra_simps del: ex_simps)
apply smt
done

lemma
  fixes p0 p1 p2 :: real
  defines "p3 \<equiv> 1 - (p0 + p1 + p2)"
  assumes "p0 \<ge> 0" "p1 > 0" "p2 > 0" "p3 \<ge> 0"
  shows "\<exists>q0 q1 q2 :: real.
    let q3 = 1 - (q0 + q1 + q2);
        r1 = q0 + q2 + q3 - (p0 + p2 + p3);
        r2 = q2 + q3 - (p2 + p3);
        r3 = q0 + q2 - (p0 + p2);
        r4 = q0 + q1 + q3 - (p0 + p1 + p3);
        r5 = q1 + q3 - (p1 + p3);
        r6 = q0 + q1 - (p0 + p1)
    in
      q0 \<ge> 0 \<and> q1 \<ge> 0 \<and> q2 \<ge> 0 \<and> q3 \<ge> 0 \<and>
      r1 \<ge> 0 \<and> r2 \<ge> 0 \<and> r3 \<ge> 0 \<and> r4 \<ge> 0 \<and> r5 \<ge> 0 \<and> r6 \<ge> 0 \<and>
      (r1 + r2 + r3 + r4 + r5 + r6 > 0)"
unfolding p3_def Let_def using assms(2-)
apply (simp_all add: algebra_simps del: ex_simps)
apply auto
apply smt



(*
lemma
  assumes "p0 + p1 + p2 + p3 = 1" "p0 \<ge> 0" "p1 > 0" "p2 > 0" "p3 \<ge> 0"
  shows "\<exists>r1 r2 r3 r4 r5 r6 q0 q1 q2 q3 :: real.
    let d1 = q0 + q2 + q3 - (p0 + p2 + p3);
        d2 = q2 + q3 - (p2 + p3);
        d3 = q0 + q2 - (p0 + p2);
        d4 = q0 + q1 + q3 - (p0 + p1 + p3);
        d5 = q1 + q3 - (p1 + p3);
        d6 = q0 + q1 - (p0 + p1)
    in
      q0 \<ge> 0 \<and> q1 \<ge> 0 \<and> q2 \<ge> 0 \<and> q3 \<ge> 0 \<and> q0 + q1 + q2 + q3 = 1 \<and>
      d1 \<ge> 0 \<and> d2 \<ge> 0 \<and> d3 \<ge> 0 \<and> d4 \<ge> 0 \<and> d5 \<ge> 0 \<and> d6 \<ge> 0 \<and>
      (d1 > 0 \<or> d2 > 0 \<or> d3 > 0 \<or> d4 > 0 \<or> d5 > 0 \<or> d6 > 0)"
using assms unfolding Let_def
oops
*)


(*
0 \<le> p0 \<Longrightarrow>
0 < p1 \<Longrightarrow>
0 < p2 \<Longrightarrow>
p0 + (p1 + p2) \<le> 1 \<Longrightarrow>
\<exists>q0 q1 q2.
   0 \<le> q0 \<and>
   0 \<le> q1 \<and>
   0 \<le> q2 \<and>
   q0 + (q1 + q2) \<le> 1 \<and>
   q1 + q2 < p1 + p2
*)


lemma
  assumes "p0 + p1 + p2 + p3 = 1" "p0 \<ge> 0" "p1 > 0" "p2 > 0" "p3 \<ge> 0"
  shows "\<exists>r1 r2 r3 r4 r5 r6 q0 q1 q2 q3 :: real.
    q0 + q1 + q2 + q3 = 1 \<and> q0 \<ge> 0 \<and> q1 \<ge> 0 \<and> q2 \<ge> 0 \<and> q3 \<ge> 0 \<and>
    q0 + q2 + q3 - r1 = p0 + p2 + p3 \<and>
    q2 + q3 - r2 = p2 + p3 \<and>
    q0 + q2 - r3 = p0 + p2 \<and>
    q0 + q1 + q3 - r4 = p0 + p1 + p3 \<and>
    q1 + q3 - r5 = p1 + p3 \<and>
    q0 + q1 - r6 = p0 + p1 \<and>
    r1 + r2 + r3 + r4 + r5 + r6 > 0"*)

lemma
  shows "\<exists>r1 r2 r3 r4 r5 r6 q0 q1 q2 q3 :: real.
    q0 + q1 + q2 + q3 = 1 \<and> q0 \<ge> 0 \<and> q1 \<ge> 0 \<and> q2 \<ge> 0 \<and> q3 \<ge> 0 \<and>
    2*(q0 + q2 + q3) - r1 = 1 \<and> 2*(q2 + q3) - r2 = 1 \<and>
    2*(q0 + q2) - r3 = 1 \<and> 2*(q0 + q1 + q3) - r4 = 1 \<and>
    2*(q1 + q3) - r5 = 1 \<and> 2*(q0 + q1) - r6 = 1 \<and>
    r1 \<ge> 0 \<and> r2 \<ge> 0 \<and> r3 \<ge> 0 \<and> r4 \<ge> 0 \<and> r5 \<ge> 0 \<and> r6 \<ge> 0 \<and>
    r1 + r2 + r3 + r4 + r5 + r6 > 0"
  by smt

end
theory QSOpt_Test
imports 
  Complex_Main
  QSOpt_Exact
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

open Rat_Linear_Program;

in

fun lp_constr_to_qsopt_constr n (lhs, slack, rhs) =
  let
    val n = Rat.from_int n
    val lhs' = (Rat.from_int (~1), slack) :: map (fn x => (n, x)) lhs
  in
    (lhs', EQ, Rat.from_int rhs)
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

fun mk_inefficiency_lp_qsopt p support =
  let
    val constrs = mk_inefficiency_lp p support
    val alts = alts_of_profile p
    val n = length support
    val one = Rat.from_int 1
    val sum = map (fn x => (one, x))
    val alt_ids = alts ~~ List.tabulate (length alts, Int.toString);
    fun mk_lottery_var x = "q" ^ the (AList.lookup op aconv alt_ids x)
    val lottery_vars = map mk_lottery_var alts
    val slack_vars = map #2 constrs
 
    val constrs' = map (lp_constr_to_qsopt_constr n) constrs
    val eq = (sum lottery_vars, EQ, one)
  in
    (MAXIMIZE, sum slack_vars, eq :: constrs', [])
  end


fun find_inefficiency_witness p lottery =
  let
    val alts = alts_of_profile p
    val lottery_vars = List.tabulate (length alts, fn x => "q" ^ Int.toString x);
    fun the_default x NONE = x
      | the_default _ (SOME y) = y

    fun process_solution (diff, assignments) = 
      if diff = Rat.from_int 0 then 
        NONE 
      else 
        SOME (alts ~~ map (the_default (Rat.from_int 0) o AList.lookup op= assignments) 
          lottery_vars)
  in 
    case solve_program (mk_inefficiency_lp_qsopt p lottery) of
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
\<close>

declare [[ML_exception_trace]]

ML \<open>
val wit = find_inefficiency_witness p [@{term "b"}, @{term "c"}]

(*
val prog = mk_inefficiency_lp_qsopt p [@{term c}, @{term b}]
val _ = Rat_Linear_Program.save_program "/tmp/foo.lp" prog
val sol = Rat_Linear_Program.solve_program prog
*)
\<close>

ML_val \<open>split_lines "asdf\nfoobar"\<close>

ML \<open>



\<close>



end
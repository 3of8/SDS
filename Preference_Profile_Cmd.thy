(*  
  Title:    Preference_Profiles_Cmd.thy
  Author:   Manuel Eberl, TU München

  Provides the preference_profile command that defines a preference profile,
  proves well-formedness and provides some useful rules for it.
*)

section \<open>Automatic definition of Preference Profiles\<close>

theory Preference_Profile_Cmd
imports
  Complex_Main
  Probability
  Social_Decision_Schemes
  Preference_Profiles
  Missing_Permutations
keywords
  "preference_profile" :: thy_goal
begin

context agenda
begin

lemma preferred_alts_prefs_from_table:
  assumes "prefs_from_table_wf agents alts xs" "i \<in> set (map fst xs)"
  shows   "preferred_alts (prefs_from_table xs i) x = 
             of_weak_ranking_Collect_ge (rev (the (map_of xs i))) x"
proof -
  interpret pref_profile_wf agents alts "prefs_from_table xs"
    by (intro pref_profile_from_tableI assms)
  from assms have [simp]: "i \<in> agents" by (auto simp: prefs_from_table_wf_def)
  have "of_weak_ranking_Collect_ge (rev (the (map_of xs i))) x = 
          Collect (of_weak_ranking (the (map_of xs i)) x)"
    by (rule eval_Collect_of_weak_ranking [symmetric])
  also from assms(2) have "the (map_of xs i) \<in> set (map snd xs)"
    by (cases "map_of xs i") (force simp: map_of_eq_None_iff dest: map_of_SomeD)+
  from prefs_from_table_wfD(5)[OF assms(1) this]
    have "Collect (of_weak_ranking (the (map_of xs i)) x) = 
            {y\<in>alts. of_weak_ranking (the (map_of xs i)) x y}"
    by safe (force elim!: of_weak_ranking.cases)
  also from assms 
    have "of_weak_ranking (the (map_of xs i)) = prefs_from_table xs i"
    by (subst prefs_from_table_map_of[OF assms(1)])
       (auto simp: prefs_from_table_wf_def)
  finally show ?thesis by (simp add: of_weak_ranking_Collect_ge_def preferred_alts_altdef)
qed

lemma favorites_prefs_from_table:
  assumes wf: "prefs_from_table_wf agents alts xs" and i: "i \<in> agents"
  shows   "favorites (prefs_from_table xs) i = hd (the (map_of xs i))"
proof (cases "map_of xs i")
  case None
  with assms show ?thesis
    by (auto simp: map_of_eq_None_iff prefs_from_table_wf_def)
next
  case (Some y)
  with assms have "is_finite_weak_ranking y" "y \<noteq> []"
    by (auto simp: prefs_from_table_wf_def)
  with Some show ?thesis
    unfolding favorites_def using assms
    by (simp add: prefs_from_table_def is_finite_weak_ranking_def 
                  Max_wrt_of_weak_ranking prefs_from_table_wfD)
qed 

lemma has_unique_favorites_prefs_from_table:
  assumes wf: "prefs_from_table_wf agents alts xs"
  shows   "has_unique_favorites (prefs_from_table xs) = 
             list_all (\<lambda>z. is_singleton (hd (snd z))) xs"
proof -
  interpret pref_profile_wf agents alts "prefs_from_table xs"
    by (intro pref_profile_from_tableI assms)
  from wf have "agents = set (map fst xs)" "distinct (map fst xs)"
    by (auto simp: prefs_from_table_wf_def)
  thus ?thesis
    unfolding has_unique_favorites_altdef using assms
    by (auto simp: favorites_prefs_from_table list_all_iff)
qed

end


subsection \<open>Automatic definition of preference profiles from tables\<close>

function favorites_prefs_from_table where
  "i = j \<Longrightarrow> favorites_prefs_from_table ((j,x)#xs) i = hd x"
| "i \<noteq> j \<Longrightarrow> favorites_prefs_from_table ((j,x)#xs) i =
               favorites_prefs_from_table xs i"
| "favorites_prefs_from_table [] i = {}"
  by (metis list.exhaust old.prod.exhaust) auto
termination by lexicographic_order

lemma (in agenda) eval_favorites_prefs_from_table:
  assumes "prefs_from_table_wf agents alts xs"
  shows   "favorites_prefs_from_table xs i = 
             favorites (prefs_from_table xs) i"
proof (cases "i \<in> agents")
  assume i: "i \<in> agents"
  with assms have "favorites (prefs_from_table xs) i = hd (the (map_of xs i))"
    by (simp add: favorites_prefs_from_table)
  also from assms i have "i \<in> set (map fst xs)"
    by (auto simp: prefs_from_table_wf_def)
  hence "hd (the (map_of xs i)) = favorites_prefs_from_table xs i"
    by (induction xs i rule: favorites_prefs_from_table.induct) simp_all
  finally show ?thesis ..
next
  assume i: "i \<notin> agents"
  with assms have i': "i \<notin> set (map fst xs)"
    by (simp add: prefs_from_table_wf_def)
  hence "map_of xs i = None" 
    by (simp add: map_of_eq_None_iff)
  hence "prefs_from_table xs i = (\<lambda>_ _. False)"
    by (intro ext) (auto simp: prefs_from_table_def)
  hence "favorites (prefs_from_table xs) i = {}"
    by (simp add: favorites_def Max_wrt_altdef)
  also from i' have "\<dots> = favorites_prefs_from_table xs i"
    by (induction xs i rule: favorites_prefs_from_table.induct) simp_all
  finally show ?thesis ..
qed

lemma eval_prefs_from_table_aux:
  assumes "R \<equiv> prefs_from_table xs" "prefs_from_table_wf agents alts xs"
  shows   "R i a b \<longleftrightarrow> prefs_from_table xs i a b"
          "a \<prec>[R i] b \<longleftrightarrow> prefs_from_table xs i a b \<and> \<not>prefs_from_table xs i b a"
          "anonymous_profile agents R = mset (map snd xs)"
          "agenda agents alts \<Longrightarrow> i \<in> set (map fst xs) \<Longrightarrow> 
             preferred_alts (R i) x = 
             of_weak_ranking_Collect_ge (rev (the (map_of xs i))) x"
          "agenda agents alts \<Longrightarrow> i \<in> set (map fst xs) \<Longrightarrow>
             favorites R i = favorites_prefs_from_table xs i"
          "agenda agents alts \<Longrightarrow> i \<in> set (map fst xs) \<Longrightarrow>
             favorite R i = the_elem (favorites_prefs_from_table xs i)"
          "agenda agents alts \<Longrightarrow> 
             has_unique_favorites R \<longleftrightarrow> list_all (\<lambda>z. is_singleton (hd (snd z))) xs"
  using assms prefs_from_table_wfD[OF assms(2)]
  by (simp_all add: strongly_preferred_def favorite_def anonymise_prefs_from_table
        agenda.preferred_alts_prefs_from_table agenda.eval_favorites_prefs_from_table
        agenda.has_unique_favorites_prefs_from_table)

lemma pref_profile_from_tableI':
  assumes "R1 \<equiv> prefs_from_table xss" "prefs_from_table_wf agents alts xss"
  shows   "pref_profile_wf agents alts R1"
  using assms by (simp add: pref_profile_from_tableI)

subsection \<open>Automorphisms\<close>

lemma an_sds_automorphism_aux:
  assumes wf: "pref_profile_wf agents alts R"
  assumes eq: "anonymous_profile agents (permute_profile \<sigma> R) = anonymous_profile agents R"
  assumes perm: "\<sigma> permutes alts"
  assumes "anonymous_neutral_sds agents alts sds"
  assumes x: "x \<in> alts"
  shows   "pmf (sds R) (\<sigma> x) = pmf (sds R) x"
proof -
  from assms(4) interpret anonymous_neutral_sds agents alts sds .
  from perm x have "pmf (sds R) x = pmf (map_pmf \<sigma> (sds R)) (\<sigma> x)"
    by (simp add: pmf_map_inj' permutes_inj)
  also from assms have "map_pmf \<sigma> (sds R) = sds R"
    by (intro sds_automorphism) simp_all
  finally show ?thesis ..
qed

ML \<open>

signature PREFERENCE_PROFILES =
sig

type prefs
type profile
type info
type support
type lottery
type 'a permutation

val pref_profileT : typ -> typ -> typ

val preference_profile : 
  (term * term) * ((binding * (term * term list list) list) list) -> Proof.context -> Proof.state

val preference_profile_cmd : 
  (string * string) * ((binding * (string * string list list) list) list) -> 
    Proof.context -> Proof.state

val get_info : term -> Proof.context -> info
val add_info : term -> info -> Context.generic -> Context.generic
val transform_info : info -> morphism -> info

val eq_prefs : (prefs * prefs) -> bool
val equiv_profile_anonymity : (profile * profile) -> bool

val agents_of_profile : profile -> term list
val alts_of_profile : profile -> term list

val apply_permutation : ('a * 'a -> bool) -> 'a permutation -> 'a -> 'a
val is_identity : ('a * 'a -> bool) -> 'a permutation -> bool
val fixpoints : ('a * 'a -> bool) -> 'a permutation -> 'a list
val permutations : ('a * 'a -> bool) -> 'a list -> 'a permutation Seq.seq
val cycles : ('a * 'a -> bool) -> 'a permutation -> 'a list list

val find_an_isomorphisms : profile * profile -> term permutation Seq.seq
val find_an_isomorphism : profile * profile -> term permutation option
val find_an_automorphisms : profile -> (term * term) list
val pareto_pairs : profile -> (term * term) list

val mk_inefficiency_lp : profile -> support -> (string list * string * int) list
val find_inefficiency_witness : profile -> support -> lottery option

end

structure Preference_Profiles : PREFERENCE_PROFILES =
struct

type prefs = term list list
type profile = (term * prefs) list
type 'a permutation = ('a * 'a) list
type support = term list
type lottery = (term * string) list

val eq_prefs = eq_list (eq_set (op aconv))

fun equiv_profile_anonymity xy = 
  let
    val xy = apply2 (map snd) xy
  in
    submultiset eq_prefs xy andalso submultiset eq_prefs (swap xy)
  end
  
val agents_of_profile = map fst

val alts_of_profile = List.concat o snd o hd


fun fixpoints eq xs = xs |> filter eq |> map fst

fun apply_permutation _ [] x = x
  | apply_permutation eq ((x,y)::p) x' = if eq (x,x') then y else apply_permutation eq p x'

val is_identity = forall

fun cycles eq =
  let
    fun go3 _ _ [] = raise Match
      | go3 acc a ((b,c) :: xs) =
         if eq (a,b) then (c, acc @ xs) else go3 ((b,c) :: acc) a xs
    fun go2 cyc a b xs =
      if eq (a,b) then 
        (cyc, xs) 
      else case go3 [] b xs of
        (c, xs) => go2 (b::cyc) a c xs
    fun go1 acc [] = acc
      | go1 acc ((a,b) :: xs) = 
          case go2 [a] a b xs of (cyc, xs') => go1 (rev cyc :: acc) xs'
  in
    rev o go1 []
  end    

fun permutations eq xs = 
  let
    fun go acc [] = Seq.single acc
      | go acc xs = Seq.maps (fn x => go (x::acc) (remove1 eq x xs)) (Seq.of_list xs)
  in
    Seq.map (fn ys => xs ~~ ys) (go [] xs)
  end

fun find_an_isomorphisms (xs, ys) =
  let
    fun is_iso p = 
      equiv_profile_anonymity (map (fn (x, yss) => (x, map (map p) yss)) xs, ys)
  in
    permutations (op aconv) (alts_of_profile xs)
    |> Seq.filter (is_iso o apply_permutation (op aconv))
  end

val find_an_isomorphism =
  find_an_isomorphisms #> Seq.pull #> Option.map fst

fun seq_fold f s acc =
  case Seq.pull s of
    NONE => acc
  | SOME (x,s) => seq_fold f s (f x acc)

fun find_an_automorphisms xs =
  let
    fun eq ((a,b),(c,d)) = (a aconv c andalso b aconv d) orelse (a aconv d andalso b aconv c)
  in
    (xs, xs) 
    |> find_an_isomorphisms
    |> Seq.map (filter_out (op aconv))
    |> (fn s => seq_fold (fn x => fn y => merge eq (x,y)) s [])
  end


fun preferred_alts r x =
  let
    fun go acc [] = acc
      | go acc (xs::xss) =
          if member op aconv xs x then (xs @ acc) else go (xs @ acc) xss
  in
    go [] r
  end


fun fold1 f [] = raise Match
  | fold1 f (x::xs) = fold f xs x

fun pareto_pairs p =
  let
    val alts = alts_of_profile p
    fun dom_set x =
      let
        fun go [] = []
          | go (xs::xss) = 
              if member op aconv xs x then List.concat (xs::xss) else go xss
      in
        fold (fn (_, xss) => inter op aconv (go xss)) p alts
      end
    fun filter_out_symmetric xs =
      filter_out (fn (x,y) => member (eq_pair op aconv op aconv) xs (y, x)) xs
    val filter_out_trans =
      let
        fun go acc [] = acc
          | go acc (x::xs) =
              if member (op aconv o apply2 snd) acc x then 
                go acc xs 
              else 
                go (x::acc) xs
      in
        go []
      end
  in
    alts
    |> map (fn x => map (fn y => (x, y)) (dom_set x))
    |> List.concat
    |> filter_out_symmetric
    |> filter_out_trans
  end
    

(*
fun mk_inefficiency_lp p lottery =
  let
    val alts = alts_of_profile p
    val alt_ids = alts ~~ List.tabulate (length alts, Int.toString);
    val lottery_prob = AList.lookup op aconv lottery #> the
    fun mk_lottery_var x = "q" ^ the (AList.lookup op aconv alt_ids x)
    fun mk_slack_var i j = "r" ^ Int.toString i ^ "_" ^ Int.toString j

    fun mk_ineqs_for_agent acc _ [] _ i = acc
      | mk_ineqs_for_agent acc _ [_] _ i = acc
      | mk_ineqs_for_agent acc (lhs, rhs) (xs::xss) j i =
          let
            val lhs' = map mk_lottery_var xs @ lhs
            val rhs' = map lottery_prob xs @ rhs
          in
            mk_ineqs_for_agent ((lhs',mk_slack_var i j,rhs')::acc) (lhs',rhs') xss (j+1) i
          end
  in
    fold (fn (_, r) => fn (i,acc) => (i+1, mk_ineqs_for_agent acc ([],[]) r 0 i)) p (0, []) |> snd
  end
*)

fun mk_inefficiency_lp p support =
  let
    val alts = alts_of_profile p
    val alt_ids = alts ~~ List.tabulate (length alts, Int.toString);
    val in_support = member op aconv support
    fun mk_lottery_var x = "q" ^ the (AList.lookup op aconv alt_ids x)
    fun mk_slack_var i j = "r" ^ Int.toString i ^ "_" ^ Int.toString j

    fun mk_ineqs_for_agent acc _ [] _ i = acc
      | mk_ineqs_for_agent acc _ [_] _ i = acc
      | mk_ineqs_for_agent acc (lhs, rhs) (xs::xss) j i =
          let
            val lhs' = map mk_lottery_var xs @ lhs
            val rhs' = length (filter in_support xs) + rhs
          in
            mk_ineqs_for_agent ((lhs',mk_slack_var i j,rhs')::acc) (lhs',rhs') xss (j+1) i
          end
  in
    fold (fn (_, r) => fn (i,acc) => (i+1, mk_ineqs_for_agent acc ([],0) r 0 i)) p (0, []) |> snd
  end

fun find_inefficiency_witness p supp =
  undefined ()



type info = 
  { term : term, def_thm : thm, wf_thm : thm, wf_raw_thm : thm, 
    raw : (term * term list list) list, eval_thms : thm list }

fun transform_info ({term = t, def_thm, wf_thm, wf_raw_thm, raw, eval_thms} : info) phi =
    let
      val thm = Morphism.thm phi
      val fact = Morphism.fact phi
      val term = Morphism.term phi
    in
      { term = term t, def_thm = thm def_thm, wf_thm = thm wf_thm, wf_raw_thm = thm wf_raw_thm, 
        raw = map (fn (a, bss) => (term a, map (map term) bss)) raw,
        eval_thms = fact eval_thms }
    end

structure Data = Generic_Data
(
  type T = (term * info) Item_Net.T
  val empty = Item_Net.init (op aconv o apply2 fst) (single o fst)
  val extend = I
  val merge = Item_Net.merge
);

fun get_info term lthy = 
  Item_Net.retrieve (Data.get (Context.Proof lthy)) term |> the_single |> snd

fun add_info term info lthy =
  Data.map (Item_Net.update (term, info)) lthy
  
fun add_infos infos lthy =
  Data.map (fold Item_Net.update infos) lthy
 
fun pref_profileT agentT altT = agentT --> altT --> altT --> HOLogic.boolT

fun preference_profile_aux agents alts (binding, args) lthy = 
  let
    val dest_Type' = Term.dest_Type #> snd #> hd
    val (agentT, altT) = apply2 (dest_Type' o fastype_of) (agents, alts)
    val alt_setT = HOLogic.mk_setT altT
    fun define t = 
      Local_Theory.define ((binding, NoSyn), ((Binding.suffix_name "_def" binding, []), t)) lthy
    val ty = HOLogic.mk_prodT (agentT, HOLogic.listT (HOLogic.mk_setT altT))
    val args' = 
      args |> map (fn x => x ||> map (HOLogic.mk_set altT) ||> HOLogic.mk_list alt_setT)
    val t_raw = 
      args' 
        |> map HOLogic.mk_prod 
        |> HOLogic.mk_list ty
    val t = Const (@{const_name prefs_from_table}, 
              HOLogic.listT ty --> pref_profileT agentT altT) $ t_raw
    val ((prefs, prefs_def), lthy) = define t
    val prefs_from_table_wf_const = 
      Const (@{const_name prefs_from_table_wf}, HOLogic.mk_setT agentT --> HOLogic.mk_setT altT --> 
          HOLogic.listT (HOLogic.mk_prodT (agentT, HOLogic.listT (HOLogic.mk_setT altT))) -->
          HOLogic.boolT)
    val wf_prop = (prefs_from_table_wf_const $ agents $ alts $ t_raw) |> HOLogic.mk_Trueprop

  in
    ((prefs, wf_prop, prefs_def), lthy)
  end

fun fold_accum f xs s =
  let
    fun fold_accum_aux _ [] s acc = (rev acc, s)
      | fold_accum_aux f (x::xs) s acc = 
          case f x s of (y, s') => fold_accum_aux f xs s' (y::acc)
  in
    fold_accum_aux f xs s []
  end

fun preference_profile ((agents, alts), args) lthy =
  let
    val (results, lthy) = fold_accum (preference_profile_aux agents alts) args lthy
    val prefs_terms = map #1 results
    val wf_props = map #2 results
    val defs = map (snd o #3) results
    val raws = map snd args
    val bindings = map fst args

    fun tac lthy =
       let 
         val lthy' = put_simpset HOL_ss lthy addsimps
           @{thms list.set Union_insert Un_insert_left insert_not_empty Int_empty_left Int_empty_right
              insert_commute Un_empty_left Un_empty_right insert_absorb2 Union_empty
              is_weak_ranking_Cons is_weak_ranking_Nil finite_insert finite.emptyI
              Set.singleton_iff Set.empty_iff Set.ball_simps}
        in
          Local_Defs.unfold_tac lthy defs
            THEN ALLGOALS (resolve_tac lthy [@{thm prefs_from_table_wfI}])
            THEN Local_Defs.unfold_tac lthy @{thms is_finite_weak_ranking_def list.set insert_iff
               empty_iff simp_thms list.map snd_conv fst_conv}
            THEN ALLGOALS (TRY o REPEAT_ALL_NEW (eresolve_tac lthy @{thms disjE}))
            THEN ALLGOALS (TRY o Hypsubst.hyp_subst_tac lthy)
            THEN ALLGOALS (Simplifier.asm_full_simp_tac lthy')
            THEN ALLGOALS (TRY o REPEAT_ALL_NEW (resolve_tac lthy @{thms conjI}))
            THEN distinct_subgoals_tac
        end

    fun after_qed [wf_thms_raw] lthy =
      let
        fun prep_thms attrs suffix (thms : thm list) binding = 
          (((Binding.suffix_name suffix binding, attrs), [(thms,[])]))
        fun prep_thmss simp suffix thmss = map2 (prep_thms simp suffix) thmss bindings
        fun notes thmss suffix attrs lthy = 
            Local_Theory.notes (prep_thmss attrs suffix thmss) lthy |> snd
        fun note thms suffix attrs lthy = notes (map single thms) suffix attrs lthy
        val eval_thmss = map2 (fn def => fn wf => 
          map (fn thm => thm OF [def, wf]) @{thms eval_prefs_from_table_aux}) 
          defs wf_thms_raw
        val wf_thms = map2 (fn def => fn wf => 
          @{thm pref_profile_from_tableI'} OF [def, wf]) defs wf_thms_raw
        val mk_infos =
          let 
            fun aux acc (t::ts) (r::raws) (def::def_thms) (wf::wf_thms) 
                   (wf_raw::wf_raw_thms) (evals::eval_thmss) =
              aux ((t, {term = t, raw = r, def_thm = def, wf_thm = wf, wf_raw_thm = wf_raw, 
                eval_thms = evals}) :: acc) ts raws def_thms wf_thms wf_raw_thms eval_thmss
            | aux acc [] _ _ _ _ _ = (acc : (term * info) list)
            | aux _ _ _ _ _ _ _ = raise Match
          in
            aux []
          end
        val infos = mk_infos prefs_terms raws defs wf_thms wf_thms_raw eval_thmss
      in
        lthy 
        |> note wf_thms_raw "_wf_raw" []
        |> note wf_thms "_wf" @{attributes [simp]} 
        |> notes eval_thmss "_eval" []
        |> Local_Theory.declaration {syntax = false, pervasive = false}
             (fn m => add_infos (map (fn (t,i) => (Morphism.term m t, transform_info i m)) infos))
      end
    | after_qed _ _ = raise Match

  in
    Proof.theorem NONE after_qed [map (fn prop => (prop, [])) wf_props] lthy
    |> Proof.refine_singleton (Method.Basic (SIMPLE_METHOD o tac))
  end

fun preference_profile_cmd ((agents, alts), argss) lthy =
  let
    val read = Syntax.read_term lthy
    val alts' = read alts
    fun read_pref_elem ts = map read ts
    fun read_prefs prefs = map read_pref_elem prefs
    fun prep (binding, args) = 
      (binding, map (fn (agent, prefs) => (read agent, read_prefs prefs)) args)
  in
    preference_profile ((read agents, alts'), map prep argss) lthy
  end

val parse_prefs = 
  let
    val parse_pref_elem = 
      (Args.bracks (Parse.list1 Parse.term)) ||
      Parse.term >> single
  in
    Parse.list1 parse_pref_elem
  end

val parse_pref_profile =
  Parse.binding --| Args.$$$ "=" -- Scan.repeat1 (Parse.term --| Args.colon -- parse_prefs)

val _ =
  Outer_Syntax.local_theory_to_proof @{command_keyword preference_profile}
    "construct preference profiles from a table"
    (Args.$$$ "agents" |-- Args.colon |-- Parse.term --| Args.$$$ "alts" --| Args.colon 
       -- Parse.term --| Args.$$$ "where" --
     Parse.and_list1 parse_pref_profile >> preference_profile_cmd);

end
\<close>


(* TODO: For testing only; can be removed *)
datatype agents = A1 | A2 | A3 | A4
datatype alts = a | b | c | d

preference_profile 
  agents: "{A1, A2, A3, A4}"
  alts:   "{a, b, c, d}"
  where R1  = A1: [a,c], [b,d]     A2: [b,d], [a,c]     A3: [a,d], b, c     A4: [b,c], a, d
    and R2  = A1: [a,c], [b,d]     A2: [b,d], [a,c]     A3: a, d, [b,c]     A4: b, c, [a, d]
by (simp_all add: insert_eq_iff)

lemma "anonymous_profile {A1, A2, A3, A4} R1 = 
  {#[{a, c}, {b, d}], [{b, d}, {a, c}], [{a, d}, {b}, {c}], [{b, c}, {a}, {d}]#}"
  by (simp add: R1_eval add_ac)

lemma
  defines "\<sigma> \<equiv> permutation_of_list [(a,b),(b,a),(c,d),(d,c)]"
  assumes "anonymous_neutral_sds {A1,A2,A3,A4} {a,b,c,d} sds"
  shows   "pmf (sds R1) (\<sigma> a) = pmf (sds R1) a"
  by (rule an_sds_automorphism_aux[OF R1_wf, of \<sigma> sds])
     (simp_all add: assms insert_commute insert_eq_iff add_ac
        distincts_Cons pref_profile_wf.anonymous_profile_permute[OF R1_wf] R1_eval)

lemma
  defines "\<sigma> \<equiv> lists_succ [[a,b],[c,d]]"
  assumes "anonymous_neutral_sds {A1,A2,A3,A4} {a,b,c,d} sds"
  shows   "pmf (sds R1) (\<sigma> a) = pmf (sds R1) a"
  apply (rule an_sds_automorphism_aux[OF R1_wf, of \<sigma> sds])
  apply (simp_all add: assms lists_succ_permutes' insert_commute 
           distincts_Cons pref_profile_wf.anonymous_profile_permute[OF R1_wf])
  apply (simp add: R1_eval list_succ_simps add_ac)
  done


ML_val \<open>
  open Preference_Profiles;
  
  let
    val ctxt = @{context}
    val {raw = raw1, ...} = Preference_Profiles.get_info @{term R1} ctxt
    val {raw = raw2, ...} = Preference_Profiles.get_info @{term R2} ctxt
    val b = Preference_Profiles.equiv_profile_anonymity (raw1, raw2)
    val w = Preference_Profiles.find_an_isomorphisms (raw1, raw2) |> Seq.list_of
    val auto = find_an_automorphisms raw1
  in
    auto |> cycles op aconv |> map (map (Thm.cterm_of @{context}))
  end
  
\<close>

end
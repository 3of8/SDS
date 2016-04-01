signature MYRAT =
sig
  type rat
  
  val of_quotient : int * int -> rat
  val to_quotient  : rat -> int * int
  val from_int : int -> rat
  val to_real : rat -> real
  val from_string : string -> rat option
  val to_string : rat -> string
  val to_string' : rat -> string

  val + : rat * rat -> rat
  val ~ : rat -> rat
  val - : rat * rat -> rat
  val * : rat * rat -> rat
  val / : rat * rat -> rat
  val < : rat * rat -> bool
  val <= : rat * rat -> bool
  val > : rat * rat -> bool
  val >= : rat * rat -> bool

  val compare : rat * rat -> General.order

  val mult_int : rat -> int -> rat
  val div_int : rat -> int -> rat
  val sign : rat -> int
  val abs : rat -> rat

  val floor : rat -> int
  val ceil : rat -> int

  val dest_rat_numeral : term -> rat

end

structure MyRat : MYRAT = 
struct

datatype rat = Rat of int * int;

(* Rational numbers *)

fun gcd a b = 
  let fun gcd' a 0 = a 
        | gcd' a b = gcd b (a mod b)
  in  gcd' (abs a) (abs b)
  end;

fun of_quotient (_, 0) = raise Div
  | of_quotient (a, b) = 
  let val g = gcd a b 
      val (a', b') = if b<0 then (~a,~b) else (a,b)
  in  Rat (a' div g, b' div g)
  end;

fun to_quotient (Rat x) = x

fun from_int a = Rat (a, 1)

fun int_to_string a = if a < 0 then "-" ^ Int.toString (~a) else Int.toString a

fun to_string (Rat (a, 1)) = int_to_string a
  | to_string (Rat (a, b)) = Int.toString a ^ " / " ^ Int.toString b

fun to_string' (Rat (a, 1)) = int_to_string a
  | to_string' (Rat (a, b)) = int_to_string a ^ " / " ^ Int.toString b


fun from_string s =
  let
    val (s1, s2') = s |> Substring.full |> Substring.splitl (fn x => x <> #"/") 
    val (s1, s2) = (s1, s2') |> apsnd (Substring.triml 1) |> apply2 Substring.string
  in
    if Substring.isEmpty s2' then
      Option.map from_int (Int.fromString s1)
    else
      Option.mapPartial (fn x => Option.map (fn y => of_quotient (x, y)) 
        (Int.fromString s2)) (Int.fromString s1)
  end

fun to_real (Rat (a, b)) = Real.fromInt a / Real.fromInt b
fun sign (Rat (a,_)) = Int.sign a;
fun abs (Rat (a,b)) = Rat (Int.abs a, b)

fun radd (Rat (a1,b1), Rat (a2,b2)) = of_quotient (a1*b2+a2*b1,b1*b2);
fun rneg (Rat (a1, b1)) = Rat (~a1, b1)
fun rmul (Rat (a1,b1), Rat (a2,b2)) = of_quotient (a1*a2, b1*b2);
fun rdiv (Rat (a1,b1), Rat (a2,b2)) = of_quotient (a1*b2,b1*a2);
fun rsub (Rat (a1,b1), Rat (a2,b2)) = of_quotient (a1*b2-a2*b1,b1*b2);
fun rless (Rat (a1,b1), Rat (a2,b2)) = a1*b2 < a2*b1;
fun rleq (Rat (a1,b1), Rat (a2,b2)) = a1*b2 <= a2*b1;
fun rgt (Rat (a1,b1), Rat (a2,b2)) = a1*b2 > a2*b1;
fun rgeq (Rat (a1,b1), Rat (a2,b2)) = a1*b2 >= a2*b1;

fun div_int (Rat (a1,b1)) c = of_quotient (a1,b1*c);
fun mult_int (Rat (a1,b1)) c = of_quotient (a1*c,b1);

fun floor (Rat (x, y)) = x div y
fun ceil (Rat (x, y)) = if x mod y = 0 then x div y else x div y + 1

val op + = radd
val ~ = rneg
val op - = rsub
val op * = rmul
val op / = rdiv
val op < = rless
val op <= = rleq
val op > = rgt
val op >= = rgeq

fun compare (i, j) =
    if i < j then General.LESS
    else if i > j then General.GREATER else General.EQUAL

(* Destructors for rational numbers / polynomials *)

fun dest_num x = 
  case x of 
    Const ("Code_Numeral.int_of_integer", _) $ x => dest_num x
  | _ => HOLogic.dest_number x

fun dest_rat_numeral t =
  case t of 
    (Const ("Rings.divide_class.divide",_)) $ a $ b
      => of_quotient (snd (dest_num a), snd (dest_num b))
  | (Const ("Groups.uminus_class.uminus",_)) $ a 
      => rneg (dest_rat_numeral a)
  | (Const ("Rat.field_char_0_class.of_rat",_)) $ a => dest_rat_numeral a
  |  (Const ("Rat.Frct", _) $ (Const ("Product_Type.Pair", _) $ a $ b))
      => of_quotient (snd (dest_num a), snd (dest_num b))
  | _ => from_int (snd (dest_num t));

end

val _ = PolyML.addPrettyPrinter (K (K (PolyML.PrettyString o MyRat.to_string)));

val () = RunCall.addOverload MyRat.~ "~";
val () = RunCall.addOverload MyRat.+ "+";
val () = RunCall.addOverload MyRat.- "-";
val () = RunCall.addOverload MyRat.* "*";
val () = RunCall.addOverload MyRat./ "/";
val () = RunCall.addOverload MyRat.< "<";
val () = RunCall.addOverload MyRat.> ">";
val () = RunCall.addOverload MyRat.<= "<=";
val () = RunCall.addOverload MyRat.>= ">=";
val () = RunCall.addOverload MyRat.abs "abs";

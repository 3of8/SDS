signature MYRAT =
sig
  type rat
  
  val zero : rat
  val one : rat
  val of_quotient : int * int -> rat
  val to_quotient  : rat -> int * int
  val from_int : int -> rat
  val to_real : rat -> real
  val from_string : string -> rat option
  val to_string : rat -> string
  val pretty : rat -> string

  val compare : rat * rat -> General.order
  val rneg : rat -> rat
  val radd : (rat * rat) -> rat
  val rsub : (rat * rat) -> rat
  val rmult : (rat * rat) -> rat
  val inv : rat -> rat
  val rdiv : (rat * rat) -> rat
  val rleq : (rat * rat) -> bool
  val rless : (rat * rat) -> bool
  val rgt : (rat * rat) -> bool
  val rgeq : (rat * rat) -> bool

  val mult_int : rat -> int -> rat
  val div_int : rat -> int -> rat
  val sign : rat -> int
  val abs : rat -> rat

  val floor : rat -> int
  val ceil : rat -> int

  val dest_rat_number : term -> rat
  val mk_rat_number : typ -> rat -> term

end

structure MyRat : MYRAT = 
struct

datatype rat = Rat of int * int;

val zero = Rat (0, 1)
val one = Rat (1, 1)

fun of_quotient (_, 0) = raise Div
  | of_quotient (a, b) = 
  let val g = PolyML.IntInf.gcd (a, b)
      val (a', b') = if b < 0 then (~a,~b) else (a,b)
  in  Rat (a' div g, b' div g)
  end;

fun to_quotient (Rat x) = x

fun from_int a = Rat (a, 1)

fun to_string (Rat (a, 1)) = Int.toString a
  | to_string (Rat (a, b)) = 
      (if a < 0 then "~ " else "") ^ Int.toString (abs a) ^ " / " ^ Int.toString b

fun pretty (Rat (a, 1)) = (if a < 0 then "-" else "") ^ Int.toString a
  | pretty (Rat (a, b)) = 
      (if a < 0 then "- " else "") ^ Int.toString (abs a) ^ " / " ^ Int.toString b


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
fun rmult (Rat (a1,b1), Rat (a2,b2)) = of_quotient (a1*a2, b1*b2);
fun rdiv (Rat (a1,b1), Rat (a2,b2)) = of_quotient (a1*b2,b1*a2);
fun inv (Rat (a, b)) = 
  case int_ord (a, 0) of
    LESS => Rat (~b, ~a)
  | GREATER => Rat (b, a)
  | EQUAL => raise Div
fun rsub (Rat (a1,b1), Rat (a2,b2)) = of_quotient (a1*b2-a2*b1,b1*b2);
fun rless (Rat (a1,b1), Rat (a2,b2)) = a1*b2 < a2*b1;
fun rleq (Rat (a1,b1), Rat (a2,b2)) = a1*b2 <= a2*b1;
fun rgt (Rat (a1,b1), Rat (a2,b2)) = a1*b2 > a2*b1;
fun rgeq (Rat (a1,b1), Rat (a2,b2)) = a1*b2 >= a2*b1;

fun div_int (Rat (a1,b1)) c = of_quotient (a1,b1*c);
fun mult_int (Rat (a1,b1)) c = of_quotient (a1*c,b1);

fun floor (Rat (x, y)) = x div y
fun ceil (Rat (x, y)) = 
  case Integer.div_mod x y of
    (q, r) => if r = 0 then q else q + 1

fun compare (Rat (a,b), Rat (c,d)) = Int.compare (a * d, b * c)

(* Destructors for rational numbers / polynomials *)

fun dest_num x = 
  case x of 
    Const (@{const_name "Code_Numeral.int_of_integer"}, _) $ x => dest_num x
  | _ => HOLogic.dest_number x

fun dest_rat_number t =
  case t of 
    (Const (@{const_name "Rings.divide_class.divide"},_)) $ a $ b
      => of_quotient (snd (dest_num a), snd (dest_num b))
  | (Const (@{const_name "Groups.uminus_class.uminus"},_)) $ a 
      => rneg (dest_rat_number a)
  | (Const (@{const_name "Rat.field_char_0_class.of_rat"},_)) $ a => dest_rat_number a
  |  (Const (@{const_name "Rat.Frct"}, _) $ (Const (@{const_name "Product_Type.Pair"}, _) $ a $ b))
      => of_quotient (snd (dest_num a), snd (dest_num b))
  | _ => from_int (snd (dest_num t));

fun mk_rat_number ty (Rat (a, 1)) = HOLogic.mk_number ty a
  | mk_rat_number ty (Rat (a, b)) = 
      Const (@{const_name Rings.divide_class.divide}, ty --> ty --> ty) $ 
        HOLogic.mk_number ty a $ HOLogic.mk_number ty b

end

val _ = PolyML.addPrettyPrinter (K (K (PolyML.PrettyString o MyRat.to_string)));

val () = RunCall.addOverload MyRat.rneg "~";
val () = RunCall.addOverload MyRat.radd "+";
val () = RunCall.addOverload MyRat.rsub "-";
val () = RunCall.addOverload MyRat.rmult "*";
val () = RunCall.addOverload MyRat.rdiv "/";
val () = RunCall.addOverload MyRat.rless "<";
val () = RunCall.addOverload MyRat.rgt ">";
val () = RunCall.addOverload MyRat.rleq "<=";
val () = RunCall.addOverload MyRat.rgeq ">=";
val () = RunCall.addOverload MyRat.abs "abs";

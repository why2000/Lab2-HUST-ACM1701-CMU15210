functor MkBigNumMultiply(structure BNA : BIGNUM_ADD
                         structure BNS : BIGNUM_SUBTRACT
                         sharing BNA.Util = BNS.Util) : BIGNUM_MULTIPLY =
struct
  structure Util = BNA.Util
  open Util
  open Seq
  open Primitives
  exception NotYetImplemented

  (* 6/7: priority of operators *)
  infix 6 ++ --
  infix 7 **

  fun x ++ y = BNA.add (x, y)
  fun x -- y = BNS.sub (x, y)
  fun x ** y = 
    let
      val diff = length x - length y
      val (larger, smaller) =
        if x > y then (x, append (tabulate (fn i => reversebit (nth y i)) (length y), tabulate (fn _ => ONE) diff))
        else if x < y then (x, append (tabulate (fn i => reversebit (nth y i)) (length y), tabulate (fn _ => ONE) (~diff)))
        else (x, y)
      val (p, q) = if length x > 1 then (drop(x, length x), take(x, length x - 1)) else (singleton(ZERO), )
      val (r, s) = (drop(y, length y - 1), take(y, length y - 1))
    in
      Seq.fromList [ONE]
    end
	       
  val mul = op**
end

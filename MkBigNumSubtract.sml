functor MkBigNumSubtract(structure BNA : BIGNUM_ADD) : BIGNUM_SUBTRACT =
struct
  structure Util = BNA.Util
  open Util
  open Seq

  exception NotYetImplemented
  infix 6 ++ --
  fun x ++ y = BNA.add (x, y)
  fun x -- y =
    let
      (* A simple function to reverse ONE and ZERO *)
      fun reversebit (b : bit) : bit = if b = ONE then ZERO else ONE
      (* save the difference of lengths *)
      val diff = length x - length y
      (* flip y, with set to the same length as x. ZERO on sign bit means positive, ONE means negative *)
      val reversed = append (tabulate (fn i => reversebit (nth y i)) (length y), tabulate (fn _ => ONE) diff)
      (* by adding a ONE, we get the negative y *)
      val negated = reversed ++ singleton(ONE)
    in
      (* add x and negative y. throw the sign bit *)
      tabulate (fn i => nth (x ++ negated) i) (length x)
    end
    
  val sub = op--
end

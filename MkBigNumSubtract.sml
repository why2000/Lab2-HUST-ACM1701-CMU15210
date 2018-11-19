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
      (* A simple function to reverse ONE and ZERO, with W = S = O(1) *)
      fun reversebit (b : bit) : bit = if b = ONE then ZERO else ONE
      (* save the difference of lengths, W = S = O(1) *)
      val diff = length x - length y
      (* flip y, with setting it to the same length as x. ZERO on sign bit means positive, ONE means negative *)
      (* append n elements altogether, W = O(n), S = O(1) *)
      val reversed = append (tabulate (fn i => reversebit (nth y i)) (length y), tabulate (fn _ => ONE) (diff+1))
      (* by adding a ONE, we get the negative y, with W = W_++ = O(n+1), S = S_++ = O(lg(n+1)) *)
      val negated = reversed ++ singleton(ONE)
      (* add x and negative y. throw the sign bit *)
      (* add between length n and length n+1, with W = O(2n+1), S = O(lg(2n+1)) *)
      val result = tabulate (fn i => nth (x ++ negated) i) (length x)
      (* check for ZERO *)
      fun bitcheck(x, y) = if x = ZERO andalso y = ZERO then ZERO else ONE

    in
      (* check whether result is zero. W = O(n), S = O(lgn) *)
      if reduce bitcheck ZERO result = ZERO then empty() else result
      (* finally we get:
        * Work = O(n) + O(n+1) + O(2n+1) + O(1) = O(n)
        * Span = O(lg(2n+1)) + O(lg(n+1)) + O(lgn) + O(1) = O(lgn)
        *)
    end
    
  val sub = op--
end

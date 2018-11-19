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
    case (length x, length y)
      (* notice that we need to return empty() when result = 0. *)
      of (0, _) => empty ()
       | (_, 0) => empty ()
       | (1, _) => if nth x 0 = ZERO then empty() else y
       | (_, 1) => if nth y 0 = ZERO then empty() else x
       | (_, _) =>
        let
          (* judge which one is larger, then setting them to the same length. S = O(1). *)
          val diff = length x - length y
          val (larger, smaller) =
            if diff > 0 then (x, append(y, tabulate (fn _ => ZERO) diff))
            else if diff < 0 then (y, append(x, tabulate (fn _ => ZERO) (~diff)))
            else (x, y)
          
          (* showt them into p, q, r, s, with larger = (p*2^m + q), smaller = (r*2^m+s). S = O(1). *)
          val (q, p) = 
            case showt larger
              of EMPTY => (empty (), empty())
               | ELT bit0 => if bit0 = ZERO then (singleton ZERO, empty()) else (singleton ONE, empty())
               | NODE (l, r) => (l, r)
          val (s, r) = 
            case showt smaller
              of EMPTY => (empty (), empty())
               | ELT bit0 => if bit0 = ZERO then (singleton ZERO, empty()) else (singleton ONE, empty())
               | NODE (l, r) => (l, r)
          
          (* 
            * @res_a = (p+q) * (r+s)
            * @res_b = p*r
            * @res_c = q*s
            * calculate them in parallel costs W = 3W(n/2), S = S(n/2).
            * and we have: pq+rs = (@res_a-@res_b-@res_c)
            *)
          val (res_a, res_b, res_c) = par3 (fn _ => (p++q) ** (r++s), fn _ => p**r, fn _ => q**s)
        in
          (*  x*y = (p*2^m + q)*(r*2^m+s) = p*r*2^(2m) + (pq+rs)*2^m + qs = @res_b*2^(2m) + (@res_a-@res_b-@res_c)*2^m + res_c.
            * obviously m = length q, so the following sentence can calculate x*y correctly.
            * notice that the square of a number has the length shorter than three times of itself(with (2^n-1)^2 has the length 2n-1 = 2(n-1) + 1 as the most)
            * append with length q costs O(n), add those `shorter than 3*(length n)` things together costs W = O(3n), which is also W = O(n)
            * S = O(1).
            *)
          (append(tabulate (fn _ => ZERO) (length q * 2), res_b) ++ append(tabulate (fn _ => ZERO) (length q), ((res_a -- res_b) -- res_c)) ++ res_c)
          (*  finally we have:
            * W(n) = 3W(n/2) + O(n).
            * S(n) = S(n/2) + O(lgn), which means S(n) = lgn*O(lgn) = O((lgn)^2)
            *)
        end
	       
  val mul = op**
end

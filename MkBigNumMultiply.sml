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
      of (0, _) => empty ()
       | (_, 0) => empty ()
       | (1, _) => if nth x 0 = ZERO then empty() else y
       | (_, 1) => if nth y 0 = ZERO then empty() else x
       | (_, _) =>
        let
          fun btostring(b) = if b = ZERO then print("0") else print("1")
          fun bstostring(now) = if length now > 1 then let val pt = btostring (nth now 0) in bstostring (drop(now, 1)) end else btostring (nth now 0)
          val diff = length x - length y
          val (larger, smaller) =
            if diff > 0 then (x, append(y, tabulate (fn _ => ZERO) diff))
            else if diff < 0 then (y, append(x, tabulate (fn _ => ZERO) (~diff)))
            else (x, y)
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
          (* val (p, q) = if (length larger) > 1 then (drop(larger, length larger - 1), take(larger, length larger - 1)) else (empty (), singleton(nth larger 0))
          val (r, s) = if (length smaller) > 1 then (drop(smaller, length smaller - 1), take(smaller, length smaller - 1)) else (empty (), singleton(nth smaller 0)) *)
          (* val ptnl = print"\nlarger:"
          val ptl = bstostring larger
          val ptns = print"\nsmaller:"
          val pts = bstostring smaller
          val ptnp = print"\np:"
          val ptp = bstostring p
          val ptnq = print"\nq:"
          val ptq = bstostring q
          val ptnr = print"\nr:"
          val ptr = bstostring r
          val ptns = print"\ns:"
          val pts = bstostring s *)
          val (res1, res2, res3) = par3 (fn _ => (p++q) ** (r++s), fn _ => p**r, fn _ => q**s)
        in
          (append(tabulate (fn _ => ZERO) (length q * 2), res2) ++ res3 ++ append(tabulate (fn _ => ZERO) (length q), ((res1 -- res2) -- res3)))
        end
	       
  val mul = op**
end

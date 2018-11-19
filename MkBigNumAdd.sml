functor MkBigNumAdd(structure U : BIGNUM_UTIL) : BIGNUM_ADD =
struct
  structure Util = U
  open Util
  open Seq

  infix 6 ++
  exception NotYetImplemented
  datatype carry = GEN | PROP | STOP

  fun x ++ y =
    case (length x, length y)
      (* notice that given 0 ++ 0, we need to return empty() instead of singleton(ZERO) *)
      of (0, 0) => empty()
       | (_, _) =>
        let
          (* add two bignum without carry to generate the mid(raw) seq *)
          (* W = S = O(1) *)
          fun bitaddtocarry (x : bit, y : bit) : carry =
            case (x, y)
              of (ZERO, ZERO) => STOP
              | (ONE, ONE) => GEN
              | ((ONE, ZERO) | (ZERO, ONE)) => PROP

          val diff = length x - length y

          (* in this seq, STOP/GEN means ZERO, PROP means ONE *)
          (* call bitaddtocarry max{m, n} times. W = O(m+n), S = O(1) *)
          val rawseq = if diff > 0 then map2 bitaddtocarry x (append(y, tabulate (fn _ => ZERO) diff))
                  else if diff < 0 then map2 bitaddtocarry y (append(x, tabulate (fn _ => ZERO) (~diff)))
                  else map2 bitaddtocarry x y
          
          (* If the last is STOP/GEN, it must gives ZERO/ONE for the next one.
            * But if it's PROP, the carry status will remain as the previous one is.
            * W = S = O(1)
            *)
          fun bitcarry (c1, c2) : carry = 
            case c2
              of PROP => c1
              | (GEN | STOP) => c2
          
          (* in this seq, GEN/STOP means whether to add a ONE or not, determined by previous ones *)
          (* since length = max{m, n} = O(m+n), scan costs W = O(m+n), S = O(lg(m+n)) *)
          val (carryseq, most) = scan bitcarry STOP rawseq

          (* 
            * rawseq saves the infomation of 0/1
            * carryseq saves the infomation of whether to carry
            * use scan to transplace forwards for one bit.
            * STOP means this bit is what saved in the rawseq.
            * GEN means this bit need to be flipped from what is in the rawseq.
            *)
          (* W = S = O(1) *)
          fun bitgrow (c1 : carry, c2 : carry) : bit =
            case (c1, c2)
              of (c1, GEN) => if c1 = PROP then ZERO else ONE
               | (c1, STOP) => if c1 = PROP then ONE else ZERO
          
          (* map2 has such cost: W = O(m+n) * O(1) = O(m+n), S = O(1) *)
          val resseq = map2 bitgrow rawseq carryseq
        in
          (* check whether to carry ONE to the most place. W = O(m+n), S = O(1) *)
          if most = GEN then append(resseq, singleton(ONE)) else resseq
          (* final costs are:
            * Work = O(m+n) + O(1) = O(m+n)
            * Span = O(lg(m+n)) + O(1) = O(lg(m+n))
            *)
        end
    
  val add = op++
end

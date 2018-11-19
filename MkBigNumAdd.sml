functor MkBigNumAdd(structure U : BIGNUM_UTIL) : BIGNUM_ADD =
struct
  structure Util = U
  open Util
  open Seq

  infix 6 ++
  exception NotYetImplemented
  datatype carry = GEN | PROP | STOP

  fun x ++ y =
    let
      fun bitaddtocarry (x : bit, y : bit) : carry =
        case (x, y)
          of (ZERO, ZERO) => STOP
           | (ONE, ONE) => GEN
           | ((ONE, ZERO) | (ZERO, ONE)) => PROP

      val diff = length x - length y

      (* in this seq, STOP/GEN means ZERO, PROP means ONE *)
      val rawseq = if diff > 0 then map2 bitaddtocarry x (append(y, tabulate (fn _ => ZERO) diff))
              else if diff < 0 then map2 bitaddtocarry y (append(x, tabulate (fn _ => ZERO) (~diff)))
              else map2 bitaddtocarry x y
      
      (* If the last is STOP/GEN, it must gives ZERO/ONE for the next one.
        * But if it's PROP, the carry status will remain as the previous one is.
        *)
      fun bitcarry (c1, c2) : carry = 
        case c2
          of PROP => c1
           | (GEN | STOP) => c2
      
      (* in this seq, GEN/STOP means whether to add a ONE or not, determined by previous ones *)
      val (carryseq, most) = scan bitcarry STOP rawseq
      fun bitgrow (c1 : carry, c2 : carry) : bit =
        case (c1, c2)
          of (PROP, c2) => if c2 = GEN then ZERO else ONE
           | (_, c2) => if c2 = GEN then ONE else ZERO
      
      val resseq = map2 bitgrow rawseq carryseq
    in
      if most = GEN then append(resseq, singleton(ONE)) else resseq
    end
    
  val add = op++
end

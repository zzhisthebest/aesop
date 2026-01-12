module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_15418
public def rotate_precond (a : Array Int) (offset : Int) : Prop :=
  offset ≥ 0

public def rotateAux (a : Array Int) (offset : Int) (i : Nat) (len : Nat) (b : Array Int) : Array Int :=
  if i < len then
    let idx_int : Int := (Int.ofNat i + offset) % (Int.ofNat len)
    let idx_int_adjusted := if idx_int < 0 then idx_int + Int.ofNat len else idx_int
    let idx_nat : Nat := Int.toNat idx_int_adjusted
    let new_b := b.set! i (a[idx_nat]!)
    rotateAux a offset (i + 1) len new_b
  else b

public def rotate (a : Array Int) (offset : Int) (h_precond : rotate_precond (a) (offset)) : Array Int :=
  let len := a.size
  let default_val : Int := if len > 0 then a[0]! else 0
  let b0 := Array.mkArray len default_val
  rotateAux a offset 0 len b0

public def rotate_postcond (a : Array Int) (offset : Int) (result: Array Int) (h_precond : rotate_precond (a) (offset)) :=
  result.size = a.size ∧
  (∀ i : Nat, i < a.size →
    result[i]! = a[Int.toNat ((Int.ofNat i + offset) % (Int.ofNat a.size))]!)


public theorem mod_eq_mod_if_nonneg (i : Nat) (offset : Int) (len : Nat) (hpos : 0 < len) :
    ((Int.ofNat i + offset) % (Int.ofNat len)) =
      if ((Int.ofNat i + offset) % (Int.ofNat len)) < 0
        then ((Int.ofNat i + offset) % (Int.ofNat len)) + Int.ofNat len
        else ((Int.ofNat i + offset) % (Int.ofNat len)):= by 
sorry


end tmp_lemma_15418
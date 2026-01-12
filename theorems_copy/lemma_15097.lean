module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_15097
public def DivisionFunction_precond (x : Nat) (y : Nat) : Prop :=
  True

public def divMod (x y : Nat) : Int × Int :=
  let q : Int := Int.ofNat (x / y)
  let r : Int := Int.ofNat (x % y)
  (r, q)

public def DivisionFunction (x : Nat) (y : Nat) (h_precond : DivisionFunction_precond (x) (y)) : Int × Int :=
  if y = 0 then (Int.ofNat x, 0) else divMod x y

public def DivisionFunction_postcond (x : Nat) (y : Nat) (result: Int × Int) (h_precond : DivisionFunction_precond (x) (y)) :=
  let (r, q) := result;
  (y = 0 → r = Int.ofNat x ∧ q = 0) ∧
  (y ≠ 0 → (q * Int.ofNat y + r = Int.ofNat x) ∧ (0 ≤ r ∧ r < Int.ofNat y) ∧ (0 ≤ q))


public theorem nat_mod_lt (x y : Nat) (h : y ≠ 0) : x % y < y:= by 
sorry


end tmp_lemma_15097
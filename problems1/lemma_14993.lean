import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def DivisionFunction_precond (x : Nat) (y : Nat) : Prop :=
  True

def divMod (x y : Nat) : Int × Int :=
  let q : Int := Int.ofNat (x / y)
  let r : Int := Int.ofNat (x % y)
  (r, q)

def DivisionFunction (x : Nat) (y : Nat) (h_precond : DivisionFunction_precond (x) (y)) : Int × Int :=
  if y = 0 then (Int.ofNat x, 0) else divMod x y

@[reducible, simp]
def DivisionFunction_postcond (x : Nat) (y : Nat) (result: Int × Int) (h_precond : DivisionFunction_precond (x) (y)) :=
  let (r, q) := result;
  (y = 0 → r = Int.ofNat x ∧ q = 0) ∧
  (y ≠ 0 → (q * Int.ofNat y + r = Int.ofNat x) ∧ (0 ≤ r ∧ r < Int.ofNat y) ∧ (0 ≤ q))


theorem mul_div_add_mod (x y : Nat) :
    (x / y) * y + x % y = x:= by 
aesop


end tmp
import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def rotateRight_precond (l : List Int) (n : Nat) : Prop :=
  True

def rotateRight (l : List Int) (n : Nat) (h_precond : rotateRight_precond (l) (n)) : List Int :=
  let len := l.length
  if len = 0 then l
  else
    (List.range len).map (fun i : Nat =>
      let idx_int : Int := ((Int.ofNat i - Int.ofNat n + Int.ofNat len) % Int.ofNat len)
      let idx_nat : Nat := Int.toNat idx_int
      l.getD idx_nat (l.headD 0)
    )

@[reducible, simp]
def rotateRight_postcond (l : List Int) (n : Nat) (result: List Int) (h_precond : rotateRight_precond (l) (n)) :=
  result.length = l.length ∧
  (∀ i : Nat, i < l.length →
    let len := l.length
    let rotated_index := Int.toNat ((Int.ofNat i - Int.ofNat n + Int.ofNat len) % Int.ofNat len)
    result[i]? = l[rotated_index]?)


theorem rotateRight_nth (l : List Int) (n i : Nat)
    (h : rotateRight_precond l n) (hi : i < l.length) :
    (rotateRight l n h)[i]? =
      l[
        Int.toNat
          ((Int.ofNat i - Int.ofNat n + Int.ofNat l.length) % Int.ofNat l.length)
        ]?:= by 
  aesop?


end tmp
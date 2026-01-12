import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def swap_precond (arr : Array Int) (i : Int) (j : Int) : Prop :=
  i ≥ 0 ∧
  j ≥ 0 ∧
  Int.toNat i < arr.size ∧
  Int.toNat j < arr.size

def swap (arr : Array Int) (i : Int) (j : Int) (h_precond : swap_precond (arr) (i) (j)) : Array Int :=
  let i_nat := Int.toNat i
  let j_nat := Int.toNat j
  let arr1 := arr.set! i_nat (arr[j_nat]!)
  let arr2 := arr1.set! j_nat (arr[i_nat]!)
  arr2

@[reducible, simp]
def swap_postcond (arr : Array Int) (i : Int) (j : Int) (result: Array Int) (h_precond : swap_precond (arr) (i) (j)) :=
  (result[Int.toNat i]! = arr[Int.toNat j]!) ∧
  (result[Int.toNat j]! = arr[Int.toNat i]!) ∧
  (∀ (k : Nat), k < arr.size → k ≠ Int.toNat i → k ≠ Int.toNat j → result[k]! = arr[k]!)


theorem swap_get_other (arr : Array Int) (i j : Int)
    (h : swap_precond arr i j) {k : Nat}
    (hk : k < arr.size) (hki : k ≠ Int.toNat i) (hkj : k ≠ Int.toNat j) :
    (swap arr i j h)[k]! = arr[k]!:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp
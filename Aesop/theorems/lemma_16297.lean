module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_16297
public def swap_precond (arr : Array Int) (i : Int) (j : Int) : Prop :=
  i ≥ 0 ∧
  j ≥ 0 ∧
  Int.toNat i < arr.size ∧
  Int.toNat j < arr.size

public def swap (arr : Array Int) (i : Int) (j : Int) (h_precond : swap_precond (arr) (i) (j)) : Array Int :=
  let i_nat := Int.toNat i
  let j_nat := Int.toNat j
  let arr1 := arr.set! i_nat (arr[j_nat]!)
  let arr2 := arr1.set! j_nat (arr[i_nat]!)
  arr2

public def swap_postcond (arr : Array Int) (i : Int) (j : Int) (result: Array Int) (h_precond : swap_precond (arr) (i) (j)) :=
  (result[Int.toNat i]! = arr[Int.toNat j]!) ∧
  (result[Int.toNat j]! = arr[Int.toNat i]!) ∧
  (∀ (k : Nat), k < arr.size → k ≠ Int.toNat i → k ≠ Int.toNat j → result[k]! = arr[k]!)


public theorem swap_aux (arr : Array Int) (i j : Int) (h_precond : swap_precond arr i j) :
    let i_nat := Int.toNat i
    let j_nat := Int.toNat j
    let arr1 := arr.set! i_nat (arr[j_nat]!)
    let arr2 := arr1.set! j_nat (arr[i_nat]!)
    ((arr2[Int.toNat i]! = arr[Int.toNat j]!) ∧
     (arr2[Int.toNat j]! = arr[Int.toNat i]!) ∧
     (∀ k, k < arr.size → k ≠ Int.toNat i → k ≠ Int.toNat j → arr2[k]! = arr[k]!)):= by 
sorry


end tmp_lemma_16297
import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def modify_array_element_precond (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) : Prop :=
  index1 < arr.size ∧
  index2 < (arr[index1]!).size

def updateInner (a : Array Nat) (idx val : Nat) : Array Nat :=
  a.set! idx val

def modify_array_element (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (h_precond : modify_array_element_precond (arr) (index1) (index2) (val)) : Array (Array Nat) :=
  let inner := arr[index1]!
  let inner' := updateInner inner index2 val
  arr.set! index1 inner'

@[reducible, simp]
def modify_array_element_postcond (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (result: Array (Array Nat)) (h_precond : modify_array_element_precond (arr) (index1) (index2) (val)) :=
  (∀ i, i < arr.size → i ≠ index1 → result[i]! = arr[i]!) ∧
  (∀ j, j < (arr[index1]!).size → j ≠ index2 → (result[index1]!)[j]! = (arr[index1]!)[j]!) ∧
  ((result[index1]!)[index2]! = val)


theorem get_set_eq (a : Array Nat) (i v : Nat) (h : i < a.size) :
    (a.set! i v)[i]! = v:= by 
aesop?(config := { enableGrind := false })


end tmp
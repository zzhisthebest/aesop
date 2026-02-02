import Codetic
set_option maxHeartbeats 0
namespace tmp
def isOdd (x : Int) : Bool :=
  x % 2 ≠ 0

@[reducible, simp]
def findFirstOdd_precond (a : Array Int) : Prop :=
  a.size > 0

def findFirstOdd (a : Array Int) (h_precond : findFirstOdd_precond (a)) : Option Nat :=
  let indexed := a.toList.zipIdx

  let found := List.find? (fun (x, _) => isOdd x) indexed

  Option.map (fun (_, i) => i) found

@[reducible, simp]
def findFirstOdd_postcond (a : Array Int) (result: Option Nat) (h_precond : findFirstOdd_precond (a)) :=
  match result with
  | some idx => idx < a.size ∧ isOdd (a[idx]!) ∧
    (∀ j, j < idx → ¬ isOdd (a[j]!))
  | none => ∀ i, i < a.size → ¬ isOdd (a[i]!)


theorem length_zipIdx (a : Array Int) :
    (a.toList.zipIdx).length = a.size:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp
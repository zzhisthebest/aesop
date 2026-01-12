import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def ToArray_precond (xs : List Int) : Prop :=
  True

def ToArray (xs : List Int) (h_precond : ToArray_precond (xs)) : Array Int :=
  xs.toArray

@[reducible, simp]
def ToArray_postcond (xs : List Int) (result: Array Int) (h_precond : ToArray_precond (xs)) :=
  result.size = xs.length ∧ ∀ (i : Nat), i < xs.length → result[i]! = xs[i]!


theorem toArray_size (xs : List Int) : (xs.toArray).size = xs.length:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp
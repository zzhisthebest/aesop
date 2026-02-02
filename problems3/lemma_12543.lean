import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def double_array_elements_precond (s : Array Int) : Prop :=
  True

def double_array_elements_aux (s_old s : Array Int) (i : Nat) : Array Int :=
  if i < s.size then
    let new_s := s.set! i (2 * (s_old[i]!))
    double_array_elements_aux s_old new_s (i + 1)
  else
    s

def double_array_elements (s : Array Int) (h_precond : double_array_elements_precond (s)) : Array Int :=
  double_array_elements_aux s s 0

@[reducible, simp]
def double_array_elements_postcond (s : Array Int) (result: Array Int) (h_precond : double_array_elements_precond (s)) :=
  result.size = s.size ∧ ∀ i, i < s.size → result[i]! = 2 * s[i]!


theorem result_elements (s : Array Int) (h_precond : double_array_elements_precond s) :
    ∀ i, i < s.size → (double_array_elements s h_precond)[i]! = 2 * s[i]!:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp
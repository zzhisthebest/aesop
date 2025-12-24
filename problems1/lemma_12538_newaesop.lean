import Aesop
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


theorem double_array_elements_aux_inv (s_old s : Array Int) (i : Nat)
    (hsz : s.size = s_old.size)
    (hproc : ∀ j, j < i → s[j]! = 2 * s_old[j]!) :
    (double_array_elements_aux s_old s i).size = s_old.size ∧
    (∀ j, j < s_old.size →
        (double_array_elements_aux s_old s i)[j]! = 2 * s_old[j]!):= by 
  aesop?


end tmp
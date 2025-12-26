import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  True

def LinearSearch (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) : Nat :=
  let rec loop (n : Nat) : Nat :=
    if n < a.size then
      if a[n]! = e then n
      else loop (n + 1)
    else n
  loop 0

@[reducible, simp]
def LinearSearch_postcond (a : Array Int) (e : Int) (result: Nat) (h_precond : LinearSearch_precond (a) (e)) :=
  result ≤ a.size ∧ (result = a.size ∨ a[result]! = e) ∧ (∀ i, i < result → a[i]! ≠ e)


theorem LinearSearch_result_no_earlier (a : Array Int) (e : Int)
    (h_precond : LinearSearch_precond a e) :
    ∀ i, i < LinearSearch a e h_precond → a[i]! ≠ e:= by
  induction i using LinearSearch.loop.induct a e with
  | case1 i h_lt h_found =>
    unfold LinearSearch.loop
    aesop
  | case2 i h_lt h_not_found ih =>
    unfold LinearSearch.loop
    aesop
  | case3 i h_not_lt =>
    unfold LinearSearch.loop
    aesop

end tmp

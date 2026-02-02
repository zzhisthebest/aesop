import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def minOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  True

def minOfThree (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) : Int :=
  if a <= b && a <= c then a
  else if b <= a && b <= c then b
  else c

@[reducible, simp]
def minOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : minOfThree_precond (a) (b) (c)) :=
  (result <= a ∧ result <= b ∧ result <= c) ∧
  (result = a ∨ result = b ∨ result = c)


theorem minOfThree_branch₂
    (a b c : Int) (h_pre : minOfThree_precond a b c)
    (h₁ : ¬ (a ≤ b ∧ a ≤ c)) (h₂ : b ≤ a ∧ b ≤ c) :
    minOfThree a b c h_pre = b:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp
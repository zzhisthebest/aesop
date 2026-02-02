import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def onlineMax_precond (a : Array Int) (x : Nat) : Prop :=
  a.size > 0 ∧ x < a.size

def findBest (a : Array Int) (x : Nat) (i : Nat) (best : Int) : Int :=
  if i < x then
    let newBest := if a[i]! > best then a[i]! else best
    findBest a x (i + 1) newBest
  else best

def findP (a : Array Int) (x : Nat) (m : Int) (i : Nat) : Nat :=
  if i < a.size then
    if a[i]! > m then i else findP a x m (i + 1)
  else a.size - 1

def onlineMax (a : Array Int) (x : Nat) (h_precond : onlineMax_precond (a) (x)) : Int × Nat :=
  let best := a[0]!
  let m := findBest a x 1 best;
  let p := findP a x m x;
  (m, p)

@[reducible, simp]
def onlineMax_postcond (a : Array Int) (x : Nat) (result: Int × Nat) (h_precond : onlineMax_precond (a) (x)) :=
  let (m, p) := result;
  (x ≤ p ∧ p < a.size) ∧
  (∀ i, i < x → a[i]! ≤ m) ∧
  (∃ i, i < x ∧ a[i]! = m) ∧
  ((p < a.size - 1) → (∀ i, i < p → a[i]! < a[p]!)) ∧
  ((∀ i, x ≤ i → i < a.size → a[i]! ≤ m) → p = a.size - 1)


theorem onlineMax_unfold (a : Array Int) (x : Nat) (h : onlineMax_precond a x) :
    onlineMax a x h = (findBest a x 1 a[0]!, findP a x (findBest a x 1 a[0]!) x):= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp
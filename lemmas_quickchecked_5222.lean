import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def nthUglyNumber_precond (n : Nat) : Prop :=
  n > 0

def nextUgly (seq : List Nat) (c2 c3 c5 : Nat) : (Nat × Nat × Nat × Nat) :=
  let i2 := seq[c2]! * 2
  let i3 := seq[c3]! * 3
  let i5 := seq[c5]! * 5
  let next := min i2 (min i3 i5)
  let c2' := if next = i2 then c2 + 1 else c2
  let c3' := if next = i3 then c3 + 1 else c3
  let c5' := if next = i5 then c5 + 1 else c5
  (next, c2', c3', c5')

def nthUglyNumber (n : Nat) (h_precond : nthUglyNumber_precond (n)) : Nat :=
  let rec loop (i : Nat) (seq : List Nat) (c2 c3 c5 : Nat) : List Nat :=
    match i with
    | 0 => seq
    | Nat.succ i' =>
      let (next, c2', c3', c5') := nextUgly seq c2 c3 c5
      loop i' (seq ++ [next]) c2' c3' c5'
  (loop (n - 1) [1] 0 0 0)[(n - 1)]!

def divideOut : Nat → Nat → Nat
  | n, p =>
    if h : p > 1 ∧ n > 0 ∧ n % p = 0 then
      have : n / p < n := by
        apply Nat.div_lt_self
        · exact h.2.1
        · exact Nat.lt_of_succ_le (Nat.succ_le_of_lt h.1)
      divideOut (n / p) p
    else n
termination_by n p => n

def isUgly (x : Nat) : Bool :=
  if x = 0 then
    false
  else
    let n1 := divideOut x 2
    let n2 := divideOut n1 3
    let n3 := divideOut n2 5
    n3 = 1

@[reducible, simp]
def nthUglyNumber_postcond (n : Nat) (result: Nat) (h_precond : nthUglyNumber_precond (n)) : Prop :=
  isUgly result = true ∧
  ((List.range (result)).filter (fun i => isUgly i)).length = n - 1


theorem divideOut_lt (n p : Nat) (hpos : p > 1) (hposn : n > 0) (hmod : n % p = 0) :
    divideOut n p < n:= by
  simp_all only [gt_iff_lt]
  induction n, p using tmp.divideOut.induct
  · unfold tmp.divideOut
    simp_all only [gt_iff_lt, and_self, Nat.div_pos_iff, and_imp, forall_const, ↓reduceDIte]
    induction p✝ with
    | zero =>
      unfold tmp.divideOut
      unfold tmp.divideOut at ih1✝
      simp_all only [Nat.zero_eq, Nat.div_zero, Nat.not_lt_zero]
    | succ a =>
      unfold tmp.divideOut
      unfold tmp.divideOut at ih1✝
      simp only [Nat.succ_eq_add_one, Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, gt_iff_lt, Nat.div_pos_iff, true_and,
        dite_eq_ite, forall_const] at *
      simp_all only [forall_const, and_self, ↓reduceIte, true_and]
      split
      next n n_ih this ih1 h =>
        simp_all only [forall_const]
        obtain ⟨left, right⟩ := h
        grind
      next n n_ih this ih1 h => simp_all only [not_and]
  · unfold tmp.divideOut
    simp_all only [gt_iff_lt, and_self, not_true_eq_false]
  aesop?(config := { useDefaultSimpSet := false })


end tmp

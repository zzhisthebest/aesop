import Aesop
set_option maxHeartbeats 0
namespace tmp
def filterlist (x : Int) (nums : List Int) : List Int :=
  let rec aux (lst : List Int) : List Int :=
    match lst with
    | []      => []
    | y :: ys => if y = x then y :: aux ys else aux ys
  aux nums

@[reducible]
def FindSingleNumber_precond (nums : List Int) : Prop :=
  let numsCount := nums.map (fun x => nums.count x)
  numsCount.all (fun count => count = 1 ∨ count = 2) ∧ numsCount.count 1 = 1

def FindSingleNumber (nums : List Int) (h_precond : FindSingleNumber_precond (nums)) : Int :=
  let rec findUnique (remaining : List Int) : Int :=
    match remaining with
    | [] =>
      0
    | x :: xs =>
      let filtered : List Int :=
        filterlist x nums
      let count : Nat :=
        filtered.length
      if count = 1 then
        x
      else
        findUnique xs
  findUnique nums

@[reducible]
def FindSingleNumber_postcond (nums : List Int) (result: Int) (h_precond : FindSingleNumber_precond (nums)) : Prop :=
  (nums.length > 0)
  ∧
  ((filterlist result nums).length = 1)
  ∧
  (∀ (x : Int),
    x ∈ nums →
    (x = result) ∨ ((filterlist x nums).length = 2))
example {a b:Nat}:a=b:=by
  induction a

theorem count_two_iff (x : Int) (xs : List Int) :
    xs.count x = 2 → (filterlist x xs).length = 2:= by
  intro a
  simp_all only [filterlist]
  induction xs with
  | @nil =>
    unfold tmp.filterlist.aux
    simp_all only [List.count_nil, reduceCtorEq]
  | @cons a_1 a_1_1 =>
    unfold tmp.filterlist.aux
    simp_all only
    split
    next tail_ih h =>
      subst h
      simp_all only [List.count_cons_self, Nat.reduceEqDiff, List.length_cons, false_implies]
      induction a_1_1 with
      | @nil =>
        unfold tmp.filterlist.aux
        simp_all only [List.count_nil, Nat.zero_ne_one]
      | @cons a_2 a_1_2 =>
        unfold tmp.filterlist.aux
        simp_all only
        split
        next tail_ih h =>
          subst h
          simp_all only [List.count_cons_self, Nat.add_eq_right, List.length_cons, List.length_eq_zero_iff,
            Nat.zero_ne_one, false_implies]
          induction a_1_2 with
          | @nil =>
            unfold tmp.filterlist.aux
            simp_all only [List.count_nil]
          | @cons a_1 a_1_1 =>
            unfold tmp.filterlist.aux
            simp_all only
            split
            next tail_ih h =>
              subst h
              simp_all only [List.count_cons_self, Nat.add_eq_zero, Nat.succ_ne_self, and_false]
            next tail_ih h => simp_all only [ne_eq, not_false_eq_true, List.count_cons_of_ne]
        next tail_ih h => simp_all only [ne_eq, not_false_eq_true, List.count_cons_of_ne]
    next tail_ih h => simp_all only [ne_eq, not_false_eq_true, List.count_cons_of_ne]


end tmp

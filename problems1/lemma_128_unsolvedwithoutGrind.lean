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


theorem count_one_mem {l : List Int} {a : Int} (h : l.count a = 1) : a ∈ l:= by
induction l with
| @nil => simp_all only [List.count_nil, Nat.zero_ne_one]
| @cons a_1 a_1_1 =>
  simp_all only [List.count_cons, beq_iff_eq, List.mem_cons]
  split at h
  next tail_ih h_1 =>
    subst h_1
    simp_all only [Nat.add_eq_right, true_or]
  next tail_ih h_1 => simp_all only [Nat.add_zero, or_true]


end tmp

import Codetic
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


theorem count_eq_one_imp_mem (x : Int) (l : List Int) (h : l.count x = 1) :
    x ∈ l:= by
induction l with
| @nil => simp_all only [List.count_nil, Nat.zero_ne_one]
| @cons a a_1 =>
  simp_all only [List.mem_cons]
  suffices ¬x=a→x ∈ a_1 by codetic
  codetic?(config := { enableGrind := false })

codetic?(config := { enableGrind := false })


end tmp
--搞出了一个定理，但依然无法直接codetic?(config := { enableGrind := false })证明。

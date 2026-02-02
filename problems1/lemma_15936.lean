import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def get2d (a : Array (Array Int)) (i j : Int) : Int :=
  (a[Int.toNat i]!)[Int.toNat j]!

@[reducible, simp]
def SlopeSearch_precond (a : Array (Array Int)) (key : Int) : Prop :=
  List.Pairwise (·.size = ·.size) a.toList ∧
  a.all (fun x => List.Pairwise (· ≤ ·) x.toList) ∧
  (
    a.size = 0 ∨ (
      (List.range (a[0]!.size)).all (fun i =>
        List.Pairwise (· ≤ ·) (a.map (fun x => x[i]!)).toList
      )
    )
  )

def SlopeSearch (a : Array (Array Int)) (key : Int) (h_precond : SlopeSearch_precond (a) (key)) : (Int × Int) :=
  let rows := a.size
  let cols := if rows > 0 then (a[0]!).size else 0

  let rec aux (m n : Int) (fuel : Nat) : (Int × Int) :=
    if fuel = 0 then (-1, -1)
    else if m ≥ Int.ofNat rows || n < 0 then (-1, -1)
    else if get2d a m n = key then (m, n)
    else if get2d a m n < key then
      aux (m + 1) n (fuel - 1)
    else
      aux m (n - 1) (fuel - 1)

  aux 0 (Int.ofNat (cols - 1)) (rows + cols)

@[reducible, simp]
def SlopeSearch_postcond (a : Array (Array Int)) (key : Int) (result: (Int × Int)) (h_precond : SlopeSearch_precond (a) (key)) :=
  let (m, n) := result;
  (m ≥ 0 ∧ m < a.size ∧ n ≥ 0 ∧ n < (a[0]!).size ∧ get2d a m n = key) ∨
  (m = -1 ∧ n = -1 ∧ a.all (fun x => x.all (fun e => e ≠ key)))


theorem cols_eq_size_of_nonempty (a : Array (Array Int)) (h : a.size > 0) :
    (let cols := if a.size > 0 then (a[0]!).size else 0; cols) = (a[0]!).size:= by 
codetic?(config := { enableGrind := false })


end tmp
import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def searchInsert_precond (xs : List Int) (target : Int) : Prop :=
  List.Pairwise (· < ·) xs

def searchInsert (xs : List Int) (target : Int) (h_precond : searchInsert_precond (xs) (target)) : Nat :=
  match xs with
  | [] =>
      0
  | _ :: _ =>
      let rec helper : List Int → Nat → Nat :=
        fun ys idx =>
          match ys with
          | [] =>
              idx
          | y :: ys' =>
              let isCurrent := y
              let currentIndex := idx
              let targetValue := target
              let condition := targetValue ≤ isCurrent
              if condition then
                currentIndex
              else
                let incrementedIndex := currentIndex + 1
                let rest := ys'
                helper rest incrementedIndex
      let startingIndex := 0
      let result := helper xs startingIndex
      result

@[reducible]
def searchInsert_postcond (xs : List Int) (target : Int) (result: Nat) (h_precond : searchInsert_precond (xs) (target)) : Prop :=
  let allBeforeLess := (List.range result).all (fun i => xs[i]! < target)
  let inBounds := result ≤ xs.length
  let insertedCorrectly :=
    result < xs.length → target ≤ xs[result]!
  inBounds ∧ allBeforeLess ∧ insertedCorrectly


theorem all_before_less (xs : List Int) (target : Int)
    (h : List.Pairwise (· < ·) xs) :
    let r := searchInsert xs target h
    (List.range r).all (fun i => xs[i]! < target):= by 
  aesop?


end tmp
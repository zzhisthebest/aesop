import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def longestIncreasingSubsequence_precond (nums : List Int) : Prop :=
  True

def longestIncreasingSubsequence (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) : Int :=
  Id.run do
    if nums.isEmpty then return 0
    let mut sub : Array Int := Array.empty
    sub := sub.push nums.head!
    for num in nums.tail do
      if num > sub[sub.size - 1]! then
        sub := sub.push num
      else
        let mut left : Nat := 0
        let mut right : Nat := sub.size - 1
        while left < right do
          let mid := (left + right) / 2
          if sub[mid]! == num then
            right := mid
          else if sub[mid]! < num then
            left := mid + 1
          else
            right := mid
        sub := sub.set! left num
    return Int.ofNat sub.size

@[reducible]
def longestIncreasingSubsequence_postcond (nums : List Int) (result: Int) (h_precond : longestIncreasingSubsequence_precond (nums)) : Prop :=
  let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)


theorem list_tail_eq_drop (l : List Int) (h : l ≠ []) :
    l.tail = l.drop 1:= by 
codetic?(config := { enableGrind := false })


end tmp
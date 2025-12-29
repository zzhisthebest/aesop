import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def maxSubarraySum_precond (numbers : List Int) : Prop :=
  True

def maxSubarraySum (numbers : List Int) (h_precond : maxSubarraySum_precond (numbers)) : Int :=
  let rec isAllNegative : List Int → Bool
    | [] => true
    | x :: xs => if x >= 0 then false else isAllNegative xs

  let rec findMaxProduct : List Int → Int → Int → Int
    | [], currMax, _ => currMax
    | [x], currMax, _ => max currMax x
    | x :: y :: rest, currMax, currSum =>
        let newSum := max y (currSum + y)
        let newMax := max currMax newSum
        findMaxProduct (y :: rest) newMax newSum

  let handleList : List Int → Nat
    | [] => 0
    | xs =>
        if isAllNegative xs then
          0
        else
          match xs with
          | [] => 0
          | x :: rest =>
              let initialMax := max 0 x
              let startSum := max 0 x
              let result := findMaxProduct (x :: rest) initialMax startSum
              result.toNat

  handleList numbers

@[reducible, simp]
def maxSubarraySum_postcond (numbers : List Int) (result: Int) (h_precond : maxSubarraySum_precond (numbers)) : Prop :=
  let subArraySums :=
    List.range (numbers.length + 1) |>.flatMap (fun start =>
      List.range (numbers.length - start + 1) |>.map (fun len =>
        numbers.drop start |>.take len |>.sum))
  subArraySums.contains result ∧ subArraySums.all (· ≤ result)


theorem take_append_of_le_length {α} (l₁ l₂ : List α) (n : Nat)
    (h : l₁.length ≤ n) :
    (l₁ ++ l₂).take n = l₁ ++ (l₂.take (n - l₁.length)):= by 
aesop


end tmp
import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def maxSubarraySumDivisibleByK_precond (arr : Array Int) (k : Int) : Prop :=
  k > 0

def maxSubarraySumDivisibleByK (arr : Array Int) (k : Int) : Int :=
  let n := arr.size
  if n = 0 || k = 0 then 0
  else
    let prefixSums := Id.run do
      let mut prefixSums := Array.mkArray (n + 1) 0
      for i in [0:n] do
        prefixSums := prefixSums.set! (i+1) (prefixSums[i]! + arr[i]!)
      prefixSums

    let minElem := Id.run do
      let mut minElem := arr[0]!
      for elem in arr do
        minElem := min minElem elem
      minElem
    let maxSum := Id.run do
      let mut maxSum := minElem - 1
      for len in List.range (n+1) do
        if len % k = 0 && len > 0 then
          for start in [0:(n - len + 1)] do
            let endIdx := start + len
            let subarraySum := prefixSums[endIdx]! - prefixSums[start]!
            maxSum := max maxSum subarraySum
      maxSum

    let default : Int := minElem - 1
    if maxSum = default then 0 else maxSum

@[reducible]
def maxSubarraySumDivisibleByK_postcond (arr : Array Int) (k : Int) (result: Int) : Prop :=
  let subarrays := List.range (arr.size) |>.flatMap (fun start =>
    List.range (arr.size - start + 1) |>.map (fun len => arr.extract start (start + len)))
  let divisibleSubarrays := subarrays.filter (fun subarray => subarray.size % k = 0 && subarray.size > 0)
  let subarraySums := divisibleSubarrays.map (fun subarray => subarray.sum)
  (result = 0 → subarraySums.length = 0) ∧
  (result ≠ 0 → result ∈ subarraySums ∧ subarraySums.all (fun sum => sum ≤ result))


theorem prefixSums_update (arr : Array Int) (i : Nat) (n : Nat)
    (h₁ : i < n) (h₂ : i + 1 < n + 1) :
    let pref := (Array.mkArray (n + 1) 0).set! (i+1) (arr[i]!)
    pref.size = n + 1:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp
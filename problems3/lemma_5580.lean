import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def rain_precond (heights : List (Int)) : Prop :=
  heights.all (fun h => h >= 0)

def rain (heights : List (Int)) (h_precond : rain_precond (heights)) : Int :=
  if heights.length < 3 then 0 else
    let n := heights.length

    let rec aux (left : Nat) (right : Nat) (leftMax : Int) (rightMax : Int) (water : Int) : Int :=
      if left >= right then
        water
      else if heights[left]! <= heights[right]! then
        let newLeftMax := max leftMax (heights[left]!)
        let newWater := water + max 0 (leftMax - heights[left]!)
        aux (left+1) right newLeftMax rightMax newWater
      else
        let newRightMax := max rightMax (heights[right]!)
        let newWater := water + max 0 (rightMax - heights[right]!)
        aux left (right-1) leftMax newRightMax newWater
      termination_by right - left
    aux 0 (n-1) (heights[0]!) (heights[n-1]!) 0

@[reducible]
def rain_postcond (heights : List (Int)) (result: Int) (h_precond : rain_precond (heights)) : Prop :=
  result >= 0 ∧
  if heights.length < 3 then result = 0 else
    result =
      let max_left_at := λ i =>
        let rec ml (j : Nat) (max_so_far : Int) : Int :=
          if j > i then max_so_far
          else ml (j+1) (max max_so_far (heights[j]!))
          termination_by i + 1 - j
        ml 0 0

      let max_right_at := λ i =>
        let rec mr (j : Nat) (max_so_far : Int) : Int :=
          if j >= heights.length then max_so_far
          else mr (j+1) (max max_so_far (heights[j]!))
          termination_by heights.length - j
        mr i 0

      let water_at := λ i =>
        max 0 (min (max_left_at i) (max_right_at i) - heights[i]!)

      let rec sum_water (i : Nat) (acc : Int) : Int :=
        if i >= heights.length then acc
        else sum_water (i+1) (acc + water_at i)
        termination_by heights.length - i

      sum_water 0 0


theorem rain_nonneg (heights : List Int) (h : rain_precond heights) :
    0 ≤ rain heights h:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp
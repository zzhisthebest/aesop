import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def trapRainWater_precond (height : List Nat) : Prop :=
  True

def trapRainWater (height : List Nat) (h_precond : trapRainWater_precond (height)) : Nat :=
  Id.run do
    let mut left := 0
    let mut right := height.length - 1
    let mut leftMax := 0
    let mut rightMax := 0
    let mut water := 0

    while left < right do
      let hLeft := height[left]!
      let hRight := height[right]!

      if hLeft < hRight then
        if hLeft >= leftMax then
          leftMax := hLeft
        else
          water := water + (leftMax - hLeft)
        left := left + 1
      else
        if hRight >= rightMax then
          rightMax := hRight
        else
          water := water + (rightMax - hRight)
        right := right - 1

    return water

@[reducible, simp]
def trapRainWater_postcond (height : List Nat) (result: Nat) (h_precond : trapRainWater_precond (height)) : Prop :=
  let waterAt := List.range height.length |>.map (fun i =>
    let lmax := List.take (i+1) height |>.foldl Nat.max 0
    let rmax := List.drop i height |>.foldl Nat.max 0
    Nat.min lmax rmax - height[i]!)

  result - (waterAt.foldl (· + ·) 0) = 0 ∧ (waterAt.foldl (· + ·) 0) ≤ result


theorem waterAt_nonneg (height : List Nat) (i : Nat) (hi : i < height.length) :
    0 ≤ Nat.min
          (List.take (i+1) height |>.foldl Nat.max 0)
          (List.drop i height |>.foldl Nat.max 0) - height[i]!:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp
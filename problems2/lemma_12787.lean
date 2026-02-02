import Codetic
set_option maxHeartbeats 0
namespace tmp
def isEven (n : Int) : Bool :=
  n % 2 = 0

@[reducible, simp]
def FindEvenNumbers_precond (arr : Array Int) : Prop :=
  True

def FindEvenNumbers (arr : Array Int) (h_precond : FindEvenNumbers_precond (arr)) : Array Int :=
  let rec loop (i : Nat) (acc : Array Int) : Array Int :=
    if i < arr.size then
      if isEven (arr.getD i 0) then
        loop (i + 1) (acc.push (arr.getD i 0))
      else
        loop (i + 1) acc
    else
      acc
  loop 0 (Array.mkEmpty 0)

@[reducible, simp]
def FindEvenNumbers_postcond (arr : Array Int) (result: Array Int) (h_precond : FindEvenNumbers_precond (arr)) :=
  result.all (fun x => isEven x && x ∈ arr) ∧
  List.Pairwise (fun (x, i) (y, j) => if i < j then arr.idxOf x ≤ arr.idxOf y else true) (result.toList.zipIdx)


theorem mem_push {a : Array Int} {x y : Int} (h : y ∈ a) :
    y ∈ a.push x:= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp
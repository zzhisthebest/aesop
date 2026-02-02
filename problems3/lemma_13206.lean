import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def insert_precond (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) : Prop :=
  l ≤ oline.size ∧
  p ≤ nl.size ∧
  atPos ≤ l

def insert (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (h_precond : insert_precond (oline) (l) (nl) (p) (atPos)) : Array Char :=
  let result := Array.mkArray (l + p) ' '

  let result := Array.foldl
    (fun acc i =>
      if i < atPos then acc.set! i (oline[i]!) else acc)
    result
    (Array.range l)

  let result := Array.foldl
    (fun acc i =>
      acc.set! (atPos + i) (nl[i]!))
    result
    (Array.range p)

  let result := Array.foldl
    (fun acc i =>
      if i >= atPos then acc.set! (i + p) (oline[i]!) else acc)
    result
    (Array.range l)

  result

@[reducible, simp]
def insert_postcond (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (result: Array Char) (h_precond : insert_precond (oline) (l) (nl) (p) (atPos)) :=
  result.size = l + p ∧
  (List.range p).all (fun i => result[atPos + i]! = nl[i]!) ∧
  (List.range atPos).all (fun i => result[i]! = oline[i]!) ∧
  (List.range (l - atPos)).all (fun i => result[atPos + p + i]! = oline[atPos + i]!)


theorem insert_suffix (oline : Array Char) (l : Nat) (nl : Array Char) (p atPos : Nat)
    (h : insert_precond oline l nl p atPos) :
    (List.range (l - atPos)).all
        (fun i => (insert oline l nl p atPos h)[atPos + p + i]! = oline[atPos + i]!):= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp
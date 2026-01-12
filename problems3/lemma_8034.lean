import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def arrayProduct_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size = b.size

def loop (a b : Array Int) (len : Nat) : Nat → Array Int → Array Int
  | i, c =>
    if i < len then
      let a_val := if i < a.size then a[i]! else 0
      let b_val := if i < b.size then b[i]! else 0
      let new_c := Array.set! c i (a_val * b_val)
      loop a b len (i+1) new_c
    else c

def arrayProduct (a : Array Int) (b : Array Int) (h_precond : arrayProduct_precond (a) (b)) : Array Int :=
  let len := a.size
  let c := Array.mkArray len 0
  loop a b len 0 c

@[reducible, simp]
def arrayProduct_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : arrayProduct_precond (a) (b)) :=
  (result.size = a.size) ∧ (∀ i, i < a.size → a[i]! * b[i]! = result[i]!)


theorem loop_correct
    (a b : Array Int) (len : Nat) (h_len : len = a.size)
    (h_pre : arrayProduct_precond a b) :
    (let c0 := Array.mkArray len 0
     let res := loop a b len 0 c0
     (res.size = len) ∧
     ∀ i, i < len → a[i]! * b[i]! = res[i]!):= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp
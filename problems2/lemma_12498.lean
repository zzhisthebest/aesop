import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def copy_precond (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) : Prop :=
  src.size ≥ sStart + len ∧
  dest.size ≥ dStart + len

def updateSegment : Array Int → Array Int → Nat → Nat → Nat → Array Int
  | r, src, sStart, dStart, 0 => r
  | r, src, sStart, dStart, n+1 =>
      let rNew := r.set! (dStart + n) (src[sStart + n]!)
      updateSegment rNew src sStart dStart n

def copy (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (h_precond : copy_precond (src) (sStart) (dest) (dStart) (len)) : Array Int :=
  if len = 0 then dest
  else
    let r := dest
    updateSegment r src sStart dStart len

@[reducible, simp]
def copy_postcond (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (result: Array Int) (h_precond : copy_precond (src) (sStart) (dest) (dStart) (len)) :=
  result.size = dest.size ∧
  (∀ i, i < dStart → result[i]! = dest[i]!) ∧
  (∀ i, dStart + len ≤ i → i < result.size → result[i]! = dest[i]!) ∧
  (∀ i, i < len → result[dStart + i]! = src[sStart + i]!)


theorem updateSegment_spec (r src : Array Int) (sStart dStart : Nat) (len : Nat)
    (h : copy_precond src sStart r dStart len) :
    (let res := updateSegment r src sStart dStart len;
      res.size = r.size ∧
      (∀ i, i < dStart → res[i]! = r[i]!) ∧
      (∀ i, dStart + len ≤ i → i < res.size → res[i]! = r[i]!) ∧
      (∀ i, i < len → res[dStart + i]! = src[sStart + i]!)):= by 
codetic(config:={enableGrind:=false,enableOmega:=false})


end tmp
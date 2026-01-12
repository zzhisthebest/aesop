module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_9566
public def isPrime_precond (n : Nat) : Prop :=
  n ≥ 2

public def isPrime (n : Nat) (h_precond : isPrime_precond (n)) : Bool :=
  let bound := n
  let rec check (i : Nat) (fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if i * i > n then true
    else if n % i = 0 then false
    else check (i + 1) (fuel - 1)
  check 2 bound

public def isPrime_postcond (n : Nat) (result: Bool) (h_precond : isPrime_precond (n)) :=
  (result → (List.range' 2 (n - 2)).all (fun k => n % k ≠ 0)) ∧
  (¬ result → (List.range' 2 (n - 2)).any (fun k => n % k = 0))


public theorem divisor_le_sqrt_exists
    (n d : Nat) (hpos : 2 ≤ d) (hle : d ≤ n-2) (hdiv : n % d = 0) :
    ∃ d' , 2 ≤ d' ∧ d' * d' ≤ n ∧ n % d' = 0:= by 
sorry


end tmp_lemma_9566
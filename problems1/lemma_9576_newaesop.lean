import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def isPrime_precond (n : Nat) : Prop :=
  n ≥ 2

def isPrime (n : Nat) (h_precond : isPrime_precond (n)) : Bool :=
  let bound := n
  let rec check (i : Nat) (fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if i * i > n then true
    else if n % i = 0 then false
    else check (i + 1) (fuel - 1)
  check 2 bound

@[reducible, simp]
def isPrime_postcond (n : Nat) (result: Bool) (h_precond : isPrime_precond (n)) :=
  (result → (List.range' 2 (n - 2)).all (fun k => n % k ≠ 0)) ∧
  (¬ result → (List.range' 2 (n - 2)).any (fun k => n % k = 0))


theorem not_dvd_of_no_small_divisor
    {n i k : Nat} (h₁ : n % i ≠ 0) (h₂ : i ≤ k) (h₃ : k ≤ n) :
    (∀ d, d < i → n % d ≠ 0) → n % k ≠ 0:= by 
  aesop?


end tmp
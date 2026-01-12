module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_9755
public def isDivisibleBy11_precond (n : Int) : Prop :=
  True

public def isDivisibleBy11 (n : Int) (h_precond : isDivisibleBy11_precond (n)) : Bool :=
  n % 11 == 0

public def isDivisibleBy11_postcond (n : Int) (result: Bool) (h_precond : isDivisibleBy11_precond (n)) :=
  (result → (∃ k : Int, n = 11 * k)) ∧ (¬ result → (∀ k : Int, ¬ n = 11 * k))


public theorem int_mod_eq_zero_mp {a b : Int} (h : b % a = 0) : ∃ k : Int, b = a * k:= by 
sorry


end tmp_lemma_9755
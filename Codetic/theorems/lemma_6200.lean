module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_6200
public def binaryToDecimal_precond (digits : List Nat) : Prop :=
  digits.all (fun d => d = 0 ∨ d = 1)

public def binaryToDecimal (digits : List Nat) (h_precond : binaryToDecimal_precond (digits)) : Nat :=
  let rec helper (digits : List Nat) : Nat :=
    match digits with
    | [] => 0
    | first :: rest => first * Nat.pow 2 rest.length + helper rest
  helper digits

public def binaryToDecimal_postcond (digits : List Nat) (result: Nat) (h_precond : binaryToDecimal_precond (digits)) : Prop :=
  result - List.foldl (λ acc bit => acc * 2 + bit) 0 digits = 0 ∧
  List.foldl (λ acc bit => acc * 2 + bit) 0 digits - result = 0


public theorem foldl_mul_add_pow (d : Nat) :
    ∀ ds : List Nat,
      d * Nat.pow 2 ds.length +
        List.foldl (fun acc bit => acc * 2 + bit) 0 ds =
        List.foldl (fun acc bit => acc * 2 + bit) d ds:= by 
sorry


end tmp_lemma_6200
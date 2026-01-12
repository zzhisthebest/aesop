module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_6204
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


public theorem foldl_cons_eq_general (l : List Nat) :
    ∀ a : Nat,
      a * 2 ^ l.length +
        List.foldl (fun acc bit => acc * 2 + bit) 0 l =
        List.foldl (fun acc bit => acc * 2 + bit) a l:= by 
sorry


end tmp_lemma_6204
import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def binaryToDecimal_precond (digits : List Nat) : Prop :=
  digits.all (fun d => d = 0 ∨ d = 1)

def binaryToDecimal (digits : List Nat) (h_precond : binaryToDecimal_precond (digits)) : Nat :=
  let rec helper (digits : List Nat) : Nat :=
    match digits with
    | [] => 0
    | first :: rest => first * Nat.pow 2 rest.length + helper rest
  helper digits

@[reducible]
def binaryToDecimal_postcond (digits : List Nat) (result: Nat) (h_precond : binaryToDecimal_precond (digits)) : Prop :=
  result - List.foldl (λ acc bit => acc * 2 + bit) 0 digits = 0 ∧
  List.foldl (λ acc bit => acc * 2 + bit) 0 digits - result = 0


theorem foldl_mul_pow_add (a : Nat) (xs : List Nat) :
    List.foldl (fun acc bit => acc * 2 + bit) a xs =
      a * Nat.pow 2 xs.length +
        List.foldl (fun acc bit => acc * 2 + bit) 0 xs:= by 
aesop


end tmp
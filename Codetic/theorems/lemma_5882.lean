module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_5882
public def runLengthEncode_precond (s : String) : Prop :=
  True

public def runLengthEncode (s : String) (h_precond : runLengthEncode_precond (s)) : List (Char × Nat) :=
  let chars := s.data

  let rec encodeAux (acc : List (Char × Nat)) (rest : List Char) : List (Char × Nat) :=
    match rest with
    | [] => acc.reverse
    | h :: t =>
      match acc with
      | (ch, count) :: accTail =>
        if ch = h then
          encodeAux ((ch, count + 1) :: accTail) t
        else
          encodeAux ((h, 1) :: (ch, count) :: accTail) t
      | [] =>
        encodeAux ([(h, 1)]) t

  let encoded := encodeAux [] chars
  encoded

public def decodeRLE (lst : List (Char × Nat)) : String :=
  match lst with
  | [] => ""
  | (ch, cnt) :: tail =>
    let repeated := String.mk (List.replicate cnt ch)
    repeated ++ decodeRLE tail

public def runLengthEncode_postcond (s : String) (result: List (Char × Nat)) (h_precond : runLengthEncode_precond (s)) : Prop :=
  (∀ pair ∈ result, pair.snd > 0) ∧
  (∀ i : Nat, i < result.length - 1 → (result[i]!).fst ≠ (result[i+1]!).fst) ∧
  decodeRLE result = s


public theorem String.mk_replicate_eq (c : Char) (k : Nat) :
    String.mk (List.replicate k c) = String.join (List.replicate k (String.mk [c])):= by 
sorry


end tmp_lemma_5882
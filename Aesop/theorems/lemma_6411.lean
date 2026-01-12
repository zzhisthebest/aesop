module
import Lean
set_option maxHeartbeats 0
namespace tmp_lemma_6411
public def countOnes (lst : List Char) : Nat :=
  lst.foldl (fun acc c => if c = '1' then acc + 1 else acc) 0

public def shortestBeautifulSubstring_precond (s : String) (k : Nat) : Prop :=
  s.toList.all (fun c => c = '0' ∨ c = '1')

public def listToString (lst : List Char) : String :=
  String.mk lst

public def isLexSmaller (a b : List Char) : Bool :=
  listToString a < listToString b

public def allSubstrings (s : List Char) : List (List Char) :=
  let n := s.length
  (List.range n).flatMap (fun i =>
    (List.range (n - i)).map (fun j =>
      s.drop i |>.take (j + 1)))

public def shortestBeautifulSubstring (s : String) (k : Nat) (h_precond : shortestBeautifulSubstring_precond (s) (k)) : String :=
  let chars := s.data
  let candidates := allSubstrings chars |>.filter (fun sub => countOnes sub = k)

  let compare (a b : List Char) : Bool :=
    a.length < b.length ∨ (a.length = b.length ∧ isLexSmaller a b)

  let best := candidates.foldl (fun acc cur =>
    match acc with
    | none => some cur
    | some best => if compare cur best then some cur else some best) none
  match best with
  | some b => listToString b
  | none => ""

public def shortestBeautifulSubstring_postcond (s : String) (k : Nat) (result: String) (h_precond : shortestBeautifulSubstring_precond (s) (k)) : Prop :=
  let chars := s.data
  let substrings := (List.range chars.length).flatMap (fun i =>
    (List.range (chars.length - i + 1)).map (fun len =>
      chars.drop i |>.take len))
  let isBeautiful := fun sub => countOnes sub = k
  let beautiful := substrings.filter (fun sub => isBeautiful sub)
  let targets := beautiful.map (·.asString) |>.filter (fun s => s ≠ "")
  (result = "" ∧ targets = []) ∨
  (result ∈ targets ∧
   ∀ r ∈ targets, r.length ≥ result.length ∨ (r.length = result.length ∧ result ≤ r))


public theorem foldl_some_minimal (l : List (List Char)) (hne : l ≠ []) :
    ∃ b ∈ l,
      (l.foldl
        (fun acc cur =>
          match acc with
          | none => some cur
          | some best => if (cur.length < best.length ∨
                           (cur.length = best.length ∧ isLexSmaller cur best))
                           then some cur else some best) none) = some b ∧
      ∀ c ∈ l, (c.length < b.length) ∨ (c.length = b.length ∧ isLexSmaller c b) → False:= by 
sorry


end tmp_lemma_6411
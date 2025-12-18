import Aesop
set_option trace.aesop true
set_option maxHeartbeats 0
namespace tmp

def allSubstrings (s : List Char) : List (List Char) :=
  let n := s.length
  (List.range n).flatMap (fun i =>
    (List.range (n - i)).map (fun j =>
      s.drop i |>.take (j + 1)))

theorem test_twice (s : List Char) :
    ∀ sub ∈ allSubstrings s, sub ≠ []:= by
  intro sub a
  aesop? (config := { useDefaultSimpSet := false })
  aesop? (config := { useDefaultSimpSet := false })

end tmp

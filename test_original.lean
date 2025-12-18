import Aesop
set_option maxHeartbeats 0
namespace tmp
def allSubstrings (s : List Char) : List (List Char) :=
  let n := s.length
  (List.range n).flatMap (fun i =>
    (List.range (n - i)).map (fun j =>
      s.drop i |>.take (j + 1)))

theorem allSubstrings_nonempty (s : List Char) :
    ∀ sub ∈ allSubstrings s, sub ≠ []:= by
  intro sub a
  aesop  -- 试试默认 aesop

end tmp

import Codetic
set_option trace.codetic.zzh_custom true
set_option maxHeartbeats 0
namespace tmp

def allSubstrings (s : List Char) : List (List Char) :=
  let n := s.length
  (List.range n).flatMap (fun i =>
    (List.range (n - i)).map (fun j =>
      s.drop i |>.take (j + 1)))

theorem test (s : List Char) :
    ∀ sub ∈ allSubstrings s, sub ≠ []:= by
  intro sub a
  trace "========== FIRST CALL =========="
  codetic (config := { useDefaultSimpSet := false })
  trace "========== SECOND CALL =========="
  codetic (config := { useDefaultSimpSet := false })

end tmp

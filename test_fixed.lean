import Aesop
set_option maxHeartbeats 0
namespace tmp

def allSubstrings (s : List Char) : List (List Char) :=
  let n := s.length
  (List.range n).flatMap (fun i =>
    (List.range (n - i)).map (fun j =>
      s.drop i |>.take (j + 1)))

-- 测试：只调用一次 aesop 
theorem test_once (s : List Char) :
    ∀ sub ∈ allSubstrings s, sub ≠ []:= by
  intro sub a
  aesop (config := { useDefaultSimpSet := false })

end tmp

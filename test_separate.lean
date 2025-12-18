import Aesop
set_option trace.aesop true
set_option maxHeartbeats 0
namespace tmp

def allSubstrings (s : List Char) : List (List Char) :=
  let n := s.length
  (List.range n).flatMap (fun i =>
    (List.range (n - i)).map (fun j =>
      s.drop i |>.take (j + 1)))

-- 第一次调用
theorem test1 (s : List Char) :
    ∀ sub ∈ allSubstrings s, sub ≠ []:= by
  intro sub a
  aesop? (config := { useDefaultSimpSet := false })
  sorry

-- 第二次调用（从第一次的状态开始）
theorem test2 (s : List Char) :
    ∀ sub ∈ allSubstrings s, sub ≠ []:= by
  intro sub a
  aesop? (config := { useDefaultSimpSet := false })
  -- 应用第一次的脚本
  simp_all only [allSubstrings, List.mem_flatMap, List.mem_map, ne_eq]
  obtain ⟨w, h⟩ := a
  obtain ⟨left, right⟩ := h
  obtain ⟨w_1, h⟩ := right
  obtain ⟨left_1, right⟩ := h
  subst right
  apply Aesop.BuiltinRules.not_intro
  intro a
  -- 第二次 aesop 从这里开始
  aesop? (config := { useDefaultSimpSet := false })

end tmp

import Aesop
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
  -- 模拟第一次调用的效果
  simp_all only [allSubstrings, List.mem_flatMap, List.mem_map, ne_eq]
  obtain ⟨w, h⟩ := a
  obtain ⟨left, right⟩ := h
  obtain ⟨w_1, h⟩ := right
  obtain ⟨left_1, right⟩ := h
  subst right
  apply Aesop.BuiltinRules.not_intro
  intro a
  -- 现在第二次 aesop 从这里开始
  trace "Goal after first aesop's work:"
  trace "{← getMainGoal >>= (·.getType)}"
  aesop (config := { useDefaultSimpSet := false })

end tmp

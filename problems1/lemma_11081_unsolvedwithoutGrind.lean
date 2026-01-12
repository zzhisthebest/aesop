import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def secondSmallest_precond (s : Array Int) : Prop :=
  s.size > 1

def minListHelper : List Int → Int
| [] => panic! "minListHelper: empty list"
| [_] => panic! "minListHelper: singleton list"
| a :: b :: [] => if a ≤ b then a else b
| a :: b :: c :: xs =>
    let m := minListHelper (b :: c :: xs)
    if a ≤ m then a else m

def minList (l : List Int) : Int :=
  minListHelper l

def secondSmallestAux (s : Array Int) (i minIdx secondIdx : Nat) : Int :=
  if i ≥ s.size then
    s[secondIdx]!
  else
    let x    := s[i]!
    let m    := s[minIdx]!
    let smin := s[secondIdx]!
    if x < m then
      secondSmallestAux s (i + 1) i minIdx
    else if x < smin then
      secondSmallestAux s (i + 1) minIdx i
    else
      secondSmallestAux s (i + 1) minIdx secondIdx
termination_by s.size - i

def secondSmallest (s : Array Int) (h_precond : secondSmallest_precond (s)) : Int :=
  let (minIdx, secondIdx) :=
    if s[1]! < s[0]! then (1, 0) else (0, 1)
  secondSmallestAux s 2 minIdx secondIdx

@[reducible, simp]
def secondSmallest_postcond (s : Array Int) (result: Int) (h_precond : secondSmallest_precond (s)) :=
  (∃ i, i < s.size ∧ s[i]! = result) ∧
  (∃ j, j < s.size ∧ s[j]! < result ∧
    ∀ k, k < s.size → s[k]! ≠ s[j]! → s[k]! ≥ result)


theorem aux_returns_array_elem
  (s : Array Int) (i minIdx secondIdx : Nat)
  (h_i : i ≤ s.size) (h_min : minIdx < s.size) (h_sec : secondIdx < s.size) :
    secondSmallestAux s i minIdx secondIdx ∈ s:= by
aesop?(config:={enableGrind:=false})
induction i, minIdx, secondIdx using tmp.secondSmallestAux.induct s
·
  unfold tmp.secondSmallestAux
  aesop?(config:={enableGrind:=false})

·
  unfold tmp.secondSmallestAux
  aesop?(config:={enableGrind:=false})

·
  unfold tmp.secondSmallestAux
  aesop?(config:={enableGrind:=false})

·
  unfold tmp.secondSmallestAux
  aesop?(config:={enableGrind:=false})


-- (Tactic.tacticSeq
--  (Tactic.tacticSeq1Indented
-- [(Tactic.induction
--   "induction"
--   [(Tactic.elimTarget [] `i) "," (Tactic.elimTarget [] `minIdx) "," (Tactic.elimTarget [] `secondIdx)]
--   ["using" (Term.app `tmp.secondSmallestAux.induct [`s])]
--   []
--   [])
--  []
--  (Lean.cdot
--   (Lean.cdotTk (patternIgnore (token.«· » "·")))
--   (Tactic.tacticSeq
--    (Tactic.tacticSeq1Indented
--     [(Tactic.unfold "unfold" [`tmp.secondSmallestAux] [])
--      []
--      (Tactic.simpAll
--       "simp_all"
--       (Tactic.optConfig [])
--       []
--       ["only"]
--       ["["
--        [(Tactic.simpLemma [] [] `ge_iff_le)
--         ","
--         (Tactic.simpLemma [(Tactic.simpPre "↓")] [] `reduceIte)
--         ","
--         (Tactic.simpLemma [] [] `getElem!_pos)
--         ","
--         (Tactic.simpLemma [] [] `Array.getElem_mem)]
--        "]"])])))
--  []
--  (Lean.cdot
--   (Lean.cdotTk (patternIgnore (token.«· » "·")))
--   (Tactic.tacticSeq
--    (Tactic.tacticSeq1Indented
--     [(Tactic.unfold "unfold" [`tmp.secondSmallestAux] [])
--      []
--      (Tactic.simpAll
--       "simp_all"
--       (Tactic.optConfig [])
--       []
--       []
--       ["[" [(Tactic.simpLemma [(Tactic.simpPre "↓")] [] `reduceIte) "," (Tactic.simpStar "*")] "]"])
--      []
--      (Tactic.simpAll
--       "simp_all"
--       (Tactic.optConfig [])
--       []
--       ["only"]
--       ["[" [(Tactic.simpLemma [(Tactic.simpPre "↓")] [] `reduceIte)] "]"])
--      []
--      (Tactic.apply "apply" `ih1._@.problems1.lemma_11081_unsolvedwithoutGrind.2594797396._hygCtx._hyg.69)
--      []
--      (Tactic.exact "exact" `h._@.problems1.lemma_11081_unsolvedwithoutGrind.2594797396._hygCtx._hyg.65)])))
--  []
--  (Lean.cdot
--   (Lean.cdotTk (patternIgnore (token.«· » "·")))
--   (Tactic.tacticSeq
--    (Tactic.tacticSeq1Indented
--     [(Tactic.unfold "unfold" [`tmp.secondSmallestAux] [])
--      []
--      (Tactic.simpAll
--       "simp_all"
--       (Tactic.optConfig [])
--       []
--       []
--       ["[" [(Tactic.simpLemma [(Tactic.simpPre "↓")] [] `reduceIte) "," (Tactic.simpStar "*")] "]"])
--      []
--      (Tactic.simpAll
--       "simp_all"
--       (Tactic.optConfig [])
--       []
--       ["only"]
--       ["[" [(Tactic.simpLemma [(Tactic.simpPre "↓")] [] `reduceIte)] "]"])
--      []
--      (Tactic.split "split" [] [])
--      []
--      (Tactic.«tacticNext_=>_»
--       "next"
--       [(Lean.binderIdent `i)
--        (Lean.binderIdent `minIdx)
--        (Lean.binderIdent `secondIdx)
--        (Lean.binderIdent `h)
--        (Lean.binderIdent `x)
--        (Lean.binderIdent `m)
--        (Lean.binderIdent `smin)
--        (Lean.binderIdent `h_1)
--        (Lean.binderIdent `h_2)
--        (Lean.binderIdent `h_3)
--        (Lean.binderIdent `ih1)
--        (Lean.binderIdent `h_4)]
--       "=>"
--       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.omega "omega" (Tactic.optConfig []))])))
--      []
--      (Tactic.«tacticNext_=>_»
--       "next"
--       [(Lean.binderIdent `i)
--        (Lean.binderIdent `minIdx)
--        (Lean.binderIdent `secondIdx)
--        (Lean.binderIdent `h)
--        (Lean.binderIdent `x)
--        (Lean.binderIdent `m)
--        (Lean.binderIdent `smin)
--        (Lean.binderIdent `h_1)
--        (Lean.binderIdent `h_2)
--        (Lean.binderIdent `h_3)
--        (Lean.binderIdent `ih1)
--        (Lean.binderIdent `h_4)]
--       "=>"
--       (Tactic.tacticSeq
--        (Tactic.tacticSeq1Indented
--         [(Tactic.simpAll
--           "simp_all"
--           (Tactic.optConfig [])
--           []
--           ["only"]
--           ["[" [(Tactic.simpLemma [] [] `Int.not_lt)] "]"])
--          []
--          (Tactic.apply "apply" `ih1)
--          []
--          (Tactic.exact "exact" `h_1)])))])))
--  []
--  (Lean.cdot
--   (Lean.cdotTk (patternIgnore (token.«· » "·")))
--   (Tactic.tacticSeq
--    (Tactic.tacticSeq1Indented
--     [(Tactic.unfold "unfold" [`tmp.secondSmallestAux] [])
--      []
--      (Tactic.simpAll "simp_all" (Tactic.optConfig []) [] [] ["[" [(Tactic.simpStar "*")] "]"])
--      []
--      (Tactic.simpAll
--       "simp_all"
--       (Tactic.optConfig [])
--       []
--       ["only"]
--       ["[" [(Tactic.simpLemma [(Tactic.simpPre "↓")] [] `reduceIte)] "]"])
--      []
--      (Tactic.split "split" [] [])
--      []
--      (Tactic.«tacticNext_=>_»
--       "next"
--       [(Lean.binderIdent `i)
--        (Lean.binderIdent `minIdx)
--        (Lean.binderIdent `secondIdx)
--        (Lean.binderIdent `h)
--        (Lean.binderIdent `x)
--        (Lean.binderIdent `m)
--        (Lean.binderIdent `smin)
--        (Lean.binderIdent `h_1)
--        (Lean.binderIdent `h_2)
--        (Lean.binderIdent `h_3)
--        (Lean.binderIdent `ih1)
--        (Lean.binderIdent `h_4)]
--       "=>"
--       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.omega "omega" (Tactic.optConfig []))])))
--      []
--      (Tactic.«tacticNext_=>_»
--       "next"
--       [(Lean.binderIdent `i)
--        (Lean.binderIdent `minIdx)
--        (Lean.binderIdent `secondIdx)
--        (Lean.binderIdent `h)
--        (Lean.binderIdent `x)
--        (Lean.binderIdent `m)
--        (Lean.binderIdent `smin)
--        (Lean.binderIdent `h_1)
--        (Lean.binderIdent `h_2)
--        (Lean.binderIdent `h_3)
--        (Lean.binderIdent `ih1)
--        (Lean.binderIdent `h_4)]
--       "=>"
--       (Tactic.tacticSeq
--        (Tactic.tacticSeq1Indented
--         [(Tactic.simpAll
--           "simp_all"
--           (Tactic.optConfig [])
--           []
--           ["only"]
--           ["[" [(Tactic.simpLemma [] [] `Int.not_lt)] "]"])
--          []
--          (Tactic.split "split" [] [])
--          []
--          (Tactic.«tacticNext_=>_»
--           "next"
--           [(Lean.binderIdent `h_4)]
--           "=>"
--           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.omega "omega" (Tactic.optConfig []))])))
--          []
--          (Tactic.«tacticNext_=>_»
--           "next"
--           [(Lean.binderIdent `h_4)]
--           "=>"
--           (Tactic.tacticSeq
--            (Tactic.tacticSeq1Indented
--             [(Tactic.simpAll
--               "simp_all"
--               (Tactic.optConfig [])
--               []
--               ["only"]
--               ["[" [(Tactic.simpLemma [] [] `Int.not_lt)] "]"])
--              []
--              (Tactic.apply "apply" `ih1)
--              []
--              (Tactic.exact "exact" `h_1)])))])))])))]))


end tmp

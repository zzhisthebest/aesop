/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

module
import Lean
import Aesop.Frontend.Attribute

attribute [simp]
Array.eraseIdx!
Int.mul_neg_of_neg_of_pos
Int.mul_comm
Array.all_iff_forall

-- attribute [aesop safe constructors cases] Array


--以下是为了替换grind
--Array的定理
attribute[simp]
Array.setIfInBounds
Array.getElem_push
Array.getElem?_push
Array.getElem!_eq_getD
Array.getElem_set_ne
Array.getElem?_set_ne
Array.getElem_eraseIdx_of_lt
Array.getElem?_eraseIdx_of_lt
Array.getElem_eraseIdx_of_ge
Array.getElem?_eraseIdx_of_ge
Array.all_push
Array.getElem_set_self
Array.getElem?_set_self
Array.getElem_append
Array.getElem?_append
namespace Array

@[simp]--相比于Array.getElem_set_ne，仅仅是把h从i≠j改成了j≠i。没办法,simp太笨。
public theorem getElem_set_ne_1 {xs : Array α} {i : Nat} (h' : i < xs.size) {v : α} {j : Nat}
    (pj : j < xs.size) (h : j ≠ i) :
    (xs.set i v)[j]'(by simp [*]) = xs[j] := by
  grind
@[simp]--相比于Array.getElem?_set_ne，仅仅是把h从i≠j改成了j≠i。没办法,simp太笨。
public theorem getElem?_set_ne_1 {xs : Array α} {i : Nat} (h : i < xs.size) {v : α} {j : Nat}
    (ne : j ≠ i) : (xs.set i v)[j]? = xs[j]? := by
  grind


end Array


--List的定理
attribute [simp]
List.count_cons
List.countP_cons
List.filter_cons
List.count_erase
List.length_eraseIdx
List.take_of_length_le
List.erase_of_not_mem
List.getElem?_append
List.getElem_append
List.eraseDups_cons
List.pairwise_cons
List.drop_take
List.range_succ--这个存疑
List.idxOf_eq_length
List.zipIdx_append
List.take_take
List.drop_drop
List.idxOf_append
List.nodup_iff_pairwise_ne

namespace List
@[simp]
public theorem get_take_eq (l : List α) (i n : Nat)
  (h : i < Nat.min l.length n) :
  (l.take n)[i]? = l[i]?:= by
  grind
@[simp]
public theorem pairwise_of_forall_eq
  {α : Type u} (c : α) (l : List α)
  (h : ∀ a ∈ l, a = c) :
  List.Pairwise (· = ·) l := by
  sorry
@[simp]
public theorem take_append_gen (l₁ l₂ : List α) (n : Nat) :
    (l₁ ++ l₂).take n = (l₁.take n) ++ (l₂.take (n - l₁.length)) := by
  sorry
-- 正确的 simp 方向：把 take/drop 往里推，把 reverse 往外拉
@[simp]
public theorem reverse_take_eq (l : List α) (n : Nat) :
    (List.reverse l).take n = (l.drop (l.length - n)).reverse := by
  sorry

@[simp]
public theorem reverse_drop_eq (l : List α) (n : Nat) :
    (List.reverse l).drop n = (l.take (l.length - n)).reverse := by
  sorry

@[simp]
public theorem length_filter_eq_countP {α} (p : α → Bool) (l : List α) :
    (l.filter p).length = l.countP p := by
  grind





end List

--下面是一些放什么namespace都不太合适的
@[simp]
public theorem or_not_self (P : Prop) : (P ∨ ¬P) = True :=by
  grind

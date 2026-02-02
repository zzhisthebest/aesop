/-
Copyright (c) 2022 Asta H. From. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asta H. From
-/

import Codetic

set_option codetic.check.script true
set_option codetic.check.script.steps true

--- Decidable

attribute [codetic unsafe [50% constructors, 50% cases]] Decidable
attribute [codetic safe apply] instDecidableAnd


--- Mem

attribute [codetic safe cases (cases_patterns := [List.Mem _ []])] List.Mem
attribute [codetic unsafe 50% constructors] List.Mem
attribute [codetic unsafe 50% cases (cases_patterns := [List.Mem _ (_ :: _)])] List.Mem

theorem Mem.map {x : α} {xs : List α} (f : α → β) (h : x ∈ xs) : f x ∈ xs.map f := by
  induction h <;> codetic

theorem Mem.split [DecidableEq α] {xs : List α} {v : α} (h : v ∈ xs)
  : ∃ l r, xs = l ++ v :: r := by
  induction xs
  case nil =>
    codetic
  case cons x xs ih =>
    have dec : Decidable (x = v) := inferInstance
    cases dec
    case isFalse no =>
      let ⟨l, r, eq⟩ : ∃ l r, xs = l ++ v :: r := by codetic
      rw [eq]
      exact ⟨x :: l, r, rfl⟩
    case isTrue yes =>
      rw [yes]
      exact ⟨[], xs, rfl⟩


--- All

@[codetic safe [constructors, cases (cases_patterns := [All _ [], All _ (_ :: _)])]]
inductive All (P : α → Prop) : List α → Prop
  | nil : All P []
  | cons {x xs} : P x → All P xs → All P (x :: xs)

namespace All

@[simp]
theorem split_cons (P : α → Prop) (x : α) (xs : List α)
  : All P (x :: xs) ↔ (P x ∧ All P xs) := by
  codetic

theorem mem (P : α → Prop) (xs : List α)
  : All P xs ↔ ∀ a : α, a ∈ xs → P a := by
  induction xs <;> codetic

theorem weaken (P Q : α → Prop) (wk : ∀ x, P x → Q x) (xs : List α) (h : All P xs)
  : All Q xs := by
  induction h <;> codetic

-- TODO: the trace.codetic.proof does not work here
theorem in_self (xs : List α) : All (· ∈ xs) xs := by
  induction xs <;> codetic (add unsafe apply weaken)

theorem map (P : β → Prop) (f : α → β) (xs : List α)
  : All P (xs.map f) ↔ All (fun x => P (f x)) xs := by
  induction xs <;> codetic

end All


--- Any

@[codetic safe cases (cases_patterns := [Any _ []]),
  codetic unsafe [50% constructors, 50% cases (cases_patterns := [Any _ (_ :: _ )])]]
inductive Any (P : α → Prop) : List α → Prop
  | here {x xs} : P x → Any P (x :: xs)
  | there {x xs} : Any P xs → Any P (x :: xs)

namespace Any

@[simp]
theorem cons (P : α → Prop) (x : α) (xs : List α)
  : Any P (x :: xs) ↔ (P x ∨ Any P xs) := by
  codetic

theorem mem (P : α → Prop) (xs : List α)
  : Any P xs ↔ ∃ a : α, P a ∧ a ∈ xs := by
  apply Iff.intro
  case mp =>
    intro AnyPxs
    induction AnyPxs <;> codetic
  case mpr =>
    intro ⟨a, Pa, Ea⟩
    induction Ea <;> codetic

theorem map (P : β → Prop) (f : α → β) (xs : List α)
  : Any P (xs.map f) ↔ Any (fun x => P (f x)) xs := by
  induction xs <;> codetic

instance instDecidablePred (P : α → Prop) [d : DecidablePred P]
  : DecidablePred (Any P) := by
  intro xs
  match xs with
  | [] => codetic
  | x :: xs =>
    have ih : Decidable (Any P xs) := instDecidablePred P xs
    cases d x <;> codetic

end Any


--- Common

@[simp]
def Common (xs ys : List α) : Prop :=
  Any (· ∈ ys) xs

namespace Common

theorem mem {xs ys : List α} (h : Common xs ys)
  : ∃ a : α, a ∈ xs ∧ a ∈ ys := by
  induction h <;> codetic

theorem sym {xs ys : List α} (h : Common xs ys)
  : Common ys xs := by
  have other : ∃ a, a ∈ ys ∧ a ∈ xs := Iff.mp (Any.mem (· ∈ ys) xs) h
  apply Iff.mpr (Any.mem (· ∈ xs) ys)
  codetic

instance instDecidable [DecidableEq α] (xs ys : List α)
  : Decidable (Common xs ys) := by
  apply Any.instDecidablePred

end Common


--- List Permutations

-- From https://github.com/agda/agda-stdlib/blob/master/src/Data/List/Relation/Binary/Permutation/Propositional.agda
@[codetic unsafe [50% constructors, 25% cases (cases_patterns := [Perm (_ :: _) (_ :: _ )])]]
inductive Perm : (xs ys : List α) → Prop
  | refl {xs} : Perm xs xs
  | prep {xs ys} x : Perm xs ys → Perm (x :: xs) (x :: ys)
  | swap {xs ys} x y : Perm xs ys → Perm (x :: y :: xs) (y :: x :: ys)
  | tran {xs ys zs} : Perm xs ys → Perm ys zs → Perm xs zs

infix:45 " ↭ " => Perm

namespace Perm

noncomputable section

def sym {xs ys : List α} (perm : xs ↭ ys)
  : ys ↭ xs := by
  induction perm <;> codetic

def shift (v : α) (xs ys : List α)
  : xs ++ v :: ys ↭ v :: xs ++ ys := by
  induction xs <;> codetic

def map {xs ys : List α} (f : α → β) (perm : xs ↭ ys)
  : xs.map f ↭ ys.map f := by
  induction perm <;> codetic

theorem all {xs ys : List α} (perm : xs ↭ ys) (P : α → Prop)
  : All P xs → All P ys := by
  induction perm <;> codetic

theorem any {xs ys : List α} (perm : xs ↭ ys) (P : α → Prop)
  : Any P xs → Any P ys := by
  induction perm <;> codetic

end

end Perm


--- Syntax

inductive Form (Φ : Type)
| pro : Φ → Form Φ
| fls : Form Φ
| imp (φ ψ : Form Φ) : Form Φ

prefix:80 "♩" => Form.pro
notation "⊥" => Form.fls
infixr:75 " ⇒ " => Form.imp


--- Semantics

@[simp]
def Val (i : Φ → Prop) : Form Φ → Prop
  | ♩n => i n
  | ⊥ => false
  | φ ⇒ ψ => Val i φ → Val i ψ

instance Val.instDecidable (i : Φ → Prop) [d : DecidablePred i] (φ : Form Φ)
  : Decidable (Val i φ) := by
  match φ with
  | ♩n => codetic
  | ⊥ => codetic
  | φ ⇒ ψ =>
    have ihφ : Decidable (Val i φ) := instDecidable i φ
    have ihψ : Decidable (Val i ψ) := instDecidable i ψ
    codetic

abbrev Valid (φ : Form Φ) : Prop := ∀ i, DecidablePred i → Val i φ

@[simp]
def SC (i : Φ → Prop) (Γ Δ : List (Form Φ)) : Prop :=
  All (Val i) Γ → Any (Val i) Δ

namespace SC

theorem all {i : Φ → Prop} {Γ Γ' Δ : List (Form Φ)} (perm : Γ' ↭ Γ) (h : SC i Γ Δ)
  : SC i Γ' Δ := by codetic (add unsafe apply Perm.all)

theorem any {i : Φ → Prop} {Γ Δ Δ' : List (Form Φ)} (perm : Δ ↭ Δ') (h : SC i Γ Δ)
  : SC i Γ Δ' := by codetic (add unsafe apply Perm.any)

end SC


--- Prover

@[simp]
def sum : List Nat → Nat
  | [] => 0
  | x :: xs => sum xs + x

@[simp]
def Cal (l r : List Φ) : (Γ Δ : List (Form Φ)) → Prop
  | [], [] => Common l r
  | ⊥ :: _, [] => true
  | Γ, ⊥ :: Δ => Cal l r Γ Δ
  | ♩n :: Γ, [] => Cal (n :: l) r Γ []
  | Γ, ♩n :: Δ => Cal l (n :: r) Γ Δ
  | φ ⇒ ψ :: Γ, [] => Cal l r Γ [φ] ∧ Cal l r (ψ :: Γ) []
  | Γ, φ ⇒ ψ :: Δ => Cal l r (φ :: Γ) (ψ :: Δ)
termination_by Γ Δ => sum (Γ.map sizeOf) + sum (Δ.map sizeOf)

instance Cal.instDecidable [DecidableEq Φ] (l r : List Φ) (Γ Δ : List (Form Φ))
  : Decidable (Cal l r Γ Δ) := by
  match Γ, Δ with
  | [], [] => unfold Cal; apply Common.instDecidable l r
  | ⊥ :: Γ, [] => codetic
  | Γ, ⊥ :: Δ =>
    have ih : Decidable (Cal l r Γ Δ) := instDecidable l r Γ Δ
    codetic
  | ♩n :: Γ, [] =>
    have ih : Decidable (Cal (n :: l) r Γ []) := instDecidable (n :: l) r Γ []
    codetic
  | Γ, ♩n :: Δ =>
    have ih : Decidable (Cal l (n :: r) Γ Δ) := instDecidable l (n :: r) Γ Δ
    codetic
  | φ ⇒ ψ :: Γ, [] =>
    have ih₁ : Decidable (Cal l r Γ [φ]) := instDecidable l r Γ [φ]
    have ih₂ : Decidable (Cal l r (ψ :: Γ) []) := instDecidable l r (ψ :: Γ) []
    codetic
  | Γ, φ ⇒ ψ :: Δ =>
    have ih : Decidable (Cal l r (φ :: Γ) (ψ :: Δ)) := instDecidable l r (φ :: Γ) (ψ :: Δ)
    codetic
termination_by sum (Γ.map sizeOf) + sum (Δ.map sizeOf)
decreasing_by all_goals simp_wf <;> simp +arith

abbrev Prove (φ : Form Φ) : Prop := Cal [] [] [] [φ]

example : Prove (⊥ ⇒ ♩0) := by simp
example : Prove (♩0 ⇒ ♩0) := by simp
example : Prove (♩0 ⇒ ♩1 ⇒ ♩0) := by simp
example : ¬ Prove (♩0 ⇒ ♩1) := by simp (config := {decide := true})


--- Soundness and Completeness

@[simp]
def SC' (i : Φ → Prop) (l r : List Φ) (Γ Δ : List (Form Φ)) : Prop :=
  SC i (Γ ++ l.map (♩·)) (Δ ++ r.map (♩·))

theorem Cal_sound_complete [DecidableEq Φ]
  (l r : List Φ) (Γ Δ : List (Form Φ))
  : Cal l r Γ Δ ↔ ∀ i : Φ → Prop, DecidablePred i → SC' i l r Γ Δ := by
  match Γ, Δ with
  | [], [] =>
    apply Iff.intro
    case mp =>
      intro h i _ A
      let ⟨a, al, ar⟩ : ∃ a, a ∈ l ∧ a ∈ r := by
        unfold Cal at h
        exact Common.mem h
      have ml : ♩a ∈ l.map (♩·) := Mem.map (♩·) al
      have Va : Val i (♩a) := Iff.mp (All.mem (Val i) (l.map (♩·))) A (♩a) ml
      have mr : ♩a ∈ r.map (♩·) := Mem.map (♩·) ar
      apply Iff.mpr (Any.mem (Val i) _) ⟨♩a, ⟨Va, mr⟩⟩
    case mpr =>
      intro h
      let i a := a ∈ l
      have dec : DecidablePred i := inferInstance
      have h' : All (Val i) (l.map (♩·)) → Any (Val i) (r.map (♩·)) := h i dec
      have All_l : All (Val i) (l.map (♩·)) := Iff.mpr (All.map (Val i) (♩·) l) (All.in_self l)
      have Any_r : Any (Val (· ∈ l)) (r.map (♩·)) := h' All_l
      have Any_r' : Any (fun n => Val (· ∈ l) (♩n)) r := Iff.mp (Any.map (Val i) (♩·) r) Any_r
      unfold Cal
      apply Common.sym Any_r'
  | ⊥ :: Γ, [] =>
    simp
  | Γ, ⊥ :: Δ =>
    have ih : Cal l r Γ Δ ↔ ∀ i, DecidablePred i → SC' i l r Γ Δ :=
      Cal_sound_complete l r Γ Δ
    codetic
  | ♩n :: Γ, [] =>
    have ih : Cal (n :: l) r Γ [] ↔ ∀ i, DecidablePred i → SC' i (n :: l) r Γ [] :=
      Cal_sound_complete (n :: l) r Γ []
    have perm : (Γ ++ ♩n :: l.map (♩·)) ↭ (♩n :: Γ ++ l.map (♩·)) := Perm.shift (♩n) Γ _
    apply Iff.intro
    case mp =>
      intro h i dec
      unfold Cal at h
      have ihr : SC' i (n :: l) r Γ [] := Iff.mp ih h i dec
      apply SC.all (Perm.sym perm) ihr
    case mpr =>
      intro h
      have hSC : ∀ i, DecidablePred i → SC' i (n :: l) r Γ [] := by
        intro i dec
        apply SC.all perm (h i dec)
      unfold Cal
      apply Iff.mpr ih hSC
  | Γ, ♩n :: Δ =>
    have ih : Cal l (n :: r) Γ Δ ↔ ∀ i, DecidablePred i → SC' i l (n :: r) Γ Δ :=
      Cal_sound_complete l (n :: r) Γ Δ
    have perm : (Δ ++ ♩n :: r.map (♩·)) ↭ (♩n :: Δ ++ r.map (♩·)) := Perm.shift (♩n) Δ _
    apply Iff.intro
    case mp =>
      intro h i dec
      simp at h
      have ihr : SC' i l (n :: r) Γ Δ := Iff.mp ih h i dec
      apply SC.any perm ihr
    case mpr =>
      intro h
      have hSC : ∀ i, DecidablePred i → SC' i l (n :: r) Γ Δ := by
        intro i dec
        apply SC.any (Perm.sym perm) (h i dec)
      simp [Iff.mpr ih hSC]
  | φ ⇒ ψ :: Γ, [] =>
    have ih₁ : Cal l r Γ [φ] ↔ ∀ i, DecidablePred i → SC' i l r Γ [φ] :=
      Cal_sound_complete l r Γ [φ]
    have ih₂ : Cal l r (ψ :: Γ) [] ↔ ∀ i, DecidablePred i → SC' i l r (ψ :: Γ) [] :=
      Cal_sound_complete l r (ψ :: Γ) []
    apply Iff.intro
    case mp =>
      intro h i dec
      simp at h
      have ih₁' : SC' i l r Γ [φ] := Iff.mp ih₁ h.left i dec
      cases (Val.instDecidable i φ) <;> simp_all
    case mpr =>
      intro h
      simp
      apply And.intro
      case left =>
        apply Iff.mpr ih₁
        intro i dec
        cases (Val.instDecidable i φ) <;> simp_all
      case right =>
        apply Iff.mpr ih₂
        intro i dec
        cases (Val.instDecidable i φ) <;> simp_all
  | Γ, φ ⇒ ψ :: Δ =>
    have ih : Cal l r (φ :: Γ) (ψ :: Δ) ↔ ∀ i, DecidablePred i →
      SC' i l r (φ :: Γ) (ψ :: Δ) :=
      Cal_sound_complete l r (φ :: Γ) (ψ :: Δ)
    apply Iff.intro
    case mp =>
      intro h i dec
      cases (Val.instDecidable i φ) <;> simp_all
    case mpr =>
      intro h
      simp
      apply Iff.mpr ih
      intro i dec
      cases (Val.instDecidable i φ)
      case isFalse no =>
        simp_all
      case isTrue yes =>
        intro AllφΓ
        have AllΓ : All (Val i) (Γ ++ l.map (♩·)) := by simp_all
        have AnyφψΔ : Any (Val i) (φ ⇒ ψ :: Δ ++ r.map (♩·)) := h i dec AllΓ
        simp_all
termination_by sum (Γ.map sizeOf) + sum (Δ.map sizeOf)
decreasing_by all_goals simp_wf <;> simp +arith

theorem Prove_sound_complete [DecidableEq Φ] (φ : Form Φ)
  : Prove φ ↔ Valid φ := by
  have h : Prove φ ↔ ∀ i : Φ → Prop, DecidablePred i → SC' i [] [] [] [φ]  :=
    Cal_sound_complete [] [] [] [φ]
  apply Iff.intro
  case mp =>
    intro Pφ i dec
    have h' : Any (Val i) (φ :: [].map (♩·)) := Iff.mp h Pφ i dec All.nil
    codetic
  case mpr =>
    codetic (add simp Valid)


--- Proof System

inductive Proof : (Γ Δ : List (Form Φ)) → Prop
  | basic Γ Δ n : Proof (♩n :: Γ) (♩n :: Δ)
  | fls_l Γ Δ : Proof (⊥ :: Γ) Δ
  | imp_l Γ Δ φ ψ : Proof Γ (φ :: Δ) → Proof (ψ :: Γ) Δ → Proof (φ ⇒ ψ :: Γ) Δ
  | imp_r Γ Δ φ ψ: Proof (φ :: Γ) (ψ :: Δ) → Proof Γ (φ ⇒ ψ :: Δ)
  | per_l Γ Γ' Δ : Proof Γ Δ → Γ' ↭ Γ → Proof Γ' Δ
  | per_r Γ Δ Δ' : Proof Γ Δ → Δ ↭ Δ' → Proof Γ Δ'

attribute [codetic safe apply] Proof.basic Proof.fls_l
attribute [codetic unsafe 50% apply] Proof.imp_l Proof.imp_r
attribute [codetic unsafe 20% apply] Proof.per_l Proof.per_r

namespace Proof

theorem weaken (Γ Δ : List (Form Φ)) (prf : Proof Γ Δ) (δ : Form Φ)
  : Proof Γ (δ :: Δ) := by
  induction prf with
  | imp_r Γ Δ φ ψ =>
    have ih' : Proof (φ :: Γ) (ψ :: δ :: Δ) := by codetic
    codetic
  | _ => codetic (config := { maxRuleApplications := 250 })


--- Soundness

theorem sound (i : Φ → Prop) [DecidablePred i] (prf : Proof Γ Δ) : SC i Γ Δ := by
  induction prf with
  | imp_r Γ Δ φ ψ _ ih =>
    have d : Decidable (Val i φ) := inferInstance
    codetic
  | _ => codetic (add unsafe apply [Perm.all, Perm.any])

end Proof

@[simp]
def Proof' (l r : List Φ) (Γ Δ : List (Form Φ)) : Prop :=
  Proof (Γ ++ l.map (♩·)) (Δ ++ r.map (♩·))

theorem Cal_Proof [DecidableEq Φ]
  (l r : List Φ) (Γ Δ : List (Form Φ)) (h : Cal l r Γ Δ)
  : Proof' l r Γ Δ := by
  match Γ, Δ with
  | [], [] =>
    let ⟨a, al, ar⟩ : ∃ a, a ∈ l ∧ a ∈ r := by
      unfold Cal at h
      exact Common.mem h
    let ⟨ll, lr, leq⟩ : ∃ ll lr, l = ll ++ a :: lr := Mem.split al
    let ⟨rl, rr, req⟩ : ∃ rl rr, r = rl ++ a :: rr := Mem.split ar
    rw [leq, req]
    have p : Proof' (a :: ll ++ lr) (a :: rl ++ rr) [] [] := by apply Proof.basic
    have p' : Proof' (ll ++ a :: lr) (a :: rl ++ rr) [] [] := by
      codetic (add unsafe apply [Perm.map, Perm.shift])
    codetic (add unsafe apply [Perm.map, Perm.shift, Perm.sym])
  | ⊥ :: Γ, [] =>
    codetic
  | Γ, ⊥ :: Δ =>
    simp at h
    have ih : Proof' l r Γ Δ := Cal_Proof l r Γ Δ h
    apply Proof.weaken _ _ ih ⊥
  | ♩n :: Γ, [] =>
    unfold Cal at h
    have ih : Proof' (n :: l) r Γ [] := Cal_Proof (n :: l) r Γ [] h
    apply Proof.per_l _ _ _ ih
    codetic (add unsafe apply [Perm.shift, Perm.sym])
  | Γ, ♩n :: Δ =>
    simp at h
    have ih : Proof' l (n :: r) Γ Δ := Cal_Proof l (n :: r) Γ Δ h
    codetic (add unsafe apply [Perm.shift])
  | φ ⇒ ψ :: Γ, [] =>
    simp at h
    have ih₁ : Proof' l r Γ [φ] := Cal_Proof l r Γ [φ] h.left
    have ih₂ : Proof' l r (ψ :: Γ) [] := Cal_Proof l r (ψ :: Γ) [] h.right
    codetic
  | Γ, φ ⇒ ψ :: Δ =>
    simp at h
    have ih : Proof' l r (φ :: Γ) (ψ :: Δ) := Cal_Proof l r (φ :: Γ) (ψ :: Δ) h
    codetic
termination_by sum (Γ.map sizeOf) + sum (Δ.map sizeOf)
decreasing_by all_goals simp_wf <;> simp +arith

theorem Proof_sound_complete [DecidableEq Φ] (φ : Form Φ)
  : Proof [] [φ] ↔ Valid φ := by
  apply Iff.intro
  case mp =>
    intro prf i dec
    have h : Any (Val i) [φ] := Proof.sound i prf All.nil
    codetic
  case mpr =>
    intro h
    have c : Prove φ := Iff.mpr (Prove_sound_complete φ) h
    have prf : Proof' [] [] [] [φ] := Cal_Proof [] [] [] [φ] c
    exact prf

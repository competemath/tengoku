/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.RingTheory.LocalRing.ResidueField.Basic
import Tengoku.Seed.RingTheory.Artinian.Module
import Tengoku.Seed.RingTheory.Noetherian.Defs
import Tengoku.Seed.RingTheory.Length

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Brick G2XSK1: determinants of finite length modules and of (2,1)-periodic complexes

Stacks Project, Chow Homology, Appendix A (§42.68.1 "Determinants of finite length modules",
§42.68.12 "Periodic complexes and determinants"); this is brick K1 of the Stacks route to the
key lemma (Fulton 2.4 with common components, see `notes/agents/G2TEXC-status.md`).

Let `(A, 𝔪, κ)` be a local ring and `M` an `A`-module of finite length
(`[IsArtinian A M] [IsNoetherian A M]`).  We never form quotient modules: every module of the
theory is a *subquotient* `T/P` of an ambient module, i.e. an interval `P ≤ T` of `Submodule A M`;
modules in different ambients are compared along linear maps (`ratio_map`, `perDet_map`).

## Determinant lines
* `Adm P T l`: `l : List M` is a Stacks *admissible* sequence of `T/P` (`𝔪 e_i ⊆ ⟨e_<i⟩`) which is
  moreover strict (`e_i ∉ ⟨e_<i⟩`) and generating, i.e. a nonzero symbol `[e_1, …, e_l]`.
* `IsVol P T c`: `c : List M → κ` satisfies Stacks' relations (b) (rescaling an entry by a unit
  modulo the previous ones) and (c) (adjacent transposition, sign `-1`): the `κ`-linear forms on
  Stacks' `det_κ(T/P)`.
* `vol_unique` (Stacks 42.68.3) and `exists_vol` (42.68.5, by removing a socle element as in
  Stacks' proof): the volumes form a line; `ratio P T l l' ∈ κ^*` is `[l]/[l']` in `det_κ(T/P)`.
* `ratio_append` (42.68.6, short exact sequences `0 → S/P → T/P → T/S → 0`), `ratio_move_block`
  (sign of a block transposition), `ratio_smul_unit` (42.68.10), `ratio_map` (functoriality),
  `Adm.moduleLength_eq` (lists have length `Module.length`).

## Periodic complexes
* `PerExact P T φ ψ`: `(T/P, φ, ψ)` is an exact `(2,1)`-periodic complex.
* `perDet P T φ ψ ∈ κ^*` (Definition 42.68.13) and `perDet_eq` (Remark 42.68.14 for *every*
  choice of lifts).
* `perDet_mul_perDet_symm` (42.68.15), `perDet_self` (42.68.16), `perDet_zero_right`,
  `perDet_zero_left`, `perDet_unit_zero` (42.68.17 + 42.68.10), `perDet_mul` (42.68.18),
  `perDet_comp` (42.68.24), `perDet_map`/`perDet_equiv` (isomorphism invariance),
  `perDet_eq_of_boundary` (42.68.25 in the case of equal boundary maps, as used in 42.68.35).

Symbols `d_M(a, b) = det_κ(M/abM, a, b)` and the tame symbol are brick K2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v

namespace FinLenDet

open IsLocalRing Submodule

variable {A : Type u} [CommRing A] [IsLocalRing A] {M : Type v} [AddCommGroup M] [Module A M]

/-! ### Spans of lists -/

variable (A) in
/-- The submodule spanned by the entries of a list.-/
def lspan (l : List M) : Submodule A M := span A {y | y ∈ l}

@[simp] lemma lspan_nil : lspan A ([] : List M) = ⊥ := by
  simp [lspan]

@[simp] lemma lspan_cons (v : M) (l : List M) : lspan A (v :: l) = A ∙ v ⊔ lspan A l := by
  simp only [lspan, List.mem_cons]
  rw [← span_insert]
  rfl

@[simp] lemma lspan_append (l₁ l₂ : List M) : lspan A (l₁ ++ l₂) = lspan A l₁ ⊔ lspan A l₂ := by
  simp only [lspan, List.mem_append]
  rw [← span_union]
  rfl

lemma mem_lspan {v : M} {l : List M} (h : v ∈ l) : v ∈ lspan A l :=
  subset_span h

lemma sup_lspan_cons (P : Submodule A M) (v : M) (l : List M) :
    P ⊔ lspan A (v :: l) = P ⊔ A ∙ v ⊔ lspan A l := by
  rw [lspan_cons, sup_assoc]

lemma sup_lspan_append (P : Submodule A M) (l₁ l₂ : List M) :
    P ⊔ lspan A (l₁ ++ l₂) = P ⊔ lspan A l₁ ⊔ lspan A l₂ := by
  rw [lspan_append, sup_assoc]

lemma sup_lspan_snoc (P : Submodule A M) (l : List M) (v : M) :
    P ⊔ lspan A (l ++ [v]) = P ⊔ lspan A l ⊔ A ∙ v := by
  rw [sup_lspan_append, lspan_cons, lspan_nil, sup_bot_eq]

/-! ### Elements killed by `𝔪` modulo a submodule -/

/-- `𝔪 • v ⊆ P`.-/
def MKill (P : Submodule A M) (v : M) : Prop := ∀ r ∈ maximalIdeal A, r • v ∈ P

lemma MKill.mono {P Q : Submodule A M} {v : M} (h : MKill P v) (hPQ : P ≤ Q) : MKill Q v :=
  fun r hr => hPQ (h r hr)

/-- If `𝔪 v ⊆ P` and `w ∈ P ⊔ A v`, `w ∉ P`, then `w ≡ a v` modulo `P` with `a` a unit.-/
lemma exists_unit_of_mem_sup {P : Submodule A M} {v w : M} (hv : MKill P v)
    (hw : w ∈ P ⊔ A ∙ v) (hwP : w ∉ P) : ∃ a : A, IsUnit a ∧ w - a • v ∈ P := by
  obtain ⟨p, hp, z, hz, rfl⟩ := mem_sup.1 hw
  obtain ⟨a, rfl⟩ := mem_span_singleton.1 hz
  refine ⟨a, ?_, by simpa using hp⟩
  by_contra ha
  exact hwP (P.add_mem hp (hv a (not_not.1 (notMem_maximalIdeal.not.2 ha))))

/-- Covering: if `𝔪 v ⊆ P` and `w ∈ (P ⊔ A v) \ P` then `P ⊔ A w = P ⊔ A v`.-/
lemma sup_span_eq_of_mem {P : Submodule A M} {v w : M} (hv : MKill P v)
    (hw : w ∈ P ⊔ A ∙ v) (hwP : w ∉ P) : P ⊔ A ∙ w = P ⊔ A ∙ v := by
  obtain ⟨a, ha, h⟩ := exists_unit_of_mem_sup hv hw hwP
  refine le_antisymm (sup_le le_sup_left ((span_singleton_le_iff_mem _ _).2 hw)) ?_
  refine sup_le le_sup_left ((span_singleton_le_iff_mem _ _).2 ?_)
  obtain ⟨b, hb⟩ := ha.exists_left_inv
  have : v = b • w - b • (w - a • v) := by
    rw [smul_sub, sub_sub_cancel, smul_smul, hb, one_smul]
  rw [this]
  exact sub_mem (smul_mem _ _ (mem_sup_right (mem_span_singleton_self w)))
    (smul_mem _ _ (mem_sup_left h))

/-! ### Admissible lists -/

/-- `Adm P T l`: `l` is an admissible, strict, generating sequence of the subquotient `T/P`
(a nonzero symbol of Stacks' `det_κ(T/P)`).-/
def Adm : Submodule A M → Submodule A M → List M → Prop
  | P, T, [] => P = T
  | P, T, v :: l => v ∈ T ∧ v ∉ P ∧ MKill P v ∧ Adm (P ⊔ A ∙ v) T l

@[simp] lemma adm_nil {P T : Submodule A M} : Adm P T [] ↔ P = T := Iff.rfl

@[simp] lemma adm_cons {P T : Submodule A M} {v : M} {l : List M} :
    Adm P T (v :: l) ↔ v ∈ T ∧ v ∉ P ∧ MKill P v ∧ Adm (P ⊔ A ∙ v) T l := Iff.rfl

lemma Adm.le {T : Submodule A M} {l : List M} : ∀ {P : Submodule A M}, Adm P T l → P ≤ T := by
  induction l with
  | nil => intro P h; exact le_of_eq (show P = T from h)
  | cons v l ih => intro P h; exact le_sup_left.trans (ih h.2.2.2)

lemma Adm.sup_lspan {T : Submodule A M} {l : List M} :
    ∀ {P : Submodule A M}, Adm P T l → P ⊔ lspan A l = T := by
  induction l with
  | nil => intro P h; simpa using h
  | cons v l ih => intro P h; rw [sup_lspan_cons]; exact ih h.2.2.2

lemma Adm.mem {T : Submodule A M} {l : List M} :
    ∀ {P : Submodule A M}, Adm P T l → ∀ v ∈ l, v ∈ T := by
  induction l with
  | nil => intro P _; simp
  | cons w l ih =>
    intro P h v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · exact h.1
    · exact ih h.2.2.2 v hv

lemma adm_append_left {T : Submodule A M} {l₁ l₂ : List M} :
    ∀ {P : Submodule A M}, Adm P T (l₁ ++ l₂) → Adm P (P ⊔ lspan A l₁) l₁ := by
  induction l₁ with
  | nil => intro P _; simp
  | cons v l₁ ih =>
    intro P h
    refine ⟨mem_sup_right (mem_lspan (List.mem_cons_self ..)), h.2.1, h.2.2.1, ?_⟩
    rw [sup_lspan_cons]
    exact ih h.2.2.2

lemma adm_append_right {T : Submodule A M} {l₁ l₂ : List M} :
    ∀ {P : Submodule A M}, Adm P T (l₁ ++ l₂) → Adm (P ⊔ lspan A l₁) T l₂ := by
  induction l₁ with
  | nil => intro P h; simpa using h
  | cons v l₁ ih =>
    intro P h
    rw [sup_lspan_cons]
    exact ih h.2.2.2

lemma adm_append {S T : Submodule A M} {l₁ l₂ : List M} :
    ∀ {P : Submodule A M}, Adm P S l₁ → Adm S T l₂ → Adm P T (l₁ ++ l₂) := by
  induction l₁ with
  | nil => intro P h₁ h₂; simp only [adm_nil] at h₁; subst h₁; simpa using h₂
  | cons v l₁ ih =>
    intro P h₁ h₂
    exact ⟨(Adm.le h₂) h₁.1, h₁.2.1, h₁.2.2.1, ih h₁.2.2.2 h₂⟩

lemma adm_append_iff {P T : Submodule A M} {l₁ l₂ : List M} :
    Adm P T (l₁ ++ l₂) ↔ Adm P (P ⊔ lspan A l₁) l₁ ∧ Adm (P ⊔ lspan A l₁) T l₂ :=
  ⟨fun h => ⟨adm_append_left h, adm_append_right h⟩, fun h => adm_append h.1 h.2⟩

lemma Adm.eq_nil {T : Submodule A M} {l : List M} (h : Adm T T l) : l = [] := by
  cases l with
  | nil => rfl
  | cons v l => exact absurd h.1 h.2.1

/-- The middle entry of an admissible list.-/
lemma Adm.mid {P T : Submodule A M} {l₁ l₂ : List M} {v : M} (h : Adm P T (l₁ ++ v :: l₂)) :
    v ∈ T ∧ v ∉ P ⊔ lspan A l₁ ∧ MKill (P ⊔ lspan A l₁) v ∧
      Adm (P ⊔ lspan A l₁ ⊔ A ∙ v) T l₂ :=
  adm_append_right h

/-- Replacing an entry by another generator of the same step.-/
lemma Adm.replace {P T : Submodule A M} {l₁ l₂ : List M} {v w : M} (h : Adm P T (l₁ ++ v :: l₂))
    (hw : w ∈ P ⊔ lspan A l₁ ⊔ A ∙ v) (hwB : w ∉ P ⊔ lspan A l₁) (hwk : MKill (P ⊔ lspan A l₁) w) :
    Adm P T (l₁ ++ w :: l₂) := by
  obtain ⟨hvT, hvB, hvk, hrest⟩ := h.mid
  have heq := sup_span_eq_of_mem hvk hw hwB
  refine adm_append (adm_append_left h) ⟨?_, hwB, hwk, ?_⟩
  · exact (Adm.le hrest) (heq ▸ mem_sup_right (mem_span_singleton_self w))
  · rw [heq]; exact hrest

/-- Swapping two adjacent entries `u, v` when `𝔪 v` lies in the span before `u`.-/
lemma Adm.swap {P T : Submodule A M} {l₁ l₂ : List M} {u v : M}
    (h : Adm P T (l₁ ++ u :: v :: l₂)) (hv : MKill (P ⊔ lspan A l₁) v) :
    Adm P T (l₁ ++ v :: u :: l₂) := by
  obtain ⟨huT, huB, huk, hv', hvB', hvk', hrest⟩ := h.mid
  set B := P ⊔ lspan A l₁
  have hvB : v ∉ B := fun hv => hvB' (mem_sup_left hv)
  have huB' : u ∉ B ⊔ A ∙ v := by
    intro hu
    have h1 := sup_span_eq_of_mem hv hu huB
    exact hvB' (h1 ▸ mem_sup_right (mem_span_singleton_self v))
  refine adm_append (adm_append_left h) ⟨hv', hvB, hv, huT, huB', huk.mono le_sup_left, ?_⟩
  rw [sup_right_comm]; exact hrest

/-! ### Splitting a list at the first entry that reaches a given element -/

lemma exists_split {P : Submodule A M} {g : M} :
    ∀ {l : List M}, g ∈ P ⊔ lspan A l → g ∉ P →
      ∃ l₁ x l₂, l = l₁ ++ x :: l₂ ∧ g ∉ P ⊔ lspan A l₁ ∧ g ∈ P ⊔ lspan A l₁ ⊔ A ∙ x
  | [], h, hg => by simp at h; exact absurd h hg
  | v :: l, h, hg => by
    by_cases hv : g ∈ P ⊔ A ∙ v
    · exact ⟨[], v, l, rfl, by simpa using hg, by simpa using hv⟩
    · rw [sup_lspan_cons] at h
      obtain ⟨l₁, x, l₂, rfl, h1, h2⟩ := exists_split (P := P ⊔ A ∙ v) h hv
      exact ⟨v :: l₁, x, l₂, rfl, by rwa [sup_lspan_cons], by rwa [sup_lspan_cons]⟩

lemma split_unique {g : M} {l₂ k₂ : List M} {x y : M} {l₁ : List M} :
    ∀ {P : Submodule A M} {k₁ : List M}, l₁ ++ x :: l₂ = k₁ ++ y :: k₂ →
    g ∉ P ⊔ lspan A l₁ → g ∈ P ⊔ lspan A l₁ ⊔ A ∙ x →
    g ∉ P ⊔ lspan A k₁ → g ∈ P ⊔ lspan A k₁ ⊔ A ∙ y → l₁ = k₁ ∧ x = y ∧ l₂ = k₂ := by
  induction l₁ with
  | nil =>
    intro P k₁ he h1 h2 h3 h4
    cases k₁ with
    | nil => simp_all
    | cons b k₁ =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      simp only [lspan_nil, sup_bot_eq] at h2
      exact absurd (by rw [sup_lspan_cons]; exact mem_sup_left h2) h3
  | cons a l₁ ih =>
    intro P k₁ he h1 h2 h3 h4
    cases k₁ with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      simp only [lspan_nil, sup_bot_eq] at h4
      exact absurd (by rw [sup_lspan_cons]; exact mem_sup_left h4) h1
    | cons b k₁ =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      rw [sup_lspan_cons] at h1 h2 h3 h4
      obtain ⟨rfl, rfl, rfl⟩ := ih he h1 h2 h3 h4
      exact ⟨rfl, rfl, rfl⟩

/-- Removing the step where a fixed element `f` with `𝔪 f ⊆ P` is reached.-/
lemma adm_erase {f : M} : ∀ {P T : Submodule A M} {l₁ l₂ : List M} {x : M},
    Adm P T (l₁ ++ x :: l₂) → MKill P f → f ∉ P ⊔ lspan A l₁ → f ∈ P ⊔ lspan A l₁ ⊔ A ∙ x →
    Adm (P ⊔ A ∙ f) T (l₁ ++ l₂)
  | P, T, [], l₂, x, h, hf, h1, h2 => by
    simp only [lspan_nil, sup_bot_eq, List.nil_append] at h h1 h2 ⊢
    rw [sup_span_eq_of_mem h.2.2.1 h2 h1]; exact h.2.2.2
  | P, T, a :: l₁, l₂, x, h, hf, h1, h2 => by
    rw [sup_lspan_cons] at h1 h2
    have ih := adm_erase h.2.2.2 (hf.mono le_sup_left) h1 h2
    refine ⟨h.1, ?_, h.2.2.1.mono le_sup_left, by rwa [sup_right_comm]⟩
    intro ha
    by_cases haP : a ∈ P
    · exact h.2.1 haP
    · have := sup_span_eq_of_mem hf ha haP
      have hfa : f ∈ P ⊔ A ∙ a := this ▸ mem_sup_right (mem_span_singleton_self f)
      exact h1 (mem_sup_left hfa)

/-- The span after the erased step.-/
lemma sup_lspan_erase {P : Submodule A M} {f x : M} {l₁ l₂ : List M}
    (hx : MKill (P ⊔ lspan A l₁) x) (h1 : f ∉ P ⊔ lspan A l₁)
    (h2 : f ∈ P ⊔ lspan A l₁ ⊔ A ∙ x) :
    P ⊔ lspan A (l₁ ++ x :: l₂) = P ⊔ A ∙ f ⊔ lspan A (l₁ ++ l₂) := by
  have := sup_span_eq_of_mem hx h2 h1
  rw [sup_lspan_append, sup_lspan_append, sup_lspan_cons, ← this]
  simp only [sup_assoc, sup_comm, sup_left_comm]

/-! ### Volumes (linear forms on `det_κ(T/P)`) -/

/-- `c` satisfies Stacks' admissible relations (b) and (c) on the admissible lists of `T/P`.-/
structure IsVol (P T : Submodule A M) (c : List M → ResidueField A) : Prop where
  /-- Stacks relation (b): rescaling an entry by `a` modulo the span of the previous ones.-/
  smul : ∀ (l₁ l₂ : List M) (v w x : M) (a : A), Adm P T (l₁ ++ v :: l₂) →
    Adm P T (l₁ ++ w :: l₂) → x ∈ P ⊔ lspan A l₁ → v = a • w + x →
    c (l₁ ++ v :: l₂) = residue A a * c (l₁ ++ w :: l₂)
  /-- Stacks relation (c): an admissible adjacent transposition changes the sign.-/
  swap : ∀ (l₁ l₂ : List M) (u v : M), Adm P T (l₁ ++ u :: v :: l₂) →
    Adm P T (l₁ ++ v :: u :: l₂) → c (l₁ ++ u :: v :: l₂) = - c (l₁ ++ v :: u :: l₂)

lemma IsVol.prefix {P S T : Submodule A M} {c : List M → ResidueField A} (hc : IsVol P T c)
    {l₀ : List M} (h₀ : Adm P S l₀) : IsVol S T (fun l => c (l₀ ++ l)) where
  smul l₁ l₂ v w x a h h' hx he := by
    have hS := h₀.sup_lspan
    have := hc.smul (l₀ ++ l₁) l₂ v w x a (by rw [List.append_assoc]; exact adm_append h₀ h)
      (by rw [List.append_assoc]; exact adm_append h₀ h') (by rw [sup_lspan_append, hS]; exact hx) he
    simpa only [List.append_assoc] using this
  swap l₁ l₂ u v h h' := by
    have := hc.swap (l₀ ++ l₁) l₂ u v (by rw [List.append_assoc]; exact adm_append h₀ h)
      (by rw [List.append_assoc]; exact adm_append h₀ h')
    simpa only [List.append_assoc] using this

lemma IsVol.suffix {P S T : Submodule A M} {c : List M → ResidueField A} (hc : IsVol P T c)
    {l₀ : List M} (h₀ : Adm S T l₀) : IsVol P S (fun l => c (l ++ l₀)) where
  smul l₁ l₂ v w x a h h' hx he := by
    have := hc.smul l₁ (l₂ ++ l₀) v w x a
      (by have := adm_append h h₀; simpa only [List.append_assoc, List.cons_append] using this)
      (by have := adm_append h' h₀; simpa only [List.append_assoc, List.cons_append] using this) hx he
    simpa only [List.append_assoc, List.cons_append] using this
  swap l₁ l₂ u v h h' := by
    have := hc.swap l₁ (l₂ ++ l₀) u v
      (by have := adm_append h h₀; simpa only [List.append_assoc, List.cons_append] using this)
      (by have := adm_append h' h₀; simpa only [List.append_assoc, List.cons_append] using this)
    simpa only [List.append_assoc, List.cons_append] using this

/-- Moving an entry `g` with `𝔪 g ⊆ P` to the front costs the sign `(-1)^{#passed}`.-/
lemma move_front {P T : Submodule A M} {g : M} (hg : MKill P g) (l₁ : List M) :
    ∀ {l₂ : List M}, Adm P T (l₁ ++ g :: l₂) → Adm P T (g :: (l₁ ++ l₂)) ∧
      ∀ c, IsVol P T c → c (l₁ ++ g :: l₂) = (-1) ^ l₁.length * c (g :: (l₁ ++ l₂)) := by
  induction l₁ using List.reverseRecOn with
  | nil => intro l₂ h; simpa using h
  | append_singleton l₀ y ih =>
    intro l₂ h
    rw [List.append_assoc, List.singleton_append] at h
    have h' : Adm P T (l₀ ++ g :: y :: l₂) := h.swap (hg.mono le_sup_left)
    obtain ⟨h1, h2⟩ := ih h'
    refine ⟨by simpa using h1, fun c hc => ?_⟩
    rw [List.append_assoc, List.singleton_append, hc.swap _ _ _ _ h h', h2 c hc]
    simp [pow_succ]

/-- **Stacks 42.68.3** (`dim det_κ ≤ 1`), in dual form, together with invariance of the length.-/
theorem vol_unique {T : Submodule A M} {l' : List M} :
    ∀ {l : List M} {P : Submodule A M}, Adm P T l → Adm P T l' →
      ∃ μ : ResidueField A, (∀ c, IsVol P T c → c l = μ * c l') ∧ l.length = l'.length := by
  induction l' with
  | nil =>
    intro l P hl hl'
    simp only [adm_nil] at hl'
    subst hl'
    obtain rfl := hl.eq_nil
    exact ⟨1, fun c _ => by simp, rfl⟩
  | cons g k' ih =>
    intro l P hl hl'
    obtain ⟨hgT, hgP, hg, hk'⟩ := hl'
    have hgl : g ∈ P ⊔ lspan A l := hl.sup_lspan ▸ hgT
    obtain ⟨l₁, x, l₂, rfl, h1, h2⟩ := exists_split hgl hgP
    obtain ⟨-, hxB, hxk, -⟩ := hl.mid
    have heq := sup_span_eq_of_mem hxk h2 h1
    have hxg : x ∈ P ⊔ lspan A l₁ ⊔ A ∙ g := heq ▸ mem_sup_right (mem_span_singleton_self x)
    obtain ⟨a, -, hxa⟩ := exists_unit_of_mem_sup (hg.mono le_sup_left) hxg hxB
    have hlg : Adm P T (l₁ ++ g :: l₂) := hl.replace h2 h1 (hg.mono le_sup_left)
    obtain ⟨hf, hmove⟩ := move_front hg l₁ hlg
    have hg1 : Adm P (P ⊔ A ∙ g) [g] := ⟨mem_sup_right (mem_span_singleton_self g), hgP, hg, rfl⟩
    obtain ⟨μ, hμ, hlen⟩ := ih hf.2.2.2 hk'
    refine ⟨residue A a * (-1) ^ l₁.length * μ, fun c hc => ?_, ?_⟩
    · have h3 := hμ _ (hc.prefix hg1)
      simp only [List.singleton_append] at h3
      rw [hc.smul l₁ l₂ x g (x - a • g) a hl hlg hxa (by abel), hmove c hc, h3]
      ring
    · simp only [List.length_append, List.length_cons] at hlen ⊢
      omega

/-! ### Existence of a nonvanishing volume (Stacks 42.68.5) -/

lemma self_mem_sup_span (B : Submodule A M) (v : M) : v ∈ B ⊔ A ∙ v :=
  mem_sup_right (mem_span_singleton_self v)

lemma Adm.lt_of_mid {P T : Submodule A M} {l₁ l₂ : List M} {v : M} (h : Adm P T (l₁ ++ v :: l₂)) :
    P < T := by
  obtain ⟨hvT, hvB, -, -⟩ := h.mid
  refine lt_of_le_of_ne h.le ?_
  rintro rfl
  exact hvB (mem_sup_left hvT)

/-- In a finite length module, every proper step `P < T` contains an element killed by `𝔪`
modulo `P` (a socle element of `T/P`).-/
lemma exists_mkill [IsArtinian A M] {P T : Submodule A M} (h : P < T) :
    ∃ f ∈ T, f ∉ P ∧ MKill P f := by
  obtain ⟨Q, ⟨hPQ, hQT⟩, hmin⟩ := (wellFounded_lt (α := Submodule A M)).has_min
    {Q | P < Q ∧ Q ≤ T} ⟨T, h, le_rfl⟩
  obtain ⟨f, hfQ, hfP⟩ := SetLike.exists_of_lt hPQ
  refine ⟨f, hQT hfQ, hfP, fun r hr => ?_⟩
  by_contra hrf
  have hle : P ⊔ A ∙ (r • f) ≤ Q :=
    sup_le hPQ.le ((span_singleton_le_iff_mem _ _).2 (Q.smul_mem r hfQ))
  have hlt : P < P ⊔ A ∙ (r • f) :=
    lt_of_le_of_ne le_sup_left fun he => hrf (he ▸ self_mem_sup_span P (r • f))
  have heq : P ⊔ A ∙ (r • f) = Q := by
    by_contra hne
    exact hmin _ ⟨hlt, hle.trans hQT⟩ (lt_of_le_of_ne hle hne)
  have hf' : f ∈ P ⊔ A ∙ (r • f) := heq ▸ hfQ
  obtain ⟨p, hp, z, hz, hpz⟩ := mem_sup.1 hf'
  obtain ⟨s, rfl⟩ := mem_span_singleton.1 hz
  have hu : IsUnit (1 - s * r) :=
    isUnit_one_sub_self_of_mem_nonunits _ ((maximalIdeal A).mul_mem_left s hr)
  have : (1 - s * r) • f = p := by
    rw [sub_smul, one_smul, mul_smul]; exact sub_eq_of_eq_add hpz.symm
  exact hfP ((P.smul_mem_iff_of_isUnit hu).1 (this ▸ hp))

open Classical in
/-- The residue of `a` where `x ≡ a • f` modulo `R` (junk `0` if there is no such `a`).-/
noncomputable def coef (R : Submodule A M) (x f : M) : ResidueField A :=
  if h : ∃ a : A, x - a • f ∈ R then residue A h.choose else 0

lemma coef_eq {R : Submodule A M} {x f : M} {a : A} (hf : f ∉ R) (h : x - a • f ∈ R) :
    coef R x f = residue A a := by
  have h' : ∃ a : A, x - a • f ∈ R := ⟨a, h⟩
  rw [coef, dite_eq_left h', ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  by_contra hab
  have hmem : (h'.choose - a) • f ∈ R := by
    have := R.sub_mem h h'.choose_spec
    convert this using 1
    rw [sub_smul]; abel
  exact hf ((R.smul_mem_iff_of_isUnit (notMem_maximalIdeal.1 hab)).1 hmem)

lemma exists_coef {B : Submodule A M} {x f : M} (hx : MKill B x) (hxB : x ∉ B) (hfB : f ∉ B)
    (hf : MKill B f) (h : f ∈ B ⊔ A ∙ x) : ∃ a : A, IsUnit a ∧ x - a • f ∈ B :=
  exists_unit_of_mem_sup hf ((sup_span_eq_of_mem hx h hfB) ▸ self_mem_sup_span B x) hxB

open Classical in
/-- Stacks' map `det_κ(M) → det_κ(M/⟨f⟩)` (proof of 42.68.5), dualised: the value of a list is
`(-1)^i · λ̄ · c'(l without its i-th entry)` where `i` is the step at which `f` is reached and
`e_i ≡ λ f`.-/
noncomputable def splitVal (P : Submodule A M) (f : M) (c' : List M → ResidueField A)
    (l : List M) : ResidueField A :=
  if h : ∃ s : List M × M × List M, l = s.1 ++ s.2.1 :: s.2.2 ∧ f ∉ P ⊔ lspan A s.1 ∧
      f ∈ P ⊔ lspan A s.1 ⊔ A ∙ s.2.1 then
    (-1) ^ h.choose.1.length * coef (P ⊔ lspan A h.choose.1) h.choose.2.1 f *
      c' (h.choose.1 ++ h.choose.2.2)
  else 0

lemma splitVal_eq {P : Submodule A M} {f : M} {c' : List M → ResidueField A} {l₁ l₂ : List M}
    {x : M} (h1 : f ∉ P ⊔ lspan A l₁) (h2 : f ∈ P ⊔ lspan A l₁ ⊔ A ∙ x) :
    splitVal P f c' (l₁ ++ x :: l₂) =
      (-1) ^ l₁.length * coef (P ⊔ lspan A l₁) x f * c' (l₁ ++ l₂) := by
  have h : ∃ s : List M × M × List M, l₁ ++ x :: l₂ = s.1 ++ s.2.1 :: s.2.2 ∧
      f ∉ P ⊔ lspan A s.1 ∧ f ∈ P ⊔ lspan A s.1 ⊔ A ∙ s.2.1 := ⟨(l₁, x, l₂), rfl, h1, h2⟩
  rw [splitVal, dite_eq_left h]
  obtain ⟨hs, hs1, hs2⟩ := h.choose_spec
  obtain ⟨e1, e2, e3⟩ := split_unique hs h1 h2 hs1 hs2
  rw [← e1, ← e2, ← e3]

lemma sup_lspan_mid (P : Submodule A M) (l₁ k₁ : List M) (z : M) :
    P ⊔ lspan A (l₁ ++ z :: k₁) = P ⊔ lspan A l₁ ⊔ A ∙ z ⊔ lspan A k₁ := by
  rw [sup_lspan_append, lspan_cons, ← sup_assoc]

section splitVal

variable {P T : Submodule A M} {f : M} {c' : List M → ResidueField A}

lemma splitVal_smul (hf : MKill P f) (hfP : f ∉ P) (hfT : f ∈ T) (hc' : IsVol (P ⊔ A ∙ f) T c')
    (l₁ l₂ : List M) (v w x : M) (a : A) (h : Adm P T (l₁ ++ v :: l₂))
    (h' : Adm P T (l₁ ++ w :: l₂)) (hx : x ∈ P ⊔ lspan A l₁) (he : v = a • w + x) :
    splitVal P f c' (l₁ ++ v :: l₂) = residue A a * splitVal P f c' (l₁ ++ w :: l₂) := by
  obtain ⟨-, hvB, hvk, -⟩ := h.mid
  obtain ⟨-, hwB, hwk, -⟩ := h'.mid
  have hvw : P ⊔ lspan A l₁ ⊔ A ∙ v = P ⊔ lspan A l₁ ⊔ A ∙ w :=
    sup_span_eq_of_mem hwk (by
      rw [he]; exact add_mem (smul_mem _ _ (self_mem_sup_span _ w)) (mem_sup_left hx)) hvB
  by_cases hA : f ∈ P ⊔ lspan A l₁
  · obtain ⟨k₁, y, k₂, rfl, h1, h2⟩ := exists_split hA hfP
    have e : ∀ z, (k₁ ++ y :: k₂) ++ z :: l₂ = k₁ ++ y :: (k₂ ++ z :: l₂) := fun z => by simp
    rw [e, e, splitVal_eq h1 h2, splitVal_eq h1 h2]
    rw [e] at h h'
    have hyk := h.mid.2.2.1
    have hBQ := sup_lspan_erase (l₂ := k₂) hyk h1 h2
    have h3 := adm_erase h hf h1 h2
    have h3' := adm_erase h' hf h1 h2
    rw [← List.append_assoc] at h3 h3'
    have := hc'.smul (k₁ ++ k₂) l₂ v w x a h3 h3' (hBQ ▸ hx) he
    simp only [List.append_assoc] at this
    rw [this]; ring
  by_cases hBv : f ∈ P ⊔ lspan A l₁ ⊔ A ∙ v
  · have hBw : f ∈ P ⊔ lspan A l₁ ⊔ A ∙ w := hvw ▸ hBv
    rw [splitVal_eq hA hBv, splitVal_eq hA hBw]
    obtain ⟨b, -, hb⟩ := exists_coef hwk hwB hA (hf.mono le_sup_left) hBw
    rw [coef_eq hA hb, coef_eq (a := a * b) hA ?_]
    · rw [map_mul]; ring
    · have : v - (a * b) • f = a • (w - b • f) + x := by
        rw [he, smul_sub, mul_smul]; abel
      rw [this]; exact add_mem (smul_mem _ _ hb) hx
  · have hfl : f ∈ P ⊔ lspan A l₁ ⊔ A ∙ v ⊔ lspan A l₂ := by
      have := h.sup_lspan
      rw [sup_lspan_mid] at this
      exact this ▸ hfT
    obtain ⟨k₁, y, k₂, rfl, h1, h2⟩ := exists_split hfl hBv
    have e : ∀ z, l₁ ++ z :: (k₁ ++ y :: k₂) = (l₁ ++ z :: k₁) ++ y :: k₂ := fun z => by simp
    have h1v : f ∉ P ⊔ lspan A (l₁ ++ v :: k₁) := by rw [sup_lspan_mid]; exact h1
    have h2v : f ∈ P ⊔ lspan A (l₁ ++ v :: k₁) ⊔ A ∙ y := by rw [sup_lspan_mid]; exact h2
    have h1w : f ∉ P ⊔ lspan A (l₁ ++ w :: k₁) := by rw [sup_lspan_mid, ← hvw]; exact h1
    have h2w : f ∈ P ⊔ lspan A (l₁ ++ w :: k₁) ⊔ A ∙ y := by rw [sup_lspan_mid, ← hvw]; exact h2
    rw [e, e, splitVal_eq h1v h2v, splitVal_eq h1w h2w, sup_lspan_mid, sup_lspan_mid, ← hvw]
    rw [e] at h h'
    have h3 := adm_erase h hf h1v h2v
    have h3' := adm_erase h' hf h1w h2w
    simp only [List.append_assoc, List.cons_append] at h3 h3'
    have hxQ : x ∈ P ⊔ A ∙ f ⊔ lspan A l₁ :=
      (sup_le_sup_right (le_sup_left : P ≤ P ⊔ A ∙ f) (lspan A l₁)) hx
    have := hc'.smul l₁ (k₁ ++ k₂) v w x a h3 h3' hxQ he
    simp only [List.append_assoc, List.cons_append, List.length_append, List.length_cons]
    rw [this]; ring

lemma splitVal_swap_caseB (hf : MKill P f) {l₁ l₂ : List M} {u v : M}
    (h : Adm P T (l₁ ++ u :: v :: l₂)) (h' : Adm P T (l₁ ++ v :: u :: l₂))
    (hA : f ∉ P ⊔ lspan A l₁) (hU : f ∈ P ⊔ lspan A l₁ ⊔ A ∙ u) :
    splitVal P f c' (l₁ ++ u :: v :: l₂) = - splitVal P f c' (l₁ ++ v :: u :: l₂) := by
  obtain ⟨-, huB, huk, -, hvB', -, -⟩ := h.mid
  obtain ⟨-, -, hvk, -, -, -, -⟩ := h'.mid
  have hV : f ∉ P ⊔ lspan A l₁ ⊔ A ∙ v := by
    intro hV
    have e1 := sup_span_eq_of_mem huk hU hA
    have e2 := sup_span_eq_of_mem hvk hV hA
    exact hvB' (by rw [← e1, e2]; exact self_mem_sup_span _ v)
  have e : l₁ ++ v :: u :: l₂ = (l₁ ++ [v]) ++ u :: l₂ := by simp
  have h1 : f ∉ P ⊔ lspan A (l₁ ++ [v]) := by rw [sup_lspan_snoc]; exact hV
  have h2 : f ∈ P ⊔ lspan A (l₁ ++ [v]) ⊔ A ∙ u := by
    rw [sup_lspan_snoc]
    exact (sup_le_sup_right (le_sup_left : P ⊔ lspan A l₁ ≤ P ⊔ lspan A l₁ ⊔ A ∙ v) (A ∙ u)) hU
  rw [e, splitVal_eq h1 h2, splitVal_eq hA hU, sup_lspan_snoc]
  obtain ⟨b, -, hb⟩ := exists_coef huk huB hA (hf.mono le_sup_left) hU
  rw [coef_eq hA hb, coef_eq hV (mem_sup_left hb)]
  simp only [List.length_append, List.length_singleton, pow_succ, List.append_assoc,
    List.singleton_append]
  ring

lemma splitVal_swap (hf : MKill P f) (hfP : f ∉ P) (hfT : f ∈ T) (hc' : IsVol (P ⊔ A ∙ f) T c')
    (l₁ l₂ : List M) (u v : M) (h : Adm P T (l₁ ++ u :: v :: l₂))
    (h' : Adm P T (l₁ ++ v :: u :: l₂)) :
    splitVal P f c' (l₁ ++ u :: v :: l₂) = - splitVal P f c' (l₁ ++ v :: u :: l₂) := by
  obtain ⟨-, huB, huk, -, hvB', hvk', -⟩ := h.mid
  obtain ⟨-, hvB, hvk, -, huB', huk', -⟩ := h'.mid
  by_cases hA : f ∈ P ⊔ lspan A l₁
  · obtain ⟨k₁, y, k₂, rfl, h1, h2⟩ := exists_split hA hfP
    have e : ∀ p q, (k₁ ++ y :: k₂) ++ p :: q :: l₂ = k₁ ++ y :: (k₂ ++ p :: q :: l₂) :=
      fun p q => by simp
    rw [e, e, splitVal_eq h1 h2, splitVal_eq h1 h2]
    rw [e] at h h'
    have h3 := adm_erase h hf h1 h2
    have h3' := adm_erase h' hf h1 h2
    rw [← List.append_assoc] at h3 h3'
    have := hc'.swap (k₁ ++ k₂) l₂ u v h3 h3'
    simp only [List.append_assoc] at this
    rw [this]; ring
  by_cases hU : f ∈ P ⊔ lspan A l₁ ⊔ A ∙ u
  · exact splitVal_swap_caseB hf h h' hA hU
  by_cases hV : f ∈ P ⊔ lspan A l₁ ⊔ A ∙ v
  · rw [splitVal_swap_caseB hf h' h hA hV, neg_neg]
  by_cases hE : f ∈ P ⊔ lspan A l₁ ⊔ A ∙ u ⊔ A ∙ v
  · -- Case E: `f` is reached exactly at the second of the two swapped steps, in both orders.
    have e : ∀ p q : M, l₁ ++ p :: q :: l₂ = (l₁ ++ [p]) ++ q :: l₂ := fun p q => by simp
    have hE' : f ∈ P ⊔ lspan A l₁ ⊔ A ∙ v ⊔ A ∙ u := by rw [sup_right_comm]; exact hE
    have h1 : f ∉ P ⊔ lspan A (l₁ ++ [u]) := by rw [sup_lspan_snoc]; exact hU
    have h2 : f ∈ P ⊔ lspan A (l₁ ++ [u]) ⊔ A ∙ v := by rw [sup_lspan_snoc]; exact hE
    have h1' : f ∉ P ⊔ lspan A (l₁ ++ [v]) := by rw [sup_lspan_snoc]; exact hV
    have h2' : f ∈ P ⊔ lspan A (l₁ ++ [v]) ⊔ A ∙ u := by rw [sup_lspan_snoc]; exact hE'
    have hE1 := adm_erase (by rw [← e]; exact h) hf h1 h2
    have hE2 := adm_erase (by rw [← e]; exact h') hf h1' h2'
    simp only [List.append_assoc, List.singleton_append] at hE1 hE2
    rw [e, e, splitVal_eq h1 h2, splitVal_eq h1' h2', sup_lspan_snoc, sup_lspan_snoc]
    simp only [List.append_assoc, List.singleton_append, List.length_append,
      List.length_singleton]
    -- `v ≡ λ f + α u` modulo `B`, `u ≡ λ' f + β v` modulo `B`
    have hfB : P ≤ P ⊔ lspan A l₁ := le_sup_left
    obtain ⟨la, -, hla⟩ := exists_coef hvk' hvB' hU (hf.mono (hfB.trans le_sup_left)) hE
    obtain ⟨lb, -, hlb⟩ := exists_coef huk' huB' hV (hf.mono (hfB.trans le_sup_left)) hE'
    obtain ⟨b, hb, z, hz, hbz⟩ := mem_sup.1 hla
    obtain ⟨α, rfl⟩ := mem_span_singleton.1 hz
    obtain ⟨b', hb', z', hz', hbz'⟩ := mem_sup.1 hlb
    obtain ⟨β, rfl⟩ := mem_span_singleton.1 hz'
    rw [coef_eq hU hla, coef_eq hV hlb]
    have hrel : c' (l₁ ++ v :: l₂) = residue A α * c' (l₁ ++ u :: l₂) :=
      hc'.smul l₁ l₂ v u (b + la • f) α hE2 hE1
        (add_mem ((sup_le_sup_right (le_sup_left : P ≤ P ⊔ A ∙ f) (lspan A l₁)) hb)
          (mem_sup_left (smul_mem _ _ (self_mem_sup_span P f))))
        (by rw [← add_assoc, add_comm (α • u), hbz]; abel)
    rw [hrel]
    -- the residues satisfy `λ̄ = - ᾱ λ̄'`
    have key : (la + α * lb) • f = (1 - α * β) • v - (b + α • b') := by
      have e1 : la • f = v - (b + α • u) := by rw [hbz]; abel
      have e2 : lb • f = u - (b' + β • v) := by rw [hbz']; abel
      rw [add_smul, mul_smul, e1, e2]
      simp only [smul_sub, smul_add, sub_smul, one_smul, mul_smul]
      abel
    have hm : la + α * lb ∈ maximalIdeal A := by
      by_contra hu
      apply hV
      rw [← (P ⊔ lspan A l₁ ⊔ A ∙ v).smul_mem_iff_of_isUnit (notMem_maximalIdeal.1 hu), key]
      exact sub_mem (smul_mem _ _ (self_mem_sup_span _ v))
        (mem_sup_left (add_mem hb (smul_mem _ _ hb')))
    have hres : residue A la = - (residue A α * residue A lb) := by
      rw [eq_neg_iff_add_eq_zero, ← map_mul, ← map_add, residue_eq_zero_iff]; exact hm
    rw [hres]; ring
  · -- Case D: `f` is reached after the two swapped steps.
    have hfl : f ∈ P ⊔ lspan A l₁ ⊔ A ∙ u ⊔ A ∙ v ⊔ lspan A l₂ := by
      have := h.sup_lspan
      rw [sup_lspan_mid, lspan_cons, ← sup_assoc] at this
      exact this ▸ hfT
    obtain ⟨k₁, y, k₂, rfl, h1, h2⟩ := exists_split hfl hE
    have e : ∀ p q, l₁ ++ p :: q :: (k₁ ++ y :: k₂) = (l₁ ++ p :: q :: k₁) ++ y :: k₂ :=
      fun p q => by simp
    have sp : ∀ p q, P ⊔ lspan A (l₁ ++ p :: q :: k₁) =
        P ⊔ lspan A l₁ ⊔ A ∙ p ⊔ A ∙ q ⊔ lspan A k₁ := fun p q => by
      rw [sup_lspan_mid, lspan_cons, ← sup_assoc]
    have h1u : f ∉ P ⊔ lspan A (l₁ ++ u :: v :: k₁) := by rw [sp]; exact h1
    have h2u : f ∈ P ⊔ lspan A (l₁ ++ u :: v :: k₁) ⊔ A ∙ y := by rw [sp]; exact h2
    have h1v : f ∉ P ⊔ lspan A (l₁ ++ v :: u :: k₁) := by
      rw [sp, sup_right_comm (P ⊔ lspan A l₁)]; exact h1
    have h2v : f ∈ P ⊔ lspan A (l₁ ++ v :: u :: k₁) ⊔ A ∙ y := by
      rw [sp, sup_right_comm (P ⊔ lspan A l₁)]; exact h2
    rw [e, e, splitVal_eq h1u h2u, splitVal_eq h1v h2v, sp, sp,
      sup_right_comm (P ⊔ lspan A l₁) (A ∙ v)]
    rw [e] at h h'
    have h3 := adm_erase h hf h1u h2u
    have h3' := adm_erase h' hf h1v h2v
    simp only [List.append_assoc, List.cons_append] at h3 h3'
    have := hc'.swap l₁ (k₁ ++ k₂) u v h3 h3'
    simp only [List.append_assoc, List.cons_append, List.length_append, List.length_cons]
    rw [this]; ring

lemma isVol_splitVal (hf : MKill P f) (hfP : f ∉ P) (hfT : f ∈ T)
    (hc' : IsVol (P ⊔ A ∙ f) T c') : IsVol P T (splitVal P f c') where
  smul := splitVal_smul hf hfP hfT hc'
  swap := splitVal_swap hf hfP hfT hc'

lemma splitVal_ne_zero (hf : MKill P f) (hfP : f ∉ P) (hfT : f ∈ T)
    (hc'0 : ∀ l, Adm (P ⊔ A ∙ f) T l → c' l ≠ 0) {l : List M} (hl : Adm P T l) :
    splitVal P f c' l ≠ 0 := by
  obtain ⟨l₁, x, l₂, rfl, h1, h2⟩ := exists_split (hl.sup_lspan ▸ hfT : f ∈ P ⊔ lspan A l) hfP
  obtain ⟨-, hxB, hxk, -⟩ := hl.mid
  obtain ⟨a, ha, hax⟩ := exists_coef hxk hxB h1 (hf.mono le_sup_left) h2
  rw [splitVal_eq h1 h2, coef_eq h1 hax]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
    ((residue_ne_zero_iff_isUnit a).2 ha)) (hc'0 _ (adm_erase hl hf h1 h2))

end splitVal

/-- **Stacks 42.68.5** (`det_κ(T/P)` is nonzero), dually: a volume nonvanishing on every
admissible list.-/
theorem exists_vol [IsArtinian A M] [IsNoetherian A M] (T P : Submodule A M) :
    ∃ c : List M → ResidueField A, IsVol P T c ∧ ∀ l, Adm P T l → c l ≠ 0 := by
  induction P using WellFoundedGT.induction with
  | _ P ih =>
  by_cases hPT : P < T
  · obtain ⟨f, hfT, hfP, hf⟩ := exists_mkill hPT
    obtain ⟨c', hc', hc'0⟩ := ih (P ⊔ A ∙ f)
      (lt_of_le_of_ne le_sup_left fun he => hfP (he ▸ self_mem_sup_span P f))
    exact ⟨splitVal P f c', isVol_splitVal hf hfP hfT hc', fun l hl =>
      splitVal_ne_zero hf hfP hfT hc'0 hl⟩
  · refine ⟨fun l => if l = [] then 1 else 0, ⟨?_, ?_⟩, ?_⟩
    · intro l₁ l₂ v w x a h; exact absurd h.lt_of_mid hPT
    · intro l₁ l₂ u v h; exact absurd h.lt_of_mid hPT
    · intro l hl
      cases l with
      | nil => simp
      | cons v l => exact absurd (Adm.lt_of_mid (l₁ := []) hl) hPT

/-! ### Lengths, block moves, units -/

lemma Adm.length_eq {P T : Submodule A M} {l l' : List M} (hl : Adm P T l) (hl' : Adm P T l') :
    l.length = l'.length :=
  (vol_unique hl hl').choose_spec.2

/-- `𝔪 e_i ⊆ B + ⟨e_<i⟩` along a list (the part of admissibility used by block moves).-/
lemma move_block {P T S : Submodule A M} (X l₂ : List M) {Y : List M} :
    ∀ {l₀ : List M}, Adm (P ⊔ lspan A l₀) S Y → Adm P T (l₀ ++ X ++ Y ++ l₂) →
      Adm P T (l₀ ++ Y ++ X ++ l₂) ∧ ∀ c, IsVol P T c →
        c (l₀ ++ X ++ Y ++ l₂) = (-1) ^ (X.length * Y.length) * c (l₀ ++ Y ++ X ++ l₂) := by
  induction Y with
  | nil => intro l₀ _ h; simpa using h
  | cons y Y ih =>
    intro l₀ hY h
    obtain ⟨-, -, hyk, hY'⟩ := hY
    have h0 : Adm P (P ⊔ lspan A l₀) l₀ := adm_append_left (l₂ := X ++ y :: Y ++ l₂)
      (by simpa only [List.append_assoc, List.cons_append] using h)
    have h1 : Adm (P ⊔ lspan A l₀) T (X ++ y :: (Y ++ l₂)) := adm_append_right
      (by simpa only [List.append_assoc, List.cons_append] using h)
    obtain ⟨h2, h3⟩ := move_front hyk X h1
    have h4 : Adm P T ((l₀ ++ [y]) ++ X ++ Y ++ l₂) := by
      have := adm_append h0 h2
      simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using this
    have hY'' : Adm (P ⊔ lspan A (l₀ ++ [y])) S Y := by rw [sup_lspan_snoc]; exact hY'
    obtain ⟨h5, h6⟩ := ih hY'' h4
    refine ⟨by simpa only [List.append_assoc, List.cons_append, List.singleton_append,
      List.nil_append] using h5,
      fun c hc => ?_⟩
    have h7 := h3 _ (hc.prefix h0)
    have h8 := h6 c hc
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h7 h8 ⊢
    rw [h7, h8, List.length_cons]
    ring

lemma adm_smul_unit {u : A} (hu : IsUnit u) {T : Submodule A M} {l : List M} :
    ∀ {P : Submodule A M}, Adm P T l → Adm P T (l.map (u • ·)) := by
  induction l with
  | nil => intro P h; exact h
  | cons v l ih =>
    intro P h
    obtain ⟨hvT, hvP, hvk, hl⟩ := h
    refine ⟨T.smul_mem u hvT, fun h' => hvP ((P.smul_mem_iff_of_isUnit hu).1 h'),
      fun r hr => ?_, ?_⟩
    · rw [smul_comm]; exact P.smul_mem u (hvk r hr)
    · rw [span_singleton_smul_eq hu]; exact ih hl

/-- Multiplying every entry by a unit `u` multiplies a volume by `ū ^ length` (Stacks 42.68.10).-/
lemma vol_smul_unit {u : A} (hu : IsUnit u) {P T : Submodule A M} {c : List M → ResidueField A}
    (hc : IsVol P T c) (l : List M) :
    ∀ {l₀ : List M}, Adm P T (l₀ ++ l) →
      c (l₀ ++ l.map (u • ·)) = residue A u ^ l.length * c (l₀ ++ l) := by
  induction l with
  | nil => intro l₀ _; simp
  | cons v l ih =>
    intro l₀ h
    have h0 := adm_append_left h
    have h1 : Adm (P ⊔ lspan A l₀) T (v :: l) := adm_append_right h
    have hA : Adm P T (l₀ ++ v :: l.map (u • ·)) :=
      adm_append h0 ⟨h1.1, h1.2.1, h1.2.2.1, adm_smul_unit hu h1.2.2.2⟩
    have hB : Adm P T (l₀ ++ (u • v) :: l.map (u • ·)) :=
      adm_append h0 (adm_smul_unit hu h1)
    have e1 := hc.smul l₀ (l.map (u • ·)) (u • v) v 0 u hB hA (zero_mem _) (by simp)
    have e2 := ih (l₀ := l₀ ++ [v]) (by simpa only [List.append_assoc, List.singleton_append] using h)
    simp only [List.append_assoc, List.singleton_append] at e2
    simp only [List.map_cons, List.length_cons]
    rw [e1, e2, pow_succ]; ring

/-! ### Transport along linear maps -/

section map

variable {M' : Type*} [AddCommGroup M'] [Module A M']

lemma lspan_map (g : M →ₗ[A] M') (l : List M) : lspan A (l.map g) = (lspan A l).map g := by
  rw [lspan, lspan, map_span]
  congr 1
  ext y
  simp

lemma map_sup_span (g : M →ₗ[A] M') (R : Submodule A M) (v : M) :
    (R ⊔ A ∙ v).map g = R.map g ⊔ A ∙ g v := by
  rw [Submodule.map_sup, map_span, Set.image_singleton]

/-- Forward transport of admissible lists along `g`, modulo `P'` on the target, provided
`g` is injective on `T/R` modulo `P'`.-/
lemma adm_map (g : M →ₗ[A] M') (P' : Submodule A M') {T : Submodule A M} {l : List M} :
    ∀ {R : Submodule A M}, T ⊓ P'.comap g ≤ R → Adm R T l →
      Adm (R.map g ⊔ P') (T.map g ⊔ P') (l.map g) := by
  induction l with
  | nil => intro R _ h; simp only [adm_nil, List.map_nil] at h ⊢; rw [h]
  | cons v l ih =>
    intro R hR h
    obtain ⟨hvT, hvR, hvk, hl⟩ := h
    have hRT : R ≤ T := le_sup_left.trans hl.le
    refine ⟨mem_sup_left (mem_map_of_mem hvT), ?_, ?_, ?_⟩
    · intro hv
      obtain ⟨y, hy, p, hp, hyp⟩ := mem_sup.1 hv
      obtain ⟨r, hr, rfl⟩ := mem_map.1 hy
      have : v - r ∈ T ⊓ P'.comap g := by
        refine ⟨sub_mem hvT (hRT hr), ?_⟩
        show g (v - r) ∈ P'
        rw [map_sub, ← hyp]; simpa using hp
      exact hvR (by simpa using add_mem (hR this) hr)
    · intro r hr
      rw [← map_smul]
      exact mem_sup_left (mem_map_of_mem (hvk r hr))
    · have := ih (hR.trans le_sup_left) hl
      rwa [map_sup_span, sup_right_comm] at this

/-- Backward transport of admissible lists along `g`.-/
lemma adm_of_map (g : M →ₗ[A] M') (P' : Submodule A M') {T : Submodule A M} {l : List M}
    (hlT : ∀ v ∈ l, v ∈ T) :
    ∀ {R : Submodule A M}, T ⊓ P'.comap g ≤ R → R ≤ T →
      Adm (R.map g ⊔ P') (T.map g ⊔ P') (l.map g) → Adm R T l := by
  have key : ∀ {R : Submodule A M}, T ⊓ P'.comap g ≤ R → R ≤ T → ∀ t ∈ T,
      g t ∈ R.map g ⊔ P' → t ∈ R := by
    intro R hR hRT t ht hgt
    obtain ⟨y, hy, p, hp, hyp⟩ := mem_sup.1 hgt
    obtain ⟨r, hr, rfl⟩ := mem_map.1 hy
    have : t - r ∈ T ⊓ P'.comap g := by
      refine ⟨sub_mem ht (hRT hr), ?_⟩
      show g (t - r) ∈ P'
      rw [map_sub, ← hyp]; simpa using hp
    simpa using add_mem (hR this) hr
  induction l with
  | nil =>
    intro R hR hRT h
    simp only [adm_nil, List.map_nil] at h ⊢
    refine le_antisymm hRT fun t ht => key hR hRT t ht ?_
    rw [h]; exact mem_sup_left (mem_map_of_mem ht)
  | cons v l ih =>
    intro R hR hRT h
    obtain ⟨-, hvR, hvk, hl⟩ := h
    have hvT := hlT v (List.mem_cons_self ..)
    refine ⟨hvT, fun hv => hvR (mem_sup_left (mem_map_of_mem hv)), fun r hr => ?_, ?_⟩
    · refine key hR hRT _ (T.smul_mem r hvT) ?_
      rw [map_smul]; exact hvk r hr
    · refine ih (fun w hw => hlT w (List.mem_cons_of_mem _ hw)) (hR.trans le_sup_left)
        (sup_le hRT ((span_singleton_le_iff_mem _ _).2 hvT)) ?_
      rwa [map_sup_span, sup_right_comm]

lemma IsVol.comap (g : M →ₗ[A] M') (P' : Submodule A M') {R T : Submodule A M}
    {c : List M' → ResidueField A} (hTR : T ⊓ P'.comap g ≤ R)
    (hc : IsVol (R.map g ⊔ P') (T.map g ⊔ P') c) : IsVol R T (fun l => c (l.map g)) where
  smul l₁ l₂ v w x a h h' hx he := by
    have hm := adm_map g P' hTR h
    have hm' := adm_map g P' hTR h'
    simp only [List.map_append, List.map_cons] at hm hm' ⊢
    refine hc.smul _ _ (g v) (g w) (g x) a hm hm' ?_ (by rw [he, map_add, map_smul])
    rw [lspan_map, sup_right_comm, ← Submodule.map_sup]
    exact mem_sup_left (mem_map_of_mem hx)
  swap l₁ l₂ u v h h' := by
    have hm := adm_map g P' hTR h
    have hm' := adm_map g P' hTR h'
    simp only [List.map_append, List.map_cons] at hm hm' ⊢
    exact hc.swap _ _ (g u) (g v) hm hm'

end map

/-! ### The ratio `[l] / [l']` in `det_κ(T/P)` -/

section ratio

variable [IsArtinian A M] [IsNoetherian A M]

/-- A fixed volume on `T/P`, nonvanishing on all admissible lists.-/
noncomputable def vol0 (P T : Submodule A M) : List M → ResidueField A :=
  (exists_vol T P).choose

lemma isVol_vol0 (P T : Submodule A M) : IsVol P T (vol0 P T) :=
  (exists_vol T P).choose_spec.1

lemma vol0_ne_zero {P T : Submodule A M} {l : List M} (hl : Adm P T l) : vol0 P T l ≠ 0 :=
  (exists_vol T P).choose_spec.2 l hl

/-- `ratio P T l l' = [l] / [l']` in Stacks' `det_κ(T/P)`.-/
noncomputable def ratio (P T : Submodule A M) (l l' : List M) : ResidueField A :=
  vol0 P T l / vol0 P T l'

variable {P S T : Submodule A M} {l l' l'' : List M}

theorem vol_eq_ratio_mul {c : List M → ResidueField A} (hc : IsVol P T c) (hl : Adm P T l)
    (hl' : Adm P T l') : c l = ratio P T l l' * c l' := by
  obtain ⟨μ, hμ, -⟩ := vol_unique hl hl'
  rw [hμ c hc, ratio, hμ _ (isVol_vol0 P T), mul_div_cancel_right₀ _ (vol0_ne_zero hl')]

theorem ratio_eq_div {c : List M → ResidueField A} (hc : IsVol P T c) (hl : Adm P T l)
    (hl' : Adm P T l') (hc' : c l' ≠ 0) : ratio P T l l' = c l / c l' := by
  rw [vol_eq_ratio_mul hc hl hl', mul_div_cancel_right₀ _ hc']

lemma ratio_ne_zero (hl : Adm P T l) (hl' : Adm P T l') : ratio P T l l' ≠ 0 :=
  div_ne_zero (vol0_ne_zero hl) (vol0_ne_zero hl')

lemma ratio_self (hl : Adm P T l) : ratio P T l l = 1 :=
  div_self (vol0_ne_zero hl)

lemma ratio_mul_ratio (hl' : Adm P T l') :
    ratio P T l l' * ratio P T l' l'' = ratio P T l l'' := by
  rw [ratio, ratio, ratio, div_mul_div_cancel₀ (vol0_ne_zero hl')]

lemma ratio_mul_ratio_symm (hl : Adm P T l) (hl' : Adm P T l') :
    ratio P T l l' * ratio P T l' l = 1 := by
  rw [ratio_mul_ratio hl', ratio_self hl]

lemma ratio_append_left {l₀ : List M} (h₀ : Adm P S l₀) (hl : Adm S T l) (hl' : Adm S T l') :
    ratio P T (l₀ ++ l) (l₀ ++ l') = ratio S T l l' := by
  have hc := (isVol_vol0 P T).prefix h₀
  rw [ratio_eq_div hc hl hl' (vol0_ne_zero (adm_append h₀ hl')), ratio]

lemma ratio_append_right {l₀ : List M} (h₀ : Adm S T l₀) (hl : Adm P S l) (hl' : Adm P S l') :
    ratio P T (l ++ l₀) (l' ++ l₀) = ratio P S l l' := by
  have hc := (isVol_vol0 P T).suffix h₀
  rw [ratio_eq_div hc hl hl' (vol0_ne_zero (adm_append hl' h₀)), ratio]

/-- Multiplicativity of `det_κ` in short exact sequences `0 → S/P → T/P → T/S → 0`
(Stacks 42.68.6), in ratio form.-/
lemma ratio_append {l₁ l₁' l₂ l₂' : List M} (h₁ : Adm P S l₁) (h₁' : Adm P S l₁')
    (h₂ : Adm S T l₂) (h₂' : Adm S T l₂') :
    ratio P T (l₁ ++ l₂) (l₁' ++ l₂') = ratio P S l₁ l₁' * ratio S T l₂ l₂' := by
  rw [← ratio_mul_ratio (l' := l₁' ++ l₂) (adm_append h₁' h₂), ratio_append_right h₂ h₁ h₁',
    ratio_append_left h₁' h₂ h₂']

lemma ratio_move_block {X Y l₀ l₂ : List M} (hY : Adm (P ⊔ lspan A l₀) S Y)
    (h : Adm P T (l₀ ++ X ++ Y ++ l₂)) :
    ratio P T (l₀ ++ X ++ Y ++ l₂) l' =
      (-1) ^ (X.length * Y.length) * ratio P T (l₀ ++ Y ++ X ++ l₂) l' := by
  obtain ⟨h1, h2⟩ := move_block X l₂ hY h
  rw [ratio, ratio, h2 _ (isVol_vol0 P T), mul_div_assoc]

lemma ratio_smul_unit {u : A} (hu : IsUnit u) (hl : Adm P T l) :
    ratio P T (l.map (u • ·)) l = residue A u ^ l.length := by
  have := vol_smul_unit hu (isVol_vol0 P T) l (l₀ := []) hl
  simp only [List.nil_append] at this
  rw [ratio, this, mul_div_cancel_right₀ _ (vol0_ne_zero hl)]

variable {M' : Type*} [AddCommGroup M'] [Module A M'] [IsArtinian A M'] [IsNoetherian A M']

/-- `det_κ` is functorial for isomorphisms of subquotients induced by linear maps.-/
lemma ratio_map (g : M →ₗ[A] M') (P' : Submodule A M') {R : Submodule A M}
    (hTR : T ⊓ P'.comap g ≤ R) (hl : Adm R T l) (hl' : Adm R T l') :
    ratio R T l l' = ratio (R.map g ⊔ P') (T.map g ⊔ P') (l.map g) (l'.map g) := by
  have hc := (isVol_vol0 (R.map g ⊔ P') (T.map g ⊔ P')).comap g P' hTR
  rw [ratio_eq_div hc hl hl' (vol0_ne_zero (adm_map g P' hTR hl')), ratio]

end ratio

/-! ### Auxiliary existence and lattice lemmas -/

/-- Admissible lists of `T/P` with entries in a submodule `S` with `T ≤ S ⊔ P`.-/
lemma exists_adm_sub [IsArtinian A M] [IsNoetherian A M] (S T : Submodule A M) (P : Submodule A M) :
    P ≤ T → T ≤ S ⊔ P → ∃ l, Adm P T l ∧ ∀ v ∈ l, v ∈ S := by
  induction P using WellFoundedGT.induction with
  | _ P ih =>
  intro hPT hTS
  by_cases hlt : P < T
  · obtain ⟨f, hfT, hfP, hf⟩ := exists_mkill hlt
    obtain ⟨s, hs, p, hp, rfl⟩ := mem_sup.1 (hTS hfT)
    have hsP : s ∉ P := fun h => hfP (add_mem h hp)
    have hsT : s ∈ T := by simpa using sub_mem hfT (hPT hp)
    have hsk : MKill P s := fun r hr => by
      have := sub_mem (hf r hr) (P.smul_mem r hp)
      rwa [smul_add, add_sub_cancel_right] at this
    obtain ⟨l, hl, hlS⟩ := ih (P ⊔ A ∙ s)
      (lt_of_le_of_ne le_sup_left fun he => hsP (he ▸ self_mem_sup_span P s))
      (sup_le hPT ((span_singleton_le_iff_mem _ _).2 hsT))
      (hTS.trans (sup_le_sup_left le_sup_left _))
    refine ⟨s :: l, ⟨hsT, hsP, hsk, hl⟩, fun v hv => ?_⟩
    rcases List.mem_cons.1 hv with rfl | hv
    · exact hs
    · exact hlS v hv
  · exact ⟨[], (eq_of_le_of_not_lt hPT hlt), by simp⟩

lemma exists_adm [IsArtinian A M] [IsNoetherian A M] {P T : Submodule A M} (h : P ≤ T) :
    ∃ l, Adm P T l :=
  (exists_adm_sub T T P h le_sup_left).imp fun _ h => h.1

lemma exists_lift (φ : M →ₗ[A] M) (T : Submodule A M) :
    ∀ l : List M, (∀ v ∈ l, v ∈ T.map φ) → ∃ X : List M, X.map φ = l ∧ ∀ x ∈ X, x ∈ T
  | [], _ => ⟨[], rfl, by simp⟩
  | v :: l, h => by
    obtain ⟨x, hx, rfl⟩ := mem_map.1 (h v (List.mem_cons_self ..))
    obtain ⟨X, hX, hXT⟩ := exists_lift φ T l fun w hw => h w (List.mem_cons_of_mem _ hw)
    refine ⟨x :: X, by simp [hX], fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx
    · exact hXT y hy

lemma adm_inf (Q : Submodule A M) {T : Submodule A M} {l : List M} :
    ∀ {R : Submodule A M}, (∀ v ∈ l, v ∈ Q) → Adm R T l → Adm (R ⊓ Q) (T ⊓ Q) l := by
  induction l with
  | nil => intro R _ h; simp only [adm_nil] at h ⊢; rw [h]
  | cons v l ih =>
    intro R hQ h
    obtain ⟨hvT, hvR, hvk, hl⟩ := h
    have hvQ := hQ v (List.mem_cons_self ..)
    refine ⟨⟨hvT, hvQ⟩, fun hv => hvR hv.1, fun r hr => ⟨hvk r hr, Q.smul_mem r hvQ⟩, ?_⟩
    have := ih (fun w hw => hQ w (List.mem_cons_of_mem _ hw)) hl
    rwa [sup_comm, sup_inf_assoc_of_le _ ((span_singleton_le_iff_mem _ _).2 hvQ), sup_comm] at this

/-! ### Exact (2,1)-periodic complexes and their determinants (Stacks 42.68.12) -/

/-- `(T/P, φ, ψ)` is an exact `(2,1)`-periodic complex: `ker φ = im ψ` and `ker ψ = im φ` on the
subquotient `T/P` (this forces `φ T ⊆ T`, `φ P ⊆ P`, `ψ φ T ⊆ P`, and the same with `φ ↔ ψ`).-/
structure PerExact (P T : Submodule A M) (φ ψ : M →ₗ[A] M) : Prop where
  /-- `P ≤ T`.-/
  le : P ≤ T
  /-- `ker φ = im ψ` on `T/P`.-/
  exact_φ : T ⊓ P.comap φ = T.map ψ ⊔ P
  /-- `ker ψ = im φ` on `T/P`.-/
  exact_ψ : T ⊓ P.comap ψ = T.map φ ⊔ P

section periodic

variable {P S T : Submodule A M} {φ ψ : M →ₗ[A] M}

lemma PerExact.symm (h : PerExact P T φ ψ) : PerExact P T ψ φ := ⟨h.le, h.exact_ψ, h.exact_φ⟩

lemma PerExact.image_le (h : PerExact P T φ ψ) : T.map φ ⊔ P ≤ T :=
  h.exact_ψ ▸ inf_le_left

lemma PerExact.image_map_le (h : PerExact P T φ ψ) : (T.map φ ⊔ P).map ψ ⊔ P = P := by
  refine le_antisymm (sup_le ?_ le_rfl) le_sup_right
  rw [map_le_iff_le_comap, ← h.exact_ψ]
  exact inf_le_right

/-- Data computing `det_κ(T/P, φ, ψ)` as in Stacks Remark 42.68.14: lists `X, Y ⊆ T` such that
`φ X` resp. `ψ Y` are admissible sequences of `im φ` resp. `im ψ`.-/
def IsChoice (P T : Submodule A M) (φ ψ : M →ₗ[A] M) (X Y : List M) : Prop :=
  (∀ x ∈ X, x ∈ T) ∧ (∀ y ∈ Y, y ∈ T) ∧ Adm P (T.map φ ⊔ P) (X.map φ) ∧
    Adm P (T.map ψ ⊔ P) (Y.map ψ)

lemma IsChoice.symm {X Y : List M} (hc : IsChoice P T φ ψ X Y) : IsChoice P T ψ φ Y X :=
  ⟨hc.2.1, hc.1, hc.2.2.2, hc.2.2.1⟩

lemma IsChoice.adm_tail {X Y : List M} (h : PerExact P T φ ψ) (hc : IsChoice P T φ ψ X Y) :
    Adm (T.map φ ⊔ P) T Y :=
  adm_of_map ψ P hc.2.1 h.exact_ψ.le h.image_le (by rw [h.image_map_le]; exact hc.2.2.2)

lemma IsChoice.adm₁ {X Y : List M} (h : PerExact P T φ ψ) (hc : IsChoice P T φ ψ X Y) :
    Adm P T (X.map φ ++ Y) :=
  adm_append hc.2.2.1 (hc.adm_tail h)

lemma IsChoice.adm₂ {X Y : List M} (h : PerExact P T φ ψ) (hc : IsChoice P T φ ψ X Y) :
    Adm P T (Y.map ψ ++ X) :=
  hc.symm.adm₁ h.symm

lemma exists_choice [IsArtinian A M] [IsNoetherian A M] (_h : PerExact P T φ ψ) :
    ∃ X Y, IsChoice P T φ ψ X Y := by
  obtain ⟨l₁, hl₁, hl₁S⟩ := exists_adm_sub (T.map φ) (T.map φ ⊔ P) P le_sup_right le_rfl
  obtain ⟨l₂, hl₂, hl₂S⟩ := exists_adm_sub (T.map ψ) (T.map ψ ⊔ P) P le_sup_right le_rfl
  obtain ⟨X, rfl, hX⟩ := exists_lift φ T l₁ hl₁S
  obtain ⟨Y, rfl, hY⟩ := exists_lift ψ T l₂ hl₂S
  exact ⟨X, Y, hX, hY, hl₁, hl₂⟩

variable [IsArtinian A M] [IsNoetherian A M]

open Classical in
/-- **Stacks Definition 42.68.13**: the determinant `det_κ(T/P, φ, ψ) ∈ κ^*` of an exact
`(2,1)`-periodic complex of finite length, computed by Remark 42.68.14:
`[φX, Y] = (-1)^{|X||Y|} det_κ(T/P, φ, ψ) [ψY, X]`.  Junk value `1` if no choice exists.-/
noncomputable def perDet (P T : Submodule A M) (φ ψ : M →ₗ[A] M) : ResidueField A :=
  if h : ∃ XY : List M × List M, IsChoice P T φ ψ XY.1 XY.2 then
    (-1) ^ (h.choose.1.length * h.choose.2.length) *
      ratio P T (h.choose.1.map φ ++ h.choose.2) (h.choose.2.map ψ ++ h.choose.1)
  else 1

/-- The formula of Stacks Remark 42.68.14 holds for **every** choice.-/
theorem perDet_eq (h : PerExact P T φ ψ) {X Y : List M} (hc : IsChoice P T φ ψ X Y) :
    perDet P T φ ψ = (-1) ^ (X.length * Y.length) * ratio P T (X.map φ ++ Y) (Y.map ψ ++ X) := by
  have hex : ∃ XY : List M × List M, IsChoice P T φ ψ XY.1 XY.2 := ⟨(X, Y), hc⟩
  rw [perDet, dite_eq_left hex]
  have hc₀ := hex.choose_spec
  generalize hex.choose = XY at hc₀ ⊢
  obtain ⟨X₀, Y₀⟩ := XY
  dsimp only at hc₀ ⊢
  have hlx : X₀.length = X.length := by
    simpa using Adm.length_eq hc₀.2.2.1 hc.2.2.1
  have hly : Y₀.length = Y.length := by
    simpa using Adm.length_eq hc₀.2.2.2 hc.2.2.2
  rw [hlx, hly]
  congr 1
  -- compare the two choices
  have hK : (T.map φ ⊔ P).map ψ ⊔ P = P := h.image_map_le
  have hK' : (T.map ψ ⊔ P).map φ ⊔ P = P := h.symm.image_map_le
  have rY : ratio (T.map φ ⊔ P) T Y Y₀ = ratio P (T.map ψ ⊔ P) (Y.map ψ) (Y₀.map ψ) := by
    rw [ratio_map ψ P h.exact_ψ.le (hc.adm_tail h) (hc₀.adm_tail h), hK]
  have rX : ratio (T.map ψ ⊔ P) T X₀ X = ratio P (T.map φ ⊔ P) (X₀.map φ) (X.map φ) := by
    rw [ratio_map φ P h.exact_φ.le (hc₀.symm.adm_tail h.symm) (hc.symm.adm_tail h.symm), hK']
  have A1 : ratio P T (X.map φ ++ Y) (X₀.map φ ++ Y₀) =
      ratio P (T.map φ ⊔ P) (X.map φ) (X₀.map φ) * ratio P (T.map ψ ⊔ P) (Y.map ψ) (Y₀.map ψ) := by
    rw [ratio_append hc.2.2.1 hc₀.2.2.1 (hc.adm_tail h) (hc₀.adm_tail h), rY]
  have A2 : ratio P T (Y₀.map ψ ++ X₀) (Y.map ψ ++ X) =
      ratio P (T.map ψ ⊔ P) (Y₀.map ψ) (Y.map ψ) * ratio P (T.map φ ⊔ P) (X₀.map φ) (X.map φ) := by
    rw [ratio_append hc₀.2.2.2 hc.2.2.2 (hc₀.symm.adm_tail h.symm) (hc.symm.adm_tail h.symm), rX]
  have main : ratio P T (X.map φ ++ Y) (Y.map ψ ++ X) = ratio P T (X.map φ ++ Y) (X₀.map φ ++ Y₀) *
      (ratio P T (X₀.map φ ++ Y₀) (Y₀.map ψ ++ X₀) * ratio P T (Y₀.map ψ ++ X₀) (Y.map ψ ++ X)) := by
    rw [ratio_mul_ratio (hc₀.adm₂ h), ratio_mul_ratio (hc₀.adm₁ h)]
  have e1 := ratio_mul_ratio_symm hc.2.2.1 hc₀.2.2.1
  have e2 := ratio_mul_ratio_symm hc.2.2.2 hc₀.2.2.2
  rw [main, A1, A2]
  set R₀ := ratio P T (X₀.map φ ++ Y₀) (Y₀.map ψ ++ X₀)
  set a := ratio P (T.map φ ⊔ P) (X.map φ) (X₀.map φ)
  set a' := ratio P (T.map φ ⊔ P) (X₀.map φ) (X.map φ)
  set b := ratio P (T.map ψ ⊔ P) (Y.map ψ) (Y₀.map ψ)
  set b' := ratio P (T.map ψ ⊔ P) (Y₀.map ψ) (Y.map ψ)
  calc R₀ = R₀ * (a * a') * (b * b') := by rw [e1, e2]; ring
    _ = a * b * (R₀ * (b' * a')) := by ring

lemma neg_one_pow_mul_self (n : ℕ) : ((-1 : ResidueField A) ^ n) * (-1) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

lemma neg_one_pow_mul_self' (n : ℕ) : (-1 : ResidueField A) ^ (n * n) = (-1) ^ n := by
  rw [pow_mul]
  rcases neg_one_pow_eq_or (ResidueField A) n with h | h
  · rw [h, one_pow]
  · rw [h, h]

/-- `det_κ(T/P, φ, ψ) ∈ κ^*`.-/
theorem perDet_ne_zero (h : PerExact P T φ ψ) : perDet P T φ ψ ≠ 0 := by
  obtain ⟨X, Y, hc⟩ := exists_choice h
  rw [perDet_eq h hc]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
    (ratio_ne_zero (hc.adm₁ h) (hc.adm₂ h))

/-- **Stacks 42.68.15**: `det_κ(M, φ, ψ) · det_κ(M, ψ, φ) = 1`.-/
theorem perDet_mul_perDet_symm (h : PerExact P T φ ψ) :
    perDet P T φ ψ * perDet P T ψ φ = 1 := by
  obtain ⟨X, Y, hc⟩ := exists_choice h
  rw [perDet_eq h hc, perDet_eq h.symm hc.symm, mul_comm Y.length]
  calc (-1) ^ (X.length * Y.length) * ratio P T (X.map φ ++ Y) (Y.map ψ ++ X) *
        ((-1) ^ (X.length * Y.length) * ratio P T (Y.map ψ ++ X) (X.map φ ++ Y))
      = ((-1) ^ (X.length * Y.length) * (-1) ^ (X.length * Y.length)) *
        (ratio P T (X.map φ ++ Y) (Y.map ψ ++ X) * ratio P T (Y.map ψ ++ X) (X.map φ ++ Y)) := by
          ring
    _ = 1 := by rw [neg_one_pow_mul_self, ratio_mul_ratio_symm (hc.adm₁ h) (hc.adm₂ h), one_mul]

theorem perDet_symm (h : PerExact P T φ ψ) : perDet P T ψ φ = (perDet P T φ ψ)⁻¹ :=
  eq_inv_of_mul_eq_one_right (perDet_mul_perDet_symm h)

/-- **Stacks 42.68.16**: `det_κ(M, φ, φ) = (-1)^{length(im φ)}`.-/
theorem perDet_self (h : PerExact P T φ φ) {X : List M} (hX : Adm P (T.map φ ⊔ P) (X.map φ))
    (hXT : ∀ x ∈ X, x ∈ T) : perDet P T φ φ = (-1) ^ X.length := by
  have hc : IsChoice P T φ φ X X := ⟨hXT, hXT, hX, hX⟩
  rw [perDet_eq h hc, ratio_self (hc.adm₁ h), mul_one, neg_one_pow_mul_self']

/-- **Stacks 42.68.17 (1)**: `det_κ(M, φ, 0) = det_κ(φ)` (as a ratio `[φX]/[X]`).-/
theorem perDet_zero_right (h : PerExact P T φ 0) {X : List M} (hX : Adm P T (X.map φ))
    (hXT : ∀ x ∈ X, x ∈ T) : perDet P T φ 0 = ratio P T (X.map φ) X := by
  have hT : T.map φ ⊔ P = T := by
    rw [← h.exact_ψ, comap_zero, inf_top_eq]
  have hc : IsChoice P T φ 0 X [] := by
    refine ⟨hXT, by simp, by rw [hT]; exact hX, ?_⟩
    simp [Submodule.map_zero]
  rw [perDet_eq h hc]
  simp

/-- **Stacks 42.68.17 (2)**: `det_κ(M, 0, ψ) = det_κ(ψ)⁻¹`.-/
theorem perDet_zero_left (h : PerExact P T 0 ψ) {Y : List M} (hY : Adm P T (Y.map ψ))
    (hYT : ∀ y ∈ Y, y ∈ T) : perDet P T 0 ψ = (ratio P T (Y.map ψ) Y)⁻¹ := by
  rw [perDet_symm h.symm, perDet_zero_right h.symm hY hYT]

lemma perExact_unit_zero {u : A} (hu : IsUnit u) (hPT : P ≤ T) :
    PerExact P T (u • LinearMap.id) 0 := by
  have hc : P.comap (u • LinearMap.id) = P := by
    ext x; simp [P.smul_mem_iff_of_isUnit hu]
  have hm : T.map (u • LinearMap.id) = T := by
    refine le_antisymm (map_le_iff_le_comap.2 fun x hx => T.smul_mem u hx) fun x hx => ?_
    refine ⟨(hu.unit⁻¹ : Aˣ) • x, T.smul_mem _ hx, ?_⟩
    show u • ((hu.unit⁻¹ : Aˣ) : A) • x = x
    rw [smul_smul, hu.mul_val_inv, one_smul]
  refine ⟨hPT, ?_, ?_⟩
  · rw [hc, Submodule.map_zero, bot_sup_eq, inf_eq_right.2 hPT]
  · rw [comap_zero, inf_top_eq, hm, sup_eq_left.2 hPT]

/-- **Stacks 42.68.17 + 42.68.10**: for a unit `u`, `det_κ(T/P, u, 0) = ū ^ length(T/P)`.-/
theorem perDet_unit_zero {u : A} (hu : IsUnit u) {X : List M} (hX : Adm P T X) :
    perDet P T (u • LinearMap.id) 0 = residue A u ^ X.length := by
  have e : X.map (u • LinearMap.id : M →ₗ[A] M) = X.map (u • ·) := by
    rfl
  rw [perDet_zero_right (perExact_unit_zero hu hX.le) (by rw [e]; exact adm_smul_unit hu hX)
    hX.mem, e, ratio_smul_unit hu hX]

/-- The image sequence of a short exact sequence of exact periodic complexes is exact.-/
lemma inf_image_eq (h₁ : PerExact P S φ ψ) (h₂ : PerExact S T φ ψ) (h : PerExact P T φ ψ) :
    S ⊓ (T.map φ ⊔ P) = S.map φ ⊔ P := by
  refine le_antisymm ?_ (le_inf h₁.image_le (sup_le_sup_right (map_mono h₂.le) _))
  rintro z ⟨hzS, hz⟩
  obtain ⟨y, hy, p, hp, rfl⟩ := mem_sup.1 hz
  obtain ⟨t, ht, rfl⟩ := mem_map.1 hy
  have hφt : φ t ∈ S := by simpa using sub_mem hzS (h₁.le hp)
  have ht' : t ∈ T ⊓ S.comap φ := ⟨ht, hφt⟩
  rw [h₂.exact_φ] at ht'
  obtain ⟨y', hy', s, hs, rfl⟩ := mem_sup.1 ht'
  obtain ⟨t', ht'', rfl⟩ := mem_map.1 hy'
  have h1 : φ (ψ t') ∈ P := by
    have : ψ t' ∈ T ⊓ P.comap φ := by rw [h.exact_φ]; exact mem_sup_left (mem_map_of_mem ht'')
    exact this.2
  rw [map_add]
  exact add_mem (add_mem (mem_sup_right h1) (mem_sup_left (mem_map_of_mem hs))) (mem_sup_right hp)

lemma IsChoice.append {X₁ Y₁ X₃ Y₃ : List M} (h₁ : PerExact P S φ ψ) (h₂ : PerExact S T φ ψ)
    (h : PerExact P T φ ψ) (hc₁ : IsChoice P S φ ψ X₁ Y₁) (hc₃ : IsChoice S T φ ψ X₃ Y₃) :
    IsChoice P T φ ψ (X₁ ++ X₃) (Y₁ ++ Y₃) := by
  have step : ∀ {φ ψ : M →ₗ[A] M} {X₁ X₃ : List M}, PerExact P S φ ψ → PerExact S T φ ψ →
      PerExact P T φ ψ → Adm P (S.map φ ⊔ P) (X₁.map φ) → Adm S (T.map φ ⊔ S) (X₃.map φ) →
      (∀ x ∈ X₃, x ∈ T) → Adm P (T.map φ ⊔ P) ((X₁ ++ X₃).map φ) := by
    intro φ ψ X₁ X₃ h₁ h₂ h hX₁ hX₃ hX₃T
    rw [List.map_append]
    refine adm_append hX₁ ?_
    have := adm_inf (T.map φ ⊔ P) (fun v hv => ?_) hX₃
    · rwa [inf_image_eq h₁ h₂ h, inf_eq_right.2 (sup_le_sup_left h₁.le _)] at this
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
      exact mem_sup_left (mem_map_of_mem (hX₃T x hx))
  refine ⟨fun x hx => ?_, fun y hy => ?_, step h₁ h₂ h hc₁.2.2.1 hc₃.2.2.1 hc₃.1,
    step h₁.symm h₂.symm h.symm hc₁.2.2.2 hc₃.2.2.2 hc₃.2.1⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact h₂.le (hc₁.1 x hx)
    · exact hc₃.1 x hx
  · rcases List.mem_append.1 hy with hy | hy
    · exact h₂.le (hc₁.2.1 y hy)
    · exact hc₃.2.1 y hy

/-- **Stacks 42.68.18**: `det_κ` of exact periodic complexes is multiplicative in short exact
sequences `0 → (S/P) → (T/P) → (T/S) → 0`.-/
theorem perDet_mul (h₁ : PerExact P S φ ψ) (h₂ : PerExact S T φ ψ) (h : PerExact P T φ ψ) :
    perDet P T φ ψ = perDet P S φ ψ * perDet S T φ ψ := by
  obtain ⟨X₁, Y₁, hc₁⟩ := exists_choice h₁
  obtain ⟨X₃, Y₃, hc₃⟩ := exists_choice h₂
  have hc := hc₁.append h₁ h₂ h hc₃
  rw [perDet_eq h hc, perDet_eq h₁ hc₁, perDet_eq h₂ hc₃]
  have hA := hc.adm₁ h
  have hB := hc.adm₂ h
  have hY₁ : Adm (P ⊔ lspan A (X₁.map φ)) S Y₁ := by
    rw [hc₁.2.2.1.sup_lspan]; exact hc₁.adm_tail h₁
  have hX₁ : Adm (P ⊔ lspan A (Y₁.map ψ)) S X₁ := by
    rw [hc₁.2.2.2.sup_lspan]; exact hc₁.symm.adm_tail h₁.symm
  simp only [List.map_append] at hA hB
  have hA0 : Adm P T (X₁.map φ ++ X₃.map φ ++ Y₁ ++ Y₃) := by
    simpa only [List.append_assoc] using hA
  have hB0 : Adm P T (Y₁.map ψ ++ Y₃.map ψ ++ X₁ ++ X₃) := by
    simpa only [List.append_assoc] using hB
  have hB1 := (move_block (Y₃.map ψ) X₃ hX₁ hB0).1
  have m1 := ratio_move_block (l' := Y₁.map ψ ++ Y₃.map ψ ++ X₁ ++ X₃) hY₁ hA0
  have m2 := ratio_move_block (l' := Y₁.map ψ ++ Y₃.map ψ ++ X₁ ++ X₃) hX₁ hB0
  have f := ratio_append (hc₁.adm₁ h₁) (hc₁.adm₂ h₁) (hc₃.adm₁ h₂) (hc₃.adm₂ h₂)
  have mm := ratio_mul_ratio (P := P) (T := T) (l := X₁.map φ ++ Y₁ ++ X₃.map φ ++ Y₃)
    (l'' := Y₁.map ψ ++ Y₃.map ψ ++ X₁ ++ X₃) hB1
  rw [ratio_self hB0] at m2
  simp only [List.append_assoc, List.length_map] at m1 m2 f mm hB1
  simp only [List.map_append, List.append_assoc, List.length_append]
  -- `ratio B1 B0 = ε₂`
  have hε : ratio P T (Y₁.map ψ ++ (X₁ ++ (Y₃.map ψ ++ X₃))) (Y₁.map ψ ++ (Y₃.map ψ ++ (X₁ ++ X₃)))
      = (-1) ^ (Y₃.length * X₁.length) := by
    have := congrArg (fun z => (-1 : ResidueField A) ^ (Y₃.length * X₁.length) * z) m2
    simp only [mul_one, ← mul_assoc, neg_one_pow_mul_self, one_mul] at this
    exact this.symm
  rw [m1, ← mm, f, hε]
  have hsign : ((-1 : ResidueField A) ^ ((X₁.length + X₃.length) * (Y₁.length + Y₃.length))) *
      ((-1) ^ (X₃.length * Y₁.length) * (-1) ^ (Y₃.length * X₁.length)) =
      (-1) ^ (X₁.length * Y₁.length) * (-1) ^ (X₃.length * Y₃.length) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    have : (X₁.length + X₃.length) * (Y₁.length + Y₃.length) +
        (X₃.length * Y₁.length + Y₃.length * X₁.length) =
        X₁.length * Y₁.length + X₃.length * Y₃.length +
          2 * (X₃.length * Y₁.length + Y₃.length * X₁.length) := by ring
    rw [this, pow_add _ (X₁.length * Y₁.length + X₃.length * Y₃.length), pow_mul, neg_one_sq,
      one_pow, mul_one]
  set R₁ := ratio P S (X₁.map φ ++ Y₁) (Y₁.map ψ ++ X₁)
  set R₃ := ratio S T (X₃.map φ ++ Y₃) (Y₃.map ψ ++ X₃)
  calc _ = ((-1 : ResidueField A) ^ ((X₁.length + X₃.length) * (Y₁.length + Y₃.length)) *
        ((-1) ^ (X₃.length * Y₁.length) * (-1) ^ (Y₃.length * X₁.length))) * (R₁ * R₃) := by ring
    _ = ((-1) ^ (X₁.length * Y₁.length) * (-1) ^ (X₃.length * Y₃.length)) * (R₁ * R₃) := by
      rw [hsign]
    _ = _ := by ring

end periodic

/-! ### Exactness on the whole module, change of ambient module -/

section ambient

variable {φ ψ : M →ₗ[A] M}

lemma perExact_bot_top_iff :
    PerExact (⊥ : Submodule A M) ⊤ φ ψ ↔
      LinearMap.ker φ = LinearMap.range ψ ∧ LinearMap.ker ψ = LinearMap.range φ := by
  have e1 : ∀ f : M →ₗ[A] M, (⊤ : Submodule A M) ⊓ (⊥ : Submodule A M).comap f = LinearMap.ker f :=
    fun f => by rw [top_inf_eq]; rfl
  have e2 : ∀ f : M →ₗ[A] M, (⊤ : Submodule A M).map f ⊔ ⊥ = LinearMap.range f :=
    fun f => by rw [sup_bot_eq, LinearMap.range_eq_map]
  constructor
  · intro h; exact ⟨(e1 φ).symm.trans (h.exact_φ.trans (e2 ψ)),
      (e1 ψ).symm.trans (h.exact_ψ.trans (e2 φ))⟩
  · rintro ⟨h1, h2⟩
    exact ⟨bot_le, (e1 φ).trans (h1.trans (e2 ψ).symm), (e1 ψ).trans (h2.trans (e2 φ).symm)⟩

variable {M' : Type*} [AddCommGroup M'] [Module A M'] {P T : Submodule A M}

lemma map_exact_aux (g : M →ₗ[A] M') {φ' ψ' : M' →ₗ[A] M'} (hφ : g ∘ₗ φ = φ' ∘ₗ g)
    (hψ : g ∘ₗ ψ = ψ' ∘ₗ g) (hPT : P ≤ T) (hφT : T.map φ ≤ T)
    (he : T ⊓ P.comap φ = T.map ψ ⊔ P) (hg : T ⊓ (⊥ : Submodule A M').comap g ≤ P) :
    T.map g ⊓ (P.map g).comap φ' = (T.map g).map ψ' ⊔ P.map g := by
  have hm : (T.map g).map ψ' = (T.map ψ).map g := by
    rw [← Submodule.map_comp, ← Submodule.map_comp, hψ]
  rw [hm, ← Submodule.map_sup, ← he]
  refine le_antisymm ?_ (le_inf (map_mono inf_le_left) ?_)
  · rintro y ⟨hy, hy'⟩
    obtain ⟨t, ht, rfl⟩ := mem_map.1 hy
    obtain ⟨p, hp, hpe⟩ := mem_map.1 (show φ' (g t) ∈ P.map g from hy')
    have h1 : g (φ t) = g p := by
      rw [hpe]; exact (LinearMap.congr_fun hφ t)
    have h2 : φ t - p ∈ T ⊓ (⊥ : Submodule A M').comap g :=
      ⟨sub_mem (hφT (mem_map_of_mem ht)) (hPT hp), by simp [h1]⟩
    have h3 : φ t ∈ P := by simpa using add_mem (hg h2) hp
    exact mem_map_of_mem ⟨ht, h3⟩
  · rw [map_le_iff_le_comap]
    rintro t ⟨-, ht⟩
    show φ' (g t) ∈ P.map g
    rw [← LinearMap.comp_apply, ← hφ, LinearMap.comp_apply]
    exact mem_map_of_mem ht

lemma PerExact.map (g : M →ₗ[A] M') {φ' ψ' : M' →ₗ[A] M'} (hφ : g ∘ₗ φ = φ' ∘ₗ g)
    (hψ : g ∘ₗ ψ = ψ' ∘ₗ g) (h : PerExact P T φ ψ) (hg : T ⊓ (⊥ : Submodule A M').comap g ≤ P) :
    PerExact (P.map g) (T.map g) φ' ψ' :=
  ⟨map_mono h.le,
    map_exact_aux g hφ hψ h.le (le_sup_left.trans h.image_le) h.exact_φ hg,
    map_exact_aux g hψ hφ h.le (le_sup_left.trans h.symm.image_le) h.exact_ψ hg⟩

variable [IsArtinian A M] [IsNoetherian A M] [IsArtinian A M'] [IsNoetherian A M']

/-- `det_κ(M, φ, ψ)` is invariant under isomorphisms of periodic complexes, here: any linear map
`g` intertwining `(φ, ψ)` with `(φ', ψ')` and injective on `T/P`.-/
theorem perDet_map (g : M →ₗ[A] M') {φ' ψ' : M' →ₗ[A] M'} (hφ : g ∘ₗ φ = φ' ∘ₗ g)
    (hψ : g ∘ₗ ψ = ψ' ∘ₗ g) (h : PerExact P T φ ψ)
    (hg : T ⊓ (⊥ : Submodule A M').comap g ≤ P) :
    perDet (P.map g) (T.map g) φ' ψ' = perDet P T φ ψ := by
  obtain ⟨X, Y, hc⟩ := exists_choice h
  have h' := h.map g hφ hψ hg
  have hX : (X.map g).map φ' = (X.map φ).map g := by
    simp only [List.map_map]; congr 1; funext x
    exact (LinearMap.congr_fun hφ x).symm
  have hY : (Y.map g).map ψ' = (Y.map ψ).map g := by
    simp only [List.map_map]; congr 1; funext x
    exact (LinearMap.congr_fun hψ x).symm
  have himg : ∀ (f : M →ₗ[A] M) (f' : M' →ₗ[A] M'), g ∘ₗ f = f' ∘ₗ g →
      (T.map g).map f' ⊔ P.map g = (T.map f ⊔ P).map g := fun f f' hf => by
    rw [← Submodule.map_comp, ← hf, Submodule.map_comp, Submodule.map_sup]
  have hle : ∀ f : M →ₗ[A] M, T.map f ⊔ P ≤ T →
      (T.map f ⊔ P) ⊓ (⊥ : Submodule A M').comap g ≤ P :=
    fun f hf => (inf_le_inf_right _ hf).trans hg
  have hc' : IsChoice (P.map g) (T.map g) φ' ψ' (X.map g) (Y.map g) := by
    refine ⟨fun x hx => ?_, fun y hy => ?_, ?_, ?_⟩
    · obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hx; exact mem_map_of_mem (hc.1 x' hx')
    · obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy; exact mem_map_of_mem (hc.2.1 y' hy')
    · have := adm_map g ⊥ (hle φ h.image_le) hc.2.2.1
      rwa [sup_bot_eq, sup_bot_eq, ← himg φ φ' hφ, ← hX] at this
    · have := adm_map g ⊥ (hle ψ h.symm.image_le) hc.2.2.2
      rwa [sup_bot_eq, sup_bot_eq, ← himg ψ ψ' hψ, ← hY] at this
  rw [perDet_eq h' hc', perDet_eq h hc, ratio_map g ⊥ hg (hc.adm₁ h) (hc.adm₂ h), sup_bot_eq,
    sup_bot_eq, List.map_append, List.map_append, ← hX, ← hY, List.length_map, List.length_map]

/-- Transport along a linear equivalence of ambient modules.-/
theorem perDet_equiv (e : M ≃ₗ[A] M') {φ' ψ' : M' →ₗ[A] M'} (hφ : e.toLinearMap ∘ₗ φ = φ' ∘ₗ e)
    (hψ : e.toLinearMap ∘ₗ ψ = ψ' ∘ₗ e) (h : PerExact P T φ ψ) :
    perDet (P.map e.toLinearMap) (T.map e.toLinearMap) φ' ψ' = perDet P T φ ψ :=
  perDet_map e.toLinearMap hφ hψ h fun x hx => by
    have : e x = 0 := hx.2
    simp only [LinearEquiv.map_eq_zero_iff] at this
    rw [this]; exact zero_mem _

end ambient

/-! ### Lengths of admissible lists = lengths of modules -/

lemma covBy_sup_span {P : Submodule A M} {v : M} (hv : MKill P v) (hvP : v ∉ P) :
    P ⋖ P ⊔ A ∙ v := by
  refine ⟨lt_of_le_of_ne le_sup_left fun h => hvP (h ▸ self_mem_sup_span P v), fun R hPR hR => ?_⟩
  obtain ⟨w, hwR, hwP⟩ := SetLike.exists_of_lt hPR
  have := sup_span_eq_of_mem hv (hR.le hwR) hwP
  exact absurd (this ▸ sup_le hPR.le ((span_singleton_le_iff_mem _ _).2 hwR)) hR.not_ge

lemma Adm.exists_compositionSeries {T : Submodule A M} {l : List M} :
    ∀ {P : Submodule A M}, Adm P T l →
      ∃ s : CompositionSeries (Submodule A M), s.head = P ∧ s.last = T ∧ s.length = l.length := by
  induction l with
  | nil =>
    intro P h
    exact ⟨RelSeries.singleton _ P, RelSeries.head_singleton P,
      (RelSeries.last_singleton P).trans h, rfl⟩
  | cons v l ih =>
    intro P h
    obtain ⟨s, hs1, hs2, hs3⟩ := ih h.2.2.2
    refine ⟨s.cons P ?_, RelSeries.head_cons .., by rw [RelSeries.last_cons, hs2], ?_⟩
    · show P ⋖ s.head
      rw [hs1]; exact covBy_sup_span h.2.2.1 h.2.1
    · rw [RelSeries.cons_length, hs3, List.length_cons]

/-- An admissible list of `M = ⊤/⊥` has length `Module.length A M`.-/
theorem Adm.moduleLength_eq {l : List M} (h : Adm (⊥ : Submodule A M) ⊤ l) :
    Module.length A M = l.length := by
  obtain ⟨s, h1, h2, h3⟩ := h.exists_compositionSeries
  rw [← Module.length_compositionSeries s h1 h2, h3]

/-! ### Composition (Stacks 42.68.24) -/

section comp

variable [IsArtinian A M] [IsNoetherian A M]

lemma exists_image_adm (f : M →ₗ[A] M) (T P : Submodule A M) :
    ∃ X : List M, (∀ x ∈ X, x ∈ T) ∧ Adm P (T.map f ⊔ P) (X.map f) := by
  obtain ⟨l, hl, hlS⟩ := exists_adm_sub (T.map f) (T.map f ⊔ P) P le_sup_right le_rfl
  obtain ⟨X, rfl, hX⟩ := exists_lift f T l hlS
  exact ⟨X, hX, hl⟩

lemma map_comp_list (f g : M →ₗ[A] M) (l : List M) : (l.map g).map f = l.map (f ∘ₗ g) := by
  simp [List.map_map]

variable {α β γ : M →ₗ[A] M}

/-- **Stacks 42.68.24**: for endomorphisms `α, β, γ` with `α β = β α`, `α γ = γ α`, `β γ = γ β`
and `im α = ker βγ`, `ker α = im βγ`, `ker β = im αγ`, `im γ = ker αβ`:
`det_κ(M, α, βγ) = det_κ(im γ, α, β) · det_κ(M / ker β, α, γ)`.
(Here `im γ = [⊥, range γ]` and `M / ker β = [ker β, ⊤]` as subquotients of `M`.)-/
theorem perDet_comp (hαβ : α ∘ₗ β = β ∘ₗ α) (hαγ : α ∘ₗ γ = γ ∘ₗ α) (hβγ : β ∘ₗ γ = γ ∘ₗ β)
    (h1 : LinearMap.range α = LinearMap.ker (β ∘ₗ γ))
    (h2 : LinearMap.ker α = LinearMap.range (β ∘ₗ γ))
    (h4 : LinearMap.ker β = LinearMap.range (α ∘ₗ γ))
    (h5 : LinearMap.range γ = LinearMap.ker (α ∘ₗ β)) :
    perDet ⊥ ⊤ α (β ∘ₗ γ) =
      perDet ⊥ (LinearMap.range γ) α β * perDet (LinearMap.ker β) ⊤ α γ := by
  -- the three complexes are exact
  have hKβγ : LinearMap.ker β ≤ LinearMap.range γ := by
    rw [h4, hαγ]; exact LinearMap.range_comp_le_range _ _
  have hKβα : LinearMap.ker β ≤ LinearMap.range α := by
    rw [h4]; exact LinearMap.range_comp_le_range _ _
  have hKα : LinearMap.ker α ≤ LinearMap.range γ := by
    rw [h2, hβγ]; exact LinearMap.range_comp_le_range _ _
  have hD : PerExact (⊥ : Submodule A M) ⊤ α (β ∘ₗ γ) := perExact_bot_top_iff.2 ⟨h2, h1.symm⟩
  have hD₂ : PerExact (⊥ : Submodule A M) (LinearMap.range γ) α β := by
    refine ⟨bot_le, ?_, ?_⟩
    · rw [sup_bot_eq, ← LinearMap.range_comp]
      show LinearMap.range γ ⊓ LinearMap.ker α = _
      rw [inf_eq_right.2 hKα, h2]
    · rw [sup_bot_eq, ← LinearMap.range_comp]
      show LinearMap.range γ ⊓ LinearMap.ker β = _
      rw [inf_eq_right.2 hKβγ, h4]
  have hD₁ : PerExact (LinearMap.ker β) ⊤ α γ := by
    refine ⟨le_top, ?_, ?_⟩
    · rw [top_inf_eq, ← LinearMap.range_eq_map, sup_eq_left.2 hKβγ, h5, hαβ]
      rfl
    · rw [top_inf_eq, ← LinearMap.range_eq_map, sup_eq_left.2 hKβα, h1]
      rfl
  -- choices
  obtain ⟨x, -, hx⟩ := exists_image_adm (β ∘ₗ γ) ⊤ ⊥
  obtain ⟨y, -, hy⟩ := exists_image_adm (α ∘ₗ γ) ⊤ ⊥
  obtain ⟨z, -, hz⟩ := exists_image_adm (β ∘ₗ α) ⊤ ⊥
  rw [sup_bot_eq, ← LinearMap.range_eq_map] at hx hy hz
  have F1 : Adm ⊥ (LinearMap.ker β) ((y.map γ).map α) := by
    rw [map_comp_list, h4]; exact hy
  have hk : (LinearMap.ker β).map β = ⊥ := eq_bot_iff.2 (map_comap_le β ⊥)
  have F2 : Adm (LinearMap.ker β) (LinearMap.range α) (z.map α) := by
    refine adm_of_map β ⊥ (fun v hv => ?_) inf_le_right hKβα ?_
    · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hv; exact LinearMap.mem_range_self α w
    · rw [sup_bot_eq, sup_bot_eq, hk, ← LinearMap.range_comp,
        map_comp_list]
      exact hz
  have F3 : Adm (LinearMap.ker β) (LinearMap.range γ) (x.map γ) := by
    refine adm_of_map β ⊥ (fun v hv => ?_) inf_le_right hKβγ ?_
    · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hv; exact LinearMap.mem_range_self γ w
    · rw [sup_bot_eq, sup_bot_eq, hk, ← LinearMap.range_comp,
        map_comp_list]
      exact hx
  have hIα : (⊤ : Submodule A M).map α ⊔ LinearMap.ker β = LinearMap.range α := by
    rw [← LinearMap.range_eq_map, sup_eq_left.2 hKβα]
  have hIγ : (⊤ : Submodule A M).map γ ⊔ LinearMap.ker β = LinearMap.range γ := by
    rw [← LinearMap.range_eq_map, sup_eq_left.2 hKβγ]
  have C : IsChoice ⊥ ⊤ α (β ∘ₗ γ) (y.map γ ++ z) x := by
    refine ⟨by simp, by simp, ?_, ?_⟩
    · rw [sup_bot_eq, ← LinearMap.range_eq_map, List.map_append]
      exact adm_append F1 F2
    · rw [sup_bot_eq, ← LinearMap.range_eq_map]; exact hx
  have C₁ : IsChoice (LinearMap.ker β) ⊤ α γ z x := by
    refine ⟨by simp, by simp, ?_, ?_⟩
    · rw [hIα]; exact F2
    · rw [hIγ]; exact F3
  have C₂ : IsChoice ⊥ (LinearMap.range γ) α β (y.map γ) (x.map γ) := by
    refine ⟨fun v hv => ?_, fun v hv => ?_, ?_, ?_⟩
    · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hv; exact LinearMap.mem_range_self γ w
    · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hv; exact LinearMap.mem_range_self γ w
    · rw [sup_bot_eq, ← LinearMap.range_comp, ← h4]; exact F1
    · rw [sup_bot_eq, ← LinearMap.range_comp, map_comp_list]; exact hx
  have F4 : Adm (LinearMap.range γ) ⊤ z := by
    have := C₁.symm.adm_tail hD₁.symm
    rwa [hIγ] at this
  have hL : Adm ⊥ ⊤ ((y.map γ).map α ++ x.map γ ++ z) := adm_append (C₂.adm₁ hD₂) F4
  have e1 : ratio ⊥ ⊤ (((y.map γ).map α ++ z.map α) ++ x) ((y.map γ).map α ++ x.map γ ++ z) =
      ratio (LinearMap.ker β) ⊤ (z.map α ++ x) (x.map γ ++ z) := by
    rw [List.append_assoc, List.append_assoc]
    exact ratio_append_left F1 (C₁.adm₁ hD₁) (C₁.adm₂ hD₁)
  have e2 : ratio ⊥ ⊤ ((y.map γ).map α ++ x.map γ ++ z) ((x.map γ).map β ++ y.map γ ++ z) =
      ratio ⊥ (LinearMap.range γ) ((y.map γ).map α ++ x.map γ) ((x.map γ).map β ++ y.map γ) :=
    ratio_append_right F4 (C₂.adm₁ hD₂) (C₂.adm₂ hD₂)
  have hR : ratio ⊥ ⊤ ((y.map γ ++ z).map α ++ x) (x.map (β ∘ₗ γ) ++ (y.map γ ++ z)) =
      ratio (LinearMap.ker β) ⊤ (z.map α ++ x) (x.map γ ++ z) *
        ratio ⊥ (LinearMap.range γ) ((y.map γ).map α ++ x.map γ) ((x.map γ).map β ++ y.map γ) := by
    have l1 : (y.map γ ++ z).map α ++ x = ((y.map γ).map α ++ z.map α) ++ x := by
      rw [List.map_append]
    have l2 : x.map (β ∘ₗ γ) ++ (y.map γ ++ z) = (x.map γ).map β ++ y.map γ ++ z := by
      rw [map_comp_list, List.append_assoc]
    rw [l1, l2, ← ratio_mul_ratio hL, e1, e2]
  rw [perDet_eq hD C, hR, perDet_eq hD₁ C₁, perDet_eq hD₂ C₂]
  simp only [List.length_append, List.length_map]
  rw [add_mul, pow_add]
  ring

end comp

/-! ### Invariance under morphisms with equal boundary maps (Stacks 42.68.25, case `α₀ = α₁`) -/

section boundary

variable {M' : Type*} [AddCommGroup M'] [Module A M']

lemma top_map_sup_bot {N : Type*} [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) :
    (⊤ : Submodule A M).map f ⊔ ⊥ = LinearMap.range f := by
  rw [sup_bot_eq, LinearMap.range_eq_map]

variable {φ ψ : M →ₗ[A] M} {φ' ψ' : M' →ₗ[A] M'}

lemma bd_adm_g (g : M →ₗ[A] M') {T : Submodule A M} {l : List M}
    (hx : Adm (LinearMap.ker g) T l) : Adm ⊥ (T.map g) (l.map g) := by
  have := adm_map g ⊥ (inf_le_right : T ⊓ (⊥ : Submodule A M').comap g ≤ LinearMap.ker g) hx
  rwa [sup_bot_eq, sup_bot_eq, eq_bot_iff.2 (map_comap_le g ⊥)] at this

lemma bd_adm_w (g : M →ₗ[A] M') (hφ : g ∘ₗ φ = φ' ∘ₗ g)
    (h' : PerExact (⊥ : Submodule A M') ⊤ φ' ψ') (hQψ : LinearMap.range ψ' ≤ LinearMap.range g)
    {w : List M'} (hw : Adm (LinearMap.range g) ⊤ w) :
    Adm ((LinearMap.range φ).map g) (LinearMap.range φ') (w.map φ') := by
  obtain ⟨hkφ', -⟩ := perExact_bot_top_iff.1 h'
  have hgIφ : (LinearMap.range φ).map g = (LinearMap.range g).map φ' := by
    rw [← LinearMap.range_comp, ← LinearMap.range_comp, hφ]
  have hc : (⊤ : Submodule A M') ⊓ ((LinearMap.range φ).map g).comap φ' ≤ LinearMap.range g := by
    rintro x ⟨-, hx⟩
    rw [hgIφ] at hx
    obtain ⟨n, hn, hnx⟩ := mem_map.1 (show φ' x ∈ (LinearMap.range g).map φ' from hx)
    have : x - n ∈ LinearMap.ker φ' := by
      rw [LinearMap.mem_ker, map_sub, hnx, sub_self]
    rw [hkφ'] at this
    simpa using add_mem (hQψ this) hn
  have hle : (LinearMap.range φ).map g ≤ (⊤ : Submodule A M').map φ' := by
    rw [hgIφ]; exact map_mono le_top
  have := adm_map φ' ((LinearMap.range φ).map g) hc hw
  rwa [← hgIφ, sup_idem, sup_eq_left.2 hle, ← LinearMap.range_eq_map] at this

variable [IsArtinian A M] [IsNoetherian A M] [IsArtinian A M'] [IsNoetherian A M']

/-- One half of Stacks' proof of 42.68.25: the scalar `λ₀` comparing `φ' w` with `g z''` inside
`det_κ(im φ' / g(im φ))`, computed through the boundary map `ψ ∘ g⁻¹ ∘ φ'`.-/
lemma boundary_ratio (g : M →ₗ[A] M') (hφ : g ∘ₗ φ = φ' ∘ₗ g) (hψ : g ∘ₗ ψ = ψ' ∘ₗ g)
    (h : PerExact (⊥ : Submodule A M) ⊤ φ ψ) (h' : PerExact (⊥ : Submodule A M') ⊤ φ' ψ')
    (hKφ : LinearMap.ker g ≤ LinearMap.ker φ) (hKψ : LinearMap.ker g ≤ LinearMap.ker ψ)
    (hQφ : LinearMap.range φ' ≤ LinearMap.range g) (hQψ : LinearMap.range ψ' ≤ LinearMap.range g)
    {w Y : List M'} {z₀ z₀'' x₀ : List M} (hz₀ : Adm ⊥ (LinearMap.ker g) z₀)
    (hz'' : z₀''.map ψ = z₀) (hx : Adm (LinearMap.ker g) (LinearMap.range φ) (x₀.map φ))
    (hw : Adm (LinearMap.range g) ⊤ w) (hY : Adm (LinearMap.range φ') ⊤ (Y ++ w))
    (s₁ : M' → M) (hs₁ : ∀ x, g (s₁ x) = φ' x) :
    ratio ⊥ ⊤ ((x₀.map φ).map g ++ (w.map φ' ++ (Y ++ w)))
        ((x₀.map φ).map g ++ (z₀''.map g ++ (Y ++ w))) =
      ratio ⊥ (LinearMap.ker g) ((w.map s₁).map ψ) z₀ := by
  obtain ⟨hkφ, hkψ⟩ := perExact_bot_top_iff.1 h
  obtain ⟨hkφ', hkψ'⟩ := perExact_bot_top_iff.1 h'
  set Iφ := LinearMap.range φ
  set Tφ := (LinearMap.range φ').comap g
  have hgIφ : Iφ.map g = (LinearMap.range g).map φ' := by
    rw [← LinearMap.range_comp, ← LinearMap.range_comp, hφ]
  have hIT : Iφ ≤ Tφ := by
    rintro _ ⟨m, rfl⟩
    show g (φ m) ∈ LinearMap.range φ'
    rw [← LinearMap.comp_apply, hφ]; exact LinearMap.mem_range_self _ _
  have hKI : LinearMap.ker g ≤ Iφ := hKψ.trans hkψ.le
  have hcondT : Tφ ⊓ (⊥ : Submodule A M').comap g ≤ Iφ := inf_le_right.trans hKI
  have hTmap : Tφ.map g = LinearMap.range φ' := map_comap_eq_of_le hQφ
  have hIψ : Iφ.map ψ = ⊥ := by
    rw [← hkψ]; exact eq_bot_iff.2 (map_comap_le ψ ⊥)
  have hTψ : Tφ.map ψ = LinearMap.ker g := by
    refine le_antisymm ?_ fun k hk => ?_
    · rw [map_le_iff_le_comap]
      intro m hm
      have h1 : g m ∈ LinearMap.ker ψ' := by rw [hkψ']; exact hm
      show g (ψ m) = 0
      rw [← LinearMap.comp_apply, hψ, LinearMap.comp_apply]; exact h1
    · have hk' : k ∈ LinearMap.range ψ := by rw [← hkφ]; exact hKφ hk
      obtain ⟨m, rfl⟩ := hk'
      refine mem_map_of_mem ?_
      show g m ∈ LinearMap.range φ'
      rw [← hkψ']
      show ψ' (g m) = 0
      rw [← LinearMap.comp_apply, ← hψ, LinearMap.comp_apply]; exact hk
  -- `z₀''` is admissible in `[im φ, g⁻¹(im φ')]`
  have hz''T : Adm Iφ Tφ z₀'' := by
    refine adm_of_map ψ ⊥ (fun v hv => ?_) (inf_le_right.trans hkψ.le) hIT ?_
    · have hv' : ψ v ∈ LinearMap.ker g :=
        hz₀.mem _ (by rw [← hz'']; exact List.mem_map_of_mem hv)
      show g v ∈ LinearMap.range φ'
      rw [← hkψ']
      show ψ' (g v) = 0
      rw [← LinearMap.comp_apply, ← hψ, LinearMap.comp_apply]
      exact hv'
    · rw [hIψ, hTψ, bot_sup_eq, sup_bot_eq, hz'']; exact hz₀
  have hz''g : Adm (Iφ.map g) (LinearMap.range φ') (z₀''.map g) := by
    have := adm_map g ⊥ hcondT hz''T
    rwa [sup_bot_eq, sup_bot_eq, hTmap] at this
  have hwφ : Adm (Iφ.map g) (LinearMap.range φ') (w.map φ') := bd_adm_w g hφ h' hQψ hw
  have hxg : Adm ⊥ (Iφ.map g) ((x₀.map φ).map g) := bd_adm_g g hx
  have hws : (w.map s₁).map g = w.map φ' := by
    rw [List.map_map]; exact List.map_congr_left fun x _ => hs₁ x
  have hwsT : Adm Iφ Tφ (w.map s₁) := by
    refine adm_of_map g ⊥ (fun v hv => ?_) hcondT hIT ?_
    · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hv
      show g (s₁ x) ∈ LinearMap.range φ'
      rw [hs₁]; exact LinearMap.mem_range_self _ _
    · rw [sup_bot_eq, sup_bot_eq, hTmap, hws]; exact hwφ
  have e1 := ratio_map g ⊥ hcondT hwsT hz''T
  rw [sup_bot_eq, sup_bot_eq, hTmap, hws] at e1
  have e2 := ratio_map ψ ⊥ (inf_le_right.trans hkψ.le) hwsT hz''T
  rw [hIψ, hTψ, bot_sup_eq, sup_bot_eq, hz''] at e2
  rw [ratio_append_left hxg (adm_append hwφ hY) (adm_append hz''g hY),
    ratio_append_right hY hwφ hz''g, ← e1, e2]

/-- **Stacks 42.68.25** in the case `α₀ = α₁`: let `g : M → M'` be a morphism of exact
`(2,1)`-periodic complexes of finite length (`g φ = φ' g`, `g ψ = ψ' g`) such that `φ, ψ` vanish
on `ker g`, `φ', ψ'` vanish on `coker g` (`im φ', im ψ' ⊆ im g`), and the two boundary maps
`coker g → ker g` agree: `ψ m₁ = φ m₂` whenever `g m₁ = φ' m'` and `g m₂ = ψ' m'`.
Then `det_κ(M', φ', ψ') = det_κ(M, φ, ψ)`.-/
theorem perDet_eq_of_boundary (g : M →ₗ[A] M') (hφ : g ∘ₗ φ = φ' ∘ₗ g)
    (hψ : g ∘ₗ ψ = ψ' ∘ₗ g)
    (h : PerExact (⊥ : Submodule A M) ⊤ φ ψ) (h' : PerExact (⊥ : Submodule A M') ⊤ φ' ψ')
    (hKφ : LinearMap.ker g ≤ LinearMap.ker φ) (hKψ : LinearMap.ker g ≤ LinearMap.ker ψ)
    (hQφ : LinearMap.range φ' ≤ LinearMap.range g) (hQψ : LinearMap.range ψ' ≤ LinearMap.range g)
    (hbd : ∀ (m' : M') (m₁ m₂ : M), g m₁ = φ' m' → g m₂ = ψ' m' → ψ m₁ = φ m₂) :
    perDet ⊥ ⊤ φ' ψ' = perDet ⊥ ⊤ φ ψ := by
  obtain ⟨hkφ, hkψ⟩ := perExact_bot_top_iff.1 h
  have hKIφ : LinearMap.ker g ≤ LinearMap.range φ := hKψ.trans hkψ.le
  have hKIψ : LinearMap.ker g ≤ LinearMap.range ψ := hKφ.trans hkφ.le
  -- lists in `M`
  obtain ⟨z₀, hz₀⟩ := exists_adm (bot_le : (⊥ : Submodule A M) ≤ LinearMap.ker g)
  obtain ⟨z', hz', -⟩ := exists_lift φ ⊤ z₀ fun v hv => by
    rw [← LinearMap.range_eq_map]; exact hKIφ (hz₀.mem v hv)
  obtain ⟨z'', hz'', -⟩ := exists_lift ψ ⊤ z₀ fun v hv => by
    rw [← LinearMap.range_eq_map]; exact hKIψ (hz₀.mem v hv)
  obtain ⟨lx, hlx, hlxS⟩ := exists_adm_sub ((⊤ : Submodule A M).map φ) (LinearMap.range φ)
    (LinearMap.ker g) hKIφ (by rw [LinearMap.range_eq_map]; exact le_sup_left)
  obtain ⟨x₀, rfl, -⟩ := exists_lift φ ⊤ lx hlxS
  obtain ⟨ly, hly, hlyS⟩ := exists_adm_sub ((⊤ : Submodule A M).map ψ) (LinearMap.range ψ)
    (LinearMap.ker g) hKIψ (by rw [LinearMap.range_eq_map]; exact le_sup_left)
  obtain ⟨y₀, rfl, -⟩ := exists_lift ψ ⊤ ly hlyS
  -- a list in `M'` generating `coker g`, sections of `g` over `im φ'`, `im ψ'`
  obtain ⟨w, hw⟩ := exists_adm (le_top : LinearMap.range g ≤ ⊤)
  choose s₁ hs₁ using fun x => hQφ (LinearMap.mem_range_self φ' x)
  choose s₂ hs₂ using fun x => hQψ (LinearMap.mem_range_self ψ' x)
  -- the two choices
  have C : IsChoice ⊥ ⊤ φ ψ (z' ++ x₀) (z'' ++ y₀) := by
    refine ⟨by simp, by simp, ?_, ?_⟩
    · rw [top_map_sup_bot, List.map_append, hz']; exact adm_append hz₀ hlx
    · rw [top_map_sup_bot, List.map_append, hz'']; exact adm_append hz₀ hly
  have gφ : (x₀.map g).map φ' = (x₀.map φ).map g := by
    simp only [List.map_map]; congr 1; funext v; exact (LinearMap.congr_fun hφ v).symm
  have gψ : (y₀.map g).map ψ' = (y₀.map ψ).map g := by
    simp only [List.map_map]; congr 1; funext v; exact (LinearMap.congr_fun hψ v).symm
  have C' : IsChoice ⊥ ⊤ φ' ψ' (x₀.map g ++ w) (y₀.map g ++ w) := by
    refine ⟨by simp, by simp, ?_, ?_⟩
    · rw [top_map_sup_bot, List.map_append, gφ]
      exact adm_append (bd_adm_g g hlx) (bd_adm_w g hφ h' hQψ hw)
    · rw [top_map_sup_bot, List.map_append, gψ]
      exact adm_append (bd_adm_g g hly) (bd_adm_w g hψ h'.symm hQφ hw)
  -- the `M` side, transported to `[⊥, im g]` and then to `M'`
  have hA : Adm (⊥ : Submodule A _) ⊤ (z₀ ++ (x₀.map φ ++ (z'' ++ y₀))) := by
    have := C.adm₁ h; rwa [List.map_append, hz', List.append_assoc] at this
  have hB : Adm (⊥ : Submodule A _) ⊤ (z₀ ++ (y₀.map ψ ++ (z' ++ x₀))) := by
    have := C.adm₂ h; rwa [List.map_append, hz'', List.append_assoc] at this
  have tA : Adm (LinearMap.ker g) ⊤ (x₀.map φ ++ (z'' ++ y₀)) := by
    have := adm_append_right hA; rwa [hz₀.sup_lspan] at this
  have tB : Adm (LinearMap.ker g) ⊤ (y₀.map ψ ++ (z' ++ x₀)) := by
    have := adm_append_right hB; rwa [hz₀.sup_lspan] at this
  have hA₀ := bd_adm_g g tA
  have hB₀ := bd_adm_g g tB
  rw [← LinearMap.range_eq_map] at hA₀ hB₀
  have eM : ratio (⊥ : Submodule A _) ⊤ ((z' ++ x₀).map φ ++ (z'' ++ y₀)) ((z'' ++ y₀).map ψ ++ (z' ++ x₀)) =
      ratio (⊥ : Submodule A _) ⊤ ((x₀.map φ ++ (z'' ++ y₀)).map g ++ w) ((y₀.map ψ ++ (z' ++ x₀)).map g ++ w) := by
    rw [List.map_append, List.map_append, hz', hz'', List.append_assoc, List.append_assoc,
      ratio_append_left hz₀ tA tB, ratio_append_right hw hA₀ hB₀]
    have e := ratio_map g ⊥ (inf_le_right : (⊤ : Submodule A M) ⊓ (⊥ : Submodule A M').comap g ≤
      LinearMap.ker g) tA tB
    rwa [top_map_sup_bot, sup_bot_eq, eq_bot_iff.2 (map_comap_le g ⊥)] at e
  -- the `M'` side
  have hY : Adm (LinearMap.range φ') ⊤ (y₀.map g ++ w) := by
    have := C'.adm_tail h'; rwa [top_map_sup_bot] at this
  have hX : Adm (LinearMap.range ψ') ⊤ (x₀.map g ++ w) := by
    have := C'.symm.adm_tail h'.symm; rwa [top_map_sup_bot] at this
  have l₀ := boundary_ratio g hφ hψ h h' hKφ hKψ hQφ hQψ hz₀ hz'' hlx hw hY s₁ hs₁
  have l₁ := boundary_ratio g hψ hφ h.symm h'.symm hKψ hKφ hQψ hQφ hz₀ hz' hly hw hX s₂ hs₂
  have hlist : (w.map s₁).map ψ = (w.map s₂).map φ := by
    simp only [List.map_map]
    exact List.map_congr_left fun x _ => hbd x (s₁ x) (s₂ x) (hs₁ x) (hs₂ x)
  rw [hlist, ← l₁] at l₀
  -- assemble
  set A₁ := (x₀.map φ).map g ++ (w.map φ' ++ (y₀.map g ++ w))
  set A₀ := (x₀.map φ).map g ++ (z''.map g ++ (y₀.map g ++ w))
  set B₁ := (y₀.map ψ).map g ++ (w.map ψ' ++ (x₀.map g ++ w))
  set B₀ := (y₀.map ψ).map g ++ (z'.map g ++ (x₀.map g ++ w))
  have hA₁ : Adm (⊥ : Submodule A _) ⊤ A₁ := by
    have := C'.adm₁ h'; rwa [List.map_append, gφ, List.append_assoc] at this
  have hB₁ : Adm (⊥ : Submodule A _) ⊤ B₁ := by
    have := C'.adm₂ h'; rwa [List.map_append, gψ, List.append_assoc] at this
  have eA₀ : (x₀.map φ ++ (z'' ++ y₀)).map g ++ w = A₀ := by simp [A₀]
  have eB₀ : (y₀.map ψ ++ (z' ++ x₀)).map g ++ w = B₀ := by simp [B₀]
  rw [eA₀, eB₀] at eM
  have hA₀' : Adm (⊥ : Submodule A _) ⊤ A₀ := by rw [← eA₀]; exact adm_append hA₀ hw
  have hB₀' : Adm (⊥ : Submodule A _) ⊤ B₀ := by rw [← eB₀]; exact adm_append hB₀ hw
  have hlen : w.length = z₀.length := by
    have := Adm.length_eq hA₁ hA₀'
    simp only [A₁, A₀, List.length_append, List.length_map] at this
    rw [← hz'', List.length_map]; omega
  rw [perDet_eq h' C', perDet_eq h C, eM]
  have e3 : ratio (⊥ : Submodule A _) ⊤ ((x₀.map g ++ w).map φ' ++ (y₀.map g ++ w))
      ((y₀.map g ++ w).map ψ' ++ (x₀.map g ++ w)) =
      ratio (⊥ : Submodule A _) ⊤ A₁ A₀ * (ratio (⊥ : Submodule A _) ⊤ A₀ B₀ * ratio (⊥ : Submodule A _) ⊤ B₀ B₁) := by
    rw [ratio_mul_ratio hB₀', ratio_mul_ratio hA₀']
    congr 1 <;> simp [A₁, B₁, gφ, gψ]
  rw [e3, l₀]
  have e4 := ratio_mul_ratio_symm hB₁ hB₀'
  have hz'len : z'.length = z₀.length := by rw [← hz', List.length_map]
  have hz''len : z''.length = z₀.length := by rw [← hz'', List.length_map]
  simp only [List.length_append, List.length_map, hlen, hz'len, hz''len]
  calc _ = (-1) ^ ((x₀.length + z₀.length) * (y₀.length + z₀.length)) * ratio (⊥ : Submodule A _) ⊤ A₀ B₀ *
        (ratio (⊥ : Submodule A _) ⊤ B₁ B₀ * ratio (⊥ : Submodule A _) ⊤ B₀ B₁) := by ring
    _ = _ := by rw [e4]; ring

end boundary

end FinLenDet

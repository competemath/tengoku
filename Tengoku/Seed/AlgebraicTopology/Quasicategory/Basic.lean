/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# Quasicategories

In this file we define quasicategories,
a common model of infinity categories.
We show that every Kan complex is a quasicategory.

In `Mathlib/AlgebraicTopology/Quasicategory/Nerve.lean`,
we show that the nerve of a category is a quasicategory.

## TODO

- Generalize the definition to higher universes.
  See the corresponding TODO in
  `Mathlib/AlgebraicTopology/SimplicialSet/KanComplex.lean`.

-/

public section

namespace SSet

open CategoryTheory Simplicial

/-- A simplicial set `S` is a *quasicategory* if it satisfies the following horn-filling condition:
for every `n : ℕ` and `0 < i < n`,
every map of simplicial sets `σ₀ : Λ[n, i] → S` can be extended to a map `σ : Δ[n] → S`.
-/
@[kerodon 003A]
class Quasicategory (S : SSet) : Prop where
  hornFilling' : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n + 3)⦄ (σ₀ : (Λ[n + 2, i] : SSet) ⟶ S)
    (_h0 : 0 < i) (_hn : i < Fin.last (n + 2)),
      ∃ σ : Δ[n + 2] ⟶ S, σ₀ = Λ[n + 2, i].ι ≫ σ

/--
@isnad1 id=ex.2h4v.s8.cdf1cb05c99b from=seed src=0 shape=69f24228 vocab=41560610
-/
lemma Quasicategory.hornFilling {S : SSet} [Quasicategory S] ⦃n : ℕ⦄ ⦃i : Fin (n + 1)⦄
    (h0 : 0 < i) (hn : i < Fin.last n)
    (σ₀ : (Λ[n, i] : SSet) ⟶ S) : ∃ σ : Δ[n] ⟶ S, σ₀ = Λ[n, i].ι ≫ σ := by
  match n with
  | 0
  | 1 => lia
  | n + 2 => exact Quasicategory.hornFilling' σ₀ h0 hn

/-- Every Kan complex is a quasicategory. -/
@[kerodon 003C]
instance (S : SSet) [KanComplex S] : Quasicategory S where
  hornFilling' _ _ σ₀ _ _ := KanComplex.hornFilling σ₀

/--
@isnad1 id=quasicat.1h1v.s10.728f6e3961c0 from=seed src=0 shape=9173c678 vocab=b4755b34
-/
lemma quasicategory_of_filler (S : SSet)
    (filler : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n + 3)⦄ (σ₀ : (Λ[n + 2, i] : SSet) ⟶ S)
      (_h0 : 0 < i) (_hn : i < Fin.last (n + 2)),
      ∃ σ : S _⦋n + 2⦌, ∀ (j) (h : j ≠ i), S.δ j σ = σ₀.app _ (horn.face i j h)) :
    Quasicategory S where
  hornFilling' n i σ₀ h₀ hₙ := by
    obtain ⟨σ, h⟩ := filler σ₀ h₀ hₙ
    refine ⟨yonedaEquiv.symm σ, ?_⟩
    apply horn.hom_ext
    intro j hj
    rw [← h j hj, NatTrans.comp_app]
    rfl

/--
@isnad1 id=quasicat.1h3v.s7.6783a92389eb from=seed src=0 shape=7b796778 vocab=ba4ed07e
-/
lemma quasicategory_of_hasLiftingProperty (S : SSet) {X : SSet} (t : Limits.IsTerminal X)
    (h : ∀ {n : ℕ} {i : Fin (n + 1)} (_ : 0 < i) (_ : i < Fin.last n),
      HasLiftingProperty Λ[n, i].ι (t.from S)) :
    Quasicategory S where
  hornFilling' n i σ₀ h0 hn :=
    let := h h0 hn
    ⟨(CommSq.mk (t.hom_ext (σ₀ ≫ t.from S) (Λ[n + 2, i].ι ≫ t.from Δ[n + 2]))).lift, by simp⟩

/--
@isnad1 id=haslifti.2h5v.s7.830e526dcfe4 from=seed src=0 shape=b494b0d8 vocab=ba4ed07e
-/
lemma Quasicategory.hasLiftingProperty (S : SSet) [Quasicategory S] {X : SSet}
    (t : Limits.IsTerminal X) {n : ℕ} {i : Fin (n + 1)} (h0 : 0 < i) (hn : i < Fin.last n) :
    HasLiftingProperty Λ[n, i].ι (t.from S) where
  sq_hasLift _ :=
    ⟨(hornFilling h0 hn _).choose, (hornFilling h0 hn _).choose_spec.symm, t.hom_ext _ _⟩

/--
@isnad1 id=iff.0h3v.s7.f7c08bb4b6db from=seed src=0 shape=970b43e0 vocab=ba4ed07e
-/
lemma quasicategory_iff_hasLiftingProperty (S : SSet) {X : SSet} (t : Limits.IsTerminal X) :
    Quasicategory S ↔ ∀ {n : ℕ} {i : Fin (n + 1)} (_ : 0 < i) (_ : i < Fin.last n),
      HasLiftingProperty Λ[n, i].ι (t.from S) :=
  ⟨fun _ ↦ Quasicategory.hasLiftingProperty S t, quasicategory_of_hasLiftingProperty S t⟩

end SSet

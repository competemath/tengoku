/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Ramification.HilbertRamification.AbsoluteValueConjugacy
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Decomposition-group restriction law

This file gives the three tower-intersection formulas in their common ambient
Galois group.  The decomposition-group statement is formulated for arbitrary
absolute values, including the archimedean case.  The inertia and ramification
statements use valuation subrings and therefore cover the nonarchimedean case
in which those groups are defined.
-/

noncomputable section

universe u v w

namespace HilbertRamification

open AlgebraicNumberTheory.Valuations
open RamificationTheory.HilbertRamification.ValuationSubring

variable (K : Type u) {L : Type w} [Field K] [Field L] [Algebra K L]

/-- The decomposition group of an absolute-value class.  Membership says that pullback by the
automorphism preserves the strict unit ball, equivalently the valuation
class, rather than requiring equality of chosen absolute-value representatives.-/
def absoluteValueDecompositionGroup (w : AbsoluteValue L ℝ) :
    Subgroup (L ≃ₐ[K] L) where
  carrier := { σ | ∀ x : L, w (σ x) < 1 ↔ w x < 1 }
  one_mem' := by
    intro x
    rfl
  mul_mem' := by
    intro σ τ hσ hτ x
    exact (hσ (τ x)).trans (hτ x)
  inv_mem' := by
    intro σ hσ x
    have h := hσ (σ⁻¹ x)
    simpa using h.symm

@[simp] theorem mem_absoluteValueDecompositionGroup_iff
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) :
    σ ∈ absoluteValueDecompositionGroup K w ↔
      ∀ x : L, w (σ x) < 1 ↔ w x < 1 :=
  Iff.rfl

section IntermediateField

variable {M : Type v} [Field M] [Algebra K M] [Algebra M L]
  [IsScalarTower K M L]

/-- The decomposition-group restriction law, decomposition-group membership form: scalar restriction
does not change the action on the chosen valuation of `L`.-/
theorem decompositionGroupRestriction_mem_absoluteValueDecompositionGroup_restrictScalars_iff
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[M] L) :
    RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars (K := K) (M
      := M) σ ∈
        absoluteValueDecompositionGroup K w ↔
      σ ∈ absoluteValueDecompositionGroup M w :=
  Iff.rfl

/-- The decomposition-group restriction law, including the archimedean case:
inside `G(L/K)`, the decomposition group over `M` is
`G_w(L/K) ∩ G(L/M)`.-/
theorem decompositionGroupRestriction_absoluteValueDecompositionGroup_range_eq_inf
    (w : AbsoluteValue L ℝ) :
    Subgroup.map
        (RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars (K :=
          K) (M := M))
        (absoluteValueDecompositionGroup M w) =
      absoluteValueDecompositionGroup K w ⊓
        (RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars
          (K := K) (M := M)).range := by
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact
      ⟨(decompositionGroupRestriction_mem_absoluteValueDecompositionGroup_restrictScalars_iff
          (K := K) (M := M) w τ).mpr hτ,
        ⟨τ, rfl⟩⟩
  · rintro ⟨hσ, τ, rfl⟩
    exact
      ⟨τ,
        (decompositionGroupRestriction_mem_absoluteValueDecompositionGroup_restrictScalars_iff
          (K := K) (M := M) w τ).mp hσ,
        rfl⟩

end IntermediateField

namespace ValuationSubring

section NonarchimedeanIntermediateField

variable {M : Type v} [Field M] [Algebra K M] [Algebra M L]
  [IsScalarTower K M L]

end NonarchimedeanIntermediateField

end ValuationSubring

end HilbertRamification

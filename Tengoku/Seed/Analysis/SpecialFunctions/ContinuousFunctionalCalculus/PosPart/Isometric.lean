/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-! # Facts about `CFC.posPart` and `CFC.negPart` involving norms

This file collects various facts about the positive and negative parts of elements of a
C⋆-algebra that involve the norm.

## Main results

* `CFC.norm_eq_max_norm_posPart_negPart`: states that `‖a‖ = max ‖a⁺‖ ‖a⁻‖`
* `CFC.norm_posPart_le` and `CFC.norm_negPart_le`: state that `‖a⁺‖ ≤ ‖a‖` and `‖a⁻‖ ≤ ‖a‖`
  respectively.
-/

public section

variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℝ A] [SMulCommClass ℝ A A]
  [IsScalarTower ℝ A A] [StarRing A]
  [NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/--
@isnad1 id=le.0h2v.s8.5a2c8e33d063 from=seed src=0 shape=da004c69 vocab=83fe0722
-/
@[simp]
lemma CStarAlgebra.norm_posPart_le (a : A) : ‖a⁺‖ ≤ ‖a‖ := by
  by_cases ha : IsSelfAdjoint a
  case neg => simp [CFC.posPart_def, cfcₙ_apply_of_not_predicate a ha]
  refine norm_cfcₙ_le fun x hx ↦ ?_
  obtain (h | h) := le_or_gt x 0
  · simp [posPart_def, max_eq_right h]
  · simp only [posPart_def, max_eq_left h.le]
    exact NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le a hx ha

/--
@isnad1 id=le.0h2v.s8.d6e99a83439a from=seed src=0 shape=da004c69 vocab=173cf380
-/
@[simp]
lemma CStarAlgebra.norm_negPart_le (a : A) : ‖a⁻‖ ≤ ‖a‖ := by
  simpa [CFC.negPart_neg] using norm_posPart_le (-a)

open CStarAlgebra in
/--
@isnad1 id=eq.0h3v.s8.fc79d9f7370d from=seed src=0 shape=058e8dbd vocab=304c10a3
-/
lemma IsSelfAdjoint.norm_eq_max_norm_posPart_negPart (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    ‖a‖ = max ‖a⁺‖ ‖a⁻‖ := by
  refine le_antisymm ?_ <| max_le (norm_posPart_le a) (norm_negPart_le a)
  conv_lhs => rw [← cfcₙ_id' ℝ a]
  rw [norm_cfcₙ_le_iff ..]
  intro x hx
  obtain (hx' | hx') := le_total 0 x
  · apply le_max_of_le_left
    refine le_of_eq_of_le ?_ <| norm_apply_le_norm_cfcₙ _ a hx
    rw [posPart_eq_self.mpr hx']
  · apply le_max_of_le_right
    refine le_of_eq_of_le ?_ <| norm_apply_le_norm_cfcₙ _ a hx
    rw [negPart_eq_neg.mpr hx', norm_neg]

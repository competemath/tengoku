/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.CornerDensity
public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.CodeBound

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The first corner-fiber upper bound

The last-line slopes exceptional for the essential supremum have negligible
first-line preimage. Integrating the parallel-fiber bound therefore controls
corner-code density by the measure of its Borel positive first-line family.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/--
@isnad1 id=le.2h9v.s9.1ecac349a84c from=translated src=- shape=2a5bec6e vocab=69079aa3
-/
theorem cornerFirstDensity_le_parallelFiber {a b : ℝ} (hab : a ≠ b) (c κ : ℝ)
    {G : Set (Line m)} {D : Set (CornerCoordinates m)} (hDG : D ⊆ cornerFamily a b G)
    (z : EuclideanSpace ℝ (Fin m)) (g : Line m) :
    cornerFirstDensity a b c κ D z g ≤
      volume {x : EuclideanSpace ℝ (Fin m) | (x, (a - b)⁻¹ • (z - κ • atHeight c g)) ∈ G} := by
  refine (lintegral_mono (fun x ↦ ?_)).trans (lintegral_indicator_one_le _)
  dsimp only
  by_cases hx : cornerFromCode a b c κ g x z ∈ D
  · have h := (hDG hx).2.2
    rw [last_cornerFromCode hab] at h
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem
      (show x ∈ {x : EuclideanSpace ℝ (Fin m) | (x,
        (a - b)⁻¹ • (z - κ • atHeight c g)) ∈ G} from h)]
    exact le_rfl
  · simp [Set.indicator_of_notMem hx]

/--
@isnad1 id=eventual.3h8v.s9.7825051216fa from=translated src=- shape=822f8d5d vocab=4d56b3dc
-/
theorem cornerFirstDensity_ae_le_parallelMultiplicity {a b κ : ℝ} (hab : a ≠ b)
    (hκ : κ ≠ 0) (c : ℝ) {G : Set (Line m)} {D : Set (CornerCoordinates m)}
    (hDG : D ⊆ cornerFamily a b G) (z : EuclideanSpace ℝ (Fin m)) :
    ∀ᵐ g, cornerFirstDensity a b c κ D z g ≤ parallelMultiplicity G := by
  have h := ((quasiMeasurePreserving_codeSlope hab.symm hκ z).comp
    (quasiMeasurePreserving_atHeight c)).ae
      (ENNReal.ae_le_essSup (μ := (volume : Measure (EuclideanSpace ℝ (Fin m))))
        (fun ξ : EuclideanSpace ℝ (Fin m) ↦ volume {x : EuclideanSpace ℝ (Fin m) | (x, ξ) ∈ G}))
  exact h.mono fun g hg ↦ (cornerFirstDensity_le_parallelFiber hab c κ hDG z g).trans hg

/-- The corner density controls the size of a Borel first-line family on each code fiber.
@isnad1 id=le.4h8v.s9.5734b8e6d6d2 from=translated src=- shape=f77bd60d vocab=b689fec3
-/
theorem cornerDensity_le_positiveCornerFiber {a b κ : ℝ} (hab : a ≠ b) (hκ : κ ≠ 0) (c : ℝ)
    {G : Set (Line m)} {D : Set (CornerCoordinates m)} (hD : MeasurableSet D)
    (hDG : D ⊆ cornerFamily a b G) (z : EuclideanSpace ℝ (Fin m)) :
    cornerDensity a b c κ D z ≤ codeJacobian m a b ^ 2 *
      (parallelMultiplicity G * volume (positiveCornerFiber a b c κ D z)) := by
  rw [cornerDensity_eq_lintegral a b c κ hD]
  exact mul_le_mul le_rfl (lintegral_le_mul_measure_of_ae_le (Subset.rfl)
    (cornerFirstDensity_ae_le_parallelMultiplicity hab hκ c hDG z)) bot_le bot_le

/--
@isnad1 id=le.4h8v.s9.7e3b936ab47d from=translated src=- shape=f77bd60d vocab=477ecba6
-/
theorem cornerDensity_le_cornerFiber {a b κ : ℝ} (hab : a ≠ b) (hκ : κ ≠ 0) (c : ℝ)
    {G : Set (Line m)} {D : Set (CornerCoordinates m)} (hD : MeasurableSet D)
    (hDG : D ⊆ cornerFamily a b G) (z : EuclideanSpace ℝ (Fin m)) :
    cornerDensity a b c κ D z ≤ codeJacobian m a b ^ 2 *
      (parallelMultiplicity G * volume (cornerFiber a b c κ D z)) := by
  exact (cornerDensity_le_positiveCornerFiber hab hκ c hD hDG z).trans
    (mul_le_mul le_rfl (mul_le_mul le_rfl
      (measure_mono (positiveCornerFiber_subset a b c κ D z)) bot_le bot_le) bot_le bot_le)

end NKBesicovitch.Projection

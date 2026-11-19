/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.CornerMeasure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Corner-code density and its first-line fibers

The density is defined by the explicit inverse-coordinate integral, as in
equation (30) of the supplied manuscript. Its positive first-line fibers are
Borel for a Borel corner family, even when the existential image need not be.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- Unnormalized last-intercept mass on a first-line and corner-code fiber.-/
noncomputable def cornerFirstDensity (a b c κ : ℝ) (D : Set (CornerCoordinates m))
    (z : EuclideanSpace ℝ (Fin m)) (g : Line m) : ℝ≥0∞ :=
  ∫⁻ x, D.indicator 1 (cornerFromCode a b c κ g x z)

/-- The explicit corner-code density, including its inverse Jacobian.-/
noncomputable def cornerDensity (a b c κ : ℝ) (D : Set (CornerCoordinates m))
    (z : EuclideanSpace ℝ (Fin m)) : ℝ≥0∞ :=
  codeJacobian m a b ^ 2 * ∫⁻ p : Line m × EuclideanSpace ℝ (Fin m), D.indicator 1
    (cornerFromCode a b c κ p.1 p.2 z)

/-- First lines represented on a corner-code fiber.-/
def cornerFiber (a b c κ : ℝ) (D : Set (CornerCoordinates m)) (z : EuclideanSpace ℝ (Fin m)) :
    Set (Line m) :=
  {g | ∃ x, cornerFromCode a b c κ g x z ∈ D}

/-- First lines having positive last-intercept mass on the specified corner-code fiber.-/
noncomputable def positiveCornerFiber (a b c κ : ℝ) (D : Set (CornerCoordinates m))
    (z : EuclideanSpace ℝ (Fin m)) : Set (Line m) := Function.support
      (cornerFirstDensity a b c κ D z)

/--
@isnad1 id=measurab.1h7v.s8.a613bafd2ae1 from=translated src=- shape=b9a8884a vocab=9e14be29
-/
theorem measurable_cornerFirstDensity (a b c κ : ℝ) {D : Set (CornerCoordinates m)}
    (hD : MeasurableSet D) (z : EuclideanSpace ℝ (Fin m)) : Measurable
      (cornerFirstDensity a b c κ D z) := by
  have h : Measurable (fun p : Line m × EuclideanSpace ℝ (Fin m) ↦
      D.indicator (1 : CornerCoordinates m → ℝ≥0∞) (cornerFromCode a b c κ p.1 p.2 z)) :=
    (measurable_const.indicator hD).comp (by unfold cornerFromCode lineAt atHeight; fun_prop)
  exact h.lintegral_prod_right'

/--
@isnad1 id=measurab.1h7v.s8.ba354e4e7091 from=translated src=- shape=96f0d623 vocab=be168d63
-/
theorem measurableSet_positiveCornerFiber (a b c κ : ℝ) {D : Set (CornerCoordinates m)}
    (hD : MeasurableSet D) (z : EuclideanSpace ℝ (Fin m)) : MeasurableSet
      (positiveCornerFiber a b c κ D z) :=
  measurableSet_support (measurable_cornerFirstDensity a b c κ hD z)

/--
@isnad1 id=le.0h7v.s5.02921f524194 from=translated src=- shape=8078fc35 vocab=66545996
-/
theorem positiveCornerFiber_subset (a b c κ : ℝ) (D : Set (CornerCoordinates m))
    (z : EuclideanSpace ℝ (Fin m)) :
    positiveCornerFiber a b c κ D z ⊆ cornerFiber a b c κ D z := by
  intro g hg
  by_contra h
  have hx : ∀ x, cornerFromCode a b c κ g x z ∉ D := fun x hx ↦ h ⟨x, hx⟩
  exact hg (by simp [cornerFirstDensity, Set.indicator_of_notMem, hx])

/--
@isnad1 id=measurab.1h6v.s7.86faefcfb35b from=translated src=- shape=69d5fec2 vocab=2ad22921
-/
theorem measurable_cornerDensity (a b c κ : ℝ) {D : Set (CornerCoordinates m)}
    (hD : MeasurableSet D) : Measurable (cornerDensity a b c κ D) := by
  have h : Measurable (fun p : (Line m × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin m) ↦
      D.indicator (1 : CornerCoordinates m → ℝ≥0∞) (cornerFromCode a b c κ p.1.1 p.1.2 p.2)) :=
    (measurable_const.indicator hD).comp (by unfold cornerFromCode lineAt atHeight; fun_prop)
  exact measurable_const.mul h.lintegral_prod_left'

/--
@isnad1 id=eq.1h7v.s9.e3b7e037c2d1 from=translated src=- shape=4c6c48b6 vocab=d7a59924
-/
theorem cornerDensity_eq_lintegral (a b c κ : ℝ) {D : Set (CornerCoordinates m)}
    (hD : MeasurableSet D) (z : EuclideanSpace ℝ (Fin m)) :
    cornerDensity a b c κ D z =
      codeJacobian m a b ^ 2 * ∫⁻ g, cornerFirstDensity a b c κ D z g := by
  have h : Measurable (fun p : Line m × EuclideanSpace ℝ (Fin m) ↦
      D.indicator (1 : CornerCoordinates m → ℝ≥0∞) (cornerFromCode a b c κ p.1 p.2 z)) :=
    (measurable_const.indicator hD).comp (by unfold cornerFromCode lineAt atHeight; fun_prop)
  unfold cornerDensity cornerFirstDensity
  rw [Measure.volume_eq_prod, lintegral_prod _ h.aemeasurable]

/--
@isnad1 id=eq.2h6v.s10.6ed20c6e7383 from=translated src=- shape=9e035b1b vocab=21e4cac1
-/
theorem lintegral_cornerDensity {a b : ℝ} (hab : a ≠ b) (c κ : ℝ)
    {D : Set (CornerCoordinates m)} (hD : MeasurableSet D) :
    (∫⁻ z, cornerDensity a b c κ D z) = volume D := by
  let f : (Line m × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin m) → ℝ≥0∞ := fun p ↦
    D.indicator 1 (cornerFromCode a b c κ p.1.1 p.1.2 p.2)
  have hf : Measurable f :=
    (measurable_const.indicator hD).comp (by unfold cornerFromCode lineAt atHeight; fun_prop)
  have hi := (measurePreserving_cornerCodeCoordinates_assoc (m := m) hab c κ).lintegral_comp hf
  calc
    _ = codeJacobian m a b ^ 2 * ∫⁻ z, ∫⁻ p, f (p, z) :=
      lintegral_const_mul _ hf.lintegral_prod_left'
    _ = codeJacobian m a b ^ 2 * ∫⁻ p, f p := by
      congr 1
      simpa only [Measure.volume_eq_prod] using
        (lintegral_prod_symm' (μ := (volume : Measure (Line m × EuclideanSpace ℝ (Fin m))))
          (ν := (volume : Measure (EuclideanSpace ℝ (Fin m)))) f hf).symm
    _ = ∫⁻ p, f p ∂(codeJacobian m a b ^ 2 • volume) := by
      rw [lintegral_smul_measure, smul_eq_mul]
    _ = ∫⁻ p, D.indicator 1 p := by
      rw [← hi]
      apply lintegral_congr
      intro p
      dsimp only [f]
      rw [cornerFromCode_cornerCode hab]
    _ = volume D := lintegral_indicator_one hD

/--
@isnad1 id=iff.1h8v.s6.55c8c9bb30ef from=translated src=- shape=52832b3a vocab=3229d3af
-/
theorem mem_cornerFiber_iff {a b : ℝ} (hab : a ≠ b) (c κ : ℝ)
    (D : Set (CornerCoordinates m)) (g : Line m) (z : EuclideanSpace ℝ (Fin m)) :
    g ∈ cornerFiber a b c κ D z ↔
      ∃ p ∈ D, cornerFirst a p = g ∧ cornerCode a b c κ p = z := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨cornerFromCode a b c κ g x z, hx, first_cornerFromCode a b c κ g x z,
      cornerCode_cornerFromCode hab c κ g x z⟩
  · rintro ⟨p, hp, rfl, rfl⟩
    refine ⟨(cornerLast b p).1, ?_⟩
    rwa [cornerFromCode_cornerCode hab]

/--
@isnad1 id=le.1h8v.s5.c4228132c208 from=translated src=- shape=1a0273b9 vocab=767578cb
-/
theorem cornerFiber_subset (a b c κ : ℝ) {G : Set (Line m)} {D : Set (CornerCoordinates m)}
    (hDG : D ⊆ cornerFamily a b G) (z : EuclideanSpace ℝ (Fin m)) :
      cornerFiber a b c κ D z ⊆ G := by
  rintro g ⟨x, hx⟩
  have h := (hDG hx).1
  rwa [first_cornerFromCode] at h

end NKBesicovitch.Projection

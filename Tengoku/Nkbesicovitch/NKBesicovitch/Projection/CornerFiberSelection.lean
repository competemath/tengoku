/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.CornerFiberBound
public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.FiberSelection
public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.BoundedFamilies

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Retaining corner density on one code fiber

Corner densities are monotone in the corner family. A refinement retaining
half the total mass therefore retains half the density on some positive
code fiber. Boundedness gives finite masses and finite pointwise densities.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/--
@isnad1 id=le.1h8v.s5.f2661d1cda83 from=translated src=- shape=7d22b1d9 vocab=9db0ee43
-/
theorem cornerFiber_mono (a b c κ : ℝ) {D₀ D₁ : Set (CornerCoordinates m)}
    (hD : D₁ ⊆ D₀) (z : EuclideanSpace ℝ (Fin m)) :
    cornerFiber a b c κ D₁ z ⊆ cornerFiber a b c κ D₀ z := by
  rintro g ⟨x, hx⟩
  exact ⟨x, hD hx⟩

/--
@isnad1 id=le.1h7v.s6.d31eb7dc3b7f from=translated src=- shape=73eabfbe vocab=36320e8c
-/
theorem cornerDensity_mono (a b c κ : ℝ) {D₀ D₁ : Set (CornerCoordinates m)}
    (hD : D₁ ⊆ D₀) : cornerDensity a b c κ D₁ ≤ cornerDensity a b c κ D₀ := by
  intro z
  apply mul_le_mul le_rfl _ bot_le bot_le
  apply lintegral_mono
  intro p
  exact indicator_le_indicator_of_subset hD (fun _ ↦ bot_le) _

/--
@isnad1 id=isbounde.1h4v.s7.29a8f77a8533 from=translated src=- shape=f185822b vocab=e1b10f37
-/
theorem isBounded_cornerFamily (a b : ℝ) {G : Set (Line m)} (hG : IsBounded G) :
    IsBounded (cornerFamily a b G) := by
  apply (hG.prod (hG.image_snd.prod hG.image_snd)).subset
  intro p hp
  exact ⟨hp.2.1, ⟨cornerFirst a p, hp.1, rfl⟩, ⟨cornerLast b p, hp.2.2, rfl⟩⟩

/--
@isnad1 id=ne.1h4v.s10.cc09b73fbe85 from=translated src=- shape=1c11ba45 vocab=5b298b2c
-/
theorem volume_cornerFamily_ne_top (a b : ℝ) {G : Set (Line m)} (hG : IsBounded G) :
    volume (cornerFamily a b G) ≠ ∞ := (isBounded_cornerFamily a b hG).measure_lt_top.ne

/--
@isnad1 id=ne.5h8v.s8.179b96c6c400 from=translated src=- shape=a435e8d8 vocab=25bd5940
-/
theorem cornerDensity_ne_top {a b κ : ℝ} (hab : a ≠ b) (hκ : κ ≠ 0) (c : ℝ)
    {G : Set (Line m)} {D : Set (CornerCoordinates m)} (hD : MeasurableSet D)
    (hDG : D ⊆ cornerFamily a b G) (hG : IsBounded G) (z : EuclideanSpace ℝ (Fin m)) :
    cornerDensity a b c κ D z ≠ ∞ := by
  have hF : volume (cornerFiber a b c κ D z) ≠ ∞ :=
    (hG.subset (cornerFiber_subset a b c κ hDG z)).measure_lt_top.ne
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top (codeJacobian_ne_top m a b))
      (ENNReal.mul_ne_top (parallelMultiplicity_ne_top hG) hF))
    (cornerDensity_le_cornerFiber hab hκ c hD hDG z)

/-- Half the total mass yields half the original density on a positive corner-code fiber.
@isnad1 id=ex.7h7v.s12.a013c47fa1d6 from=translated src=- shape=b063af22 vocab=d3a16584
-/
theorem exists_good_corner_code {a b : ℝ} (hab : a ≠ b) (c κ : ℝ)
    {D₀ D₁ : Set (CornerCoordinates m)} (hD₀ : MeasurableSet D₀) (hD₁ : MeasurableSet D₁)
    (hD : D₁ ⊆ D₀) (hpos : 0 < volume D₀) (hfin : volume D₀ ≠ ∞)
    (hmass : volume D₀ ≤ 2 * volume D₁) :
    ∃ z, 0 < cornerDensity a b c κ D₀ z ∧
      cornerDensity a b c κ D₀ z ≤ 2 * cornerDensity a b c κ D₁ z := by
  apply exists_pos_le_mul_of_lintegral_le (measurable_cornerDensity a b c κ hD₁)
    (measurable_cornerDensity a b c κ hD₀) (cornerDensity_mono a b c κ hD)
  · rwa [lintegral_cornerDensity hab c κ hD₀]
  · rwa [lintegral_cornerDensity hab c κ hD₀]
  · simpa only [lintegral_cornerDensity hab c κ hD₀, lintegral_cornerDensity hab c κ hD₁]
      using hmass

end NKBesicovitch.Projection

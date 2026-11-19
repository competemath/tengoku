/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.CodeDensity
public import Tengoku.Seed.MeasureTheory.Integral.Lebesgue.Markov

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Selecting a code fiber after refinement

A refinement retaining a fixed fraction of the total pair mass retains at
least that fraction on some code fiber of positive density. The finite-mass
assumption is explicit, so the averaging argument cannot compare two infinities.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/--
@isnad1 id=ex.6h5v.s7.db09e84eef25 from=translated src=- shape=b82c9887 vocab=2a9ce756
-/
theorem exists_pos_le_mul_of_lintegral_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f g : X → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfg : f ≤ g) (hpos : 0 < ∫⁻ x, g x ∂μ) (hfin : (∫⁻ x, g x ∂μ) ≠ ∞)
    (c : ℝ≥0∞) (havg : (∫⁻ x, g x ∂μ) ≤ c * ∫⁻ x, f x ∂μ) :
    ∃ x, 0 < g x ∧ g x ≤ c * f x := by
  by_contra h
  have hlt (x : X) (hx : 0 < g x) : c * f x < g x :=
    lt_of_not_ge (fun hle ↦ h ⟨x, hx, hle⟩)
  have hle (x : X) : c * f x ≤ g x := by
    rcases eq_or_lt_of_le (bot_le : 0 ≤ g x) with hx | hx
    · have hf0 : f x = 0 := le_antisymm ((hfg x).trans_eq hx.symm) bot_le
      simp [hf0, ← hx]
    · exact (hlt x hx).le
  have hfi : (∫⁻ x, c * f x ∂μ) ≠ ∞ :=
    ne_top_of_le_ne_top hfin (lintegral_mono hle)
  have hs : μ (Function.support g) ≠ 0 := (lintegral_pos_iff_support hg).mp hpos |>.ne'
  have hi := lintegral_strict_mono_of_ae_le_of_ae_lt_on hg.aemeasurable hfi
    (ae_of_all _ hle) hs (ae_of_all _ fun x hx ↦ hlt x (pos_iff_ne_zero.mpr hx))
  rw [lintegral_const_mul c hf] at hi
  exact (not_lt_of_ge havg) hi

/--
@isnad1 id=le.1h7v.s5.5dedb7ae7df4 from=translated src=- shape=1c068a38 vocab=3bc3c8e4
-/
theorem pairFiber_mono (a b c : ℝ) {W₀ W₁ : Set (PairCoordinates m)}
    (hW : W₁ ⊆ W₀) (z : EuclideanSpace ℝ (Fin m)) : pairFiber a b c W₁ z ⊆ pairFiber a b c W₀ z :=
  fun _ hg ↦ hW hg

/--
@isnad1 id=le.1h7v.s5.d8a6dfde616c from=translated src=- shape=4727d226 vocab=364ef99c
-/
theorem pairFiber_subset (a b c : ℝ) {G : Set (Line m)} {W : Set (PairCoordinates m)}
    (hWG : W ⊆ pairFamily a G) (z : EuclideanSpace ℝ (Fin m)) : pairFiber a b c W z ⊆ G := by
  intro g hg
  have h := (hWG hg).1
  rwa [first_pairFromCode] at h

/--
@isnad1 id=le.1h6v.s5.694b95b0d2fd from=translated src=- shape=68e5c05c vocab=baf3d129
-/
theorem codeDensity_mono (a b c : ℝ) {W₀ W₁ : Set (PairCoordinates m)}
    (hW : W₁ ⊆ W₀) : codeDensity a b c W₁ ≤ codeDensity a b c W₀ := by
  intro z
  exact mul_le_mul le_rfl (measure_mono (pairFiber_mono a b c hW z)) bot_le bot_le

/-- Retaining half the pair mass retains half the density on some positive code fiber.
@isnad1 id=ex.7h6v.s11.4f49c9b26d58 from=translated src=- shape=1fd9a689 vocab=64da5946
-/
theorem exists_good_code {a b : ℝ} (hab : a ≠ b) (c : ℝ)
    {W₀ W₁ : Set (PairCoordinates m)} (hW₀ : MeasurableSet W₀) (hW₁ : MeasurableSet W₁)
    (hW : W₁ ⊆ W₀) (hpos : 0 < volume W₀) (hfin : volume W₀ ≠ ∞)
    (hmass : volume W₀ ≤ 2 * volume W₁) :
    ∃ z, 0 < codeDensity a b c W₀ z ∧ codeDensity a b c W₀ z ≤ 2 * codeDensity a b c W₁ z := by
  apply exists_pos_le_mul_of_lintegral_le (measurable_codeDensity a b c hW₁)
    (measurable_codeDensity a b c hW₀) (codeDensity_mono a b c hW)
  · rwa [lintegral_codeDensity hab c hW₀]
  · rwa [lintegral_codeDensity hab c hW₀]
  · simpa only [lintegral_codeDensity hab c hW₀, lintegral_codeDensity hab c hW₁] using hmass

end NKBesicovitch.Projection

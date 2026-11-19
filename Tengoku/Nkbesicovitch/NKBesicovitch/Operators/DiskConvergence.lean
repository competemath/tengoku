/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.DiskMeasurability
public import Tengoku.Seed.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Continuity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Passing disk estimates to bounded pointwise limits

Dominated convergence applies on each individual disk. Taking the supremum
over centers gives a lower bound by the liminf of the maxima; Fatou's lemma
then passes a uniform integral estimate to the limiting function.
-/

public section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NKBesicovitch

variable {n k : ℕ} {f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
  {g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}

/-- Uniformly bounded pointwise convergence implies convergence of each disk average.
@isnad1 id=tendsto.3h6v.s7.720976ff989c from=translated src=- shape=e2403e02 vocab=a6e31991
-/
theorem tendsto_diskAverage_of_bounded (hf : ∀ j, Measurable (f j))
    (hb : ∀ j x, f j x ≤ 1) (hg : ∀ x, Tendsto (fun j ↦ f j x) atTop (𝓝 (g x)))
    (V : Grassmannian n k) (a : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun j ↦ diskAverage (f j) V a) atTop (𝓝 (diskAverage g V a)) := by
  have h := tendsto_lintegral_of_dominated_convergence
    (μ := volume.restrict (closedBall (0 : V.val) 1)) (fun _ ↦ (1 : ℝ≥0∞))
    (fun j ↦ (hf j).comp (continuous_const.add continuous_subtype_val).measurable)
    (fun j ↦ ae_of_all _ fun w ↦ hb j (a + w))
    (by simpa only [lintegral_const, one_mul, Measure.restrict_apply_univ]
      using (measure_closedBall_lt_top (x := (0 : V.val)) (r := 1)).ne)
    (ae_of_all _ fun w ↦ hg (a + w))
  exact (ENNReal.continuous_div_const _
    (measure_closedBall_pos volume _ zero_lt_one).ne').continuousAt.tendsto.comp h

/--
@isnad1 id=le.4h6v.s7.d436409d7a6d from=translated src=- shape=3e92ab0e vocab=075986e1
-/
theorem diskMaximal_rpow_le_liminf_of_tendsto (hf : ∀ j, Measurable (f j))
    (hb : ∀ j x, f j x ≤ 1) (hg : ∀ x, Tendsto (fun j ↦ f j x) atTop (𝓝 (g x)))
    {p : ℝ} (hp : 0 < p) (V : Grassmannian n k) :
    diskMaximal g V ^ p ≤ liminf (fun j ↦ diskMaximal (f j) V ^ p) atTop := by
  rw [← ENNReal.le_rpow_inv_iff hp]
  apply iSup_le
  intro a
  rw [ENNReal.le_rpow_inv_iff hp]
  have ht := (ENNReal.continuous_rpow_const (y := p)).continuousAt.tendsto.comp
    (tendsto_diskAverage_of_bounded hf hb hg V a)
  rw [← ht.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun j ↦
    ENNReal.rpow_le_rpow (le_iSup (fun a ↦ diskAverage (f j) V a) a) hp.le)

end NKBesicovitch

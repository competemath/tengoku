/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.W1p.Basic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import Tengoku

/-!
# The ball Poincare inequality for representative-level `W^{1,p}` functions

The proof uses interior mollification on compactly contained balls and then
exhausts the original ball.
-/

@[expose] public section

open Function Set Filter MeasureTheory Topology
open scoped ENNReal Convolution Pointwise

namespace CKN

noncomputable section
/--
@isnad1 id=eq.3h3v.s7.fe784ff0e13f from=translated src=- shape=357be06e vocab=923bce98
-/
lemma integral_rpow_norm_eq_lpNorm_rpow
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    {f : Vec 3 → ℝ} {μ : Measure (Vec 3)} (hf : MemLp f p μ) :
    (∫ x, ‖f x‖ ^ p.toReal ∂μ) = lpNorm f p μ ^ p.toReal := by
  rw [lpNorm_eq_integral_norm_rpow_toReal hp0 hpTop hf.aestronglyMeasurable]
  exact (Real.rpow_inv_rpow (integral_nonneg_of_ae
    (Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _))
    (ENNReal.toReal_ne_zero.mpr ⟨hp0, hpTop⟩)).symm

/--
@isnad1 id=tendsto.5h4v.s8.afa5a2026381 from=translated src=- shape=853bd015 vocab=52973c4b
-/
lemma tendsto_integral_rpow_norm_of_tendsto_lpNorm
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    {f : Vec 3 → ℝ} {μ : Measure (Vec 3)} (hf : MemLp f p μ)
    {g : ℕ → Vec 3 → ℝ} (hg : ∀ n, MemLp (g n) p μ)
    (hconv : Tendsto (fun n => lpNorm (g n) p μ) atTop
    (nhds (lpNorm f p μ))) :
    Tendsto (fun n => ∫ x, ‖g n x‖ ^ p.toReal ∂μ) atTop
      (nhds (∫ x, ‖f x‖ ^ p.toReal ∂μ)) := by
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  have hpow : Tendsto (fun n => lpNorm (g n) p μ ^ p.toReal) atTop
      (nhds (lpNorm f p μ ^ p.toReal)) := by
    have hpair : Tendsto (fun n => (lpNorm (g n) p μ, p.toReal)) atTop
        (nhds (lpNorm f p μ, p.toReal)) := by
      simpa only [nhds_prod_eq] using hconv.prodMk
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => p.toReal) atTop
          (nhds p.toReal))
    exact (Real.continuousAt_rpow_of_pos (lpNorm f p μ, p.toReal) hp_pos).tendsto.comp
      hpair
  have hfun :
      (fun n => ∫ x, ‖g n x‖ ^ p.toReal ∂μ) =
        (fun n => lpNorm (g n) p μ ^ p.toReal) := by
    funext n
    exact integral_rpow_norm_eq_lpNorm_rpow hp0 hpTop (hg n)
  have htarget :
      (∫ x, ‖f x‖ ^ p.toReal ∂μ) = lpNorm f p μ ^ p.toReal :=
    integral_rpow_norm_eq_lpNorm_rpow hp0 hpTop hf
  rw [hfun, htarget]
  exact hpow

end
end CKN

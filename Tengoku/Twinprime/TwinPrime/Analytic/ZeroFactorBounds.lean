import Tengoku.Twinprime.TwinPrime.Analytic.HolomorphicZeroRemoval
import Tengoku.Seed.Analysis.Complex.AbsMax

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bounds for the polynomial of the actual zeros

The natural multiplicity sum is identified with the analytic divisor sum.
The radii `5/4` and `3/2` leave a distance `1/4` from every removed zero to
the outer circle. The resulting quotient estimates use exact factorization.
-/

noncomputable section

open Finset Function MeromorphicOn Metric Set

namespace TwinPrime.Analytic

def zeroFactorMultiplicity (f : ℂ → ℂ) (K : Set ℂ) : ℕ :=
  ∑ᶠ z, (divisor f K z).toNat

/--
@isnad1 id=eq.1h2v.s7.179cd77ceb21 from=translated src=- shape=807612c6 vocab=cb88719f
-/
theorem zeroFactorMultiplicity_eq_sum (f : ℂ → ℂ) {K : Set ℂ} (hK : IsCompact K) :
    zeroFactorMultiplicity f K =
      ∑ z ∈ ((divisor f K).finiteSupport hK).toFinset, (divisor f K z).toNat := by
  classical
  unfold zeroFactorMultiplicity
  apply finsum_eq_sum_of_support_subset
  intro z hz
  by_contra h
  have hd : divisor f K z = 0 := by simpa [Function.mem_support] using h
  simp [hd] at hz

/--
@isnad1 id=eq.2h2v.s7.aeaa16692838 from=translated src=- shape=46bf4e78 vocab=7a0e419f
-/
theorem zeroFactorMultiplicity_cast {f : ℂ → ℂ} {K : Set ℂ}
    (hf : AnalyticOnNhd ℂ f K) (hK : IsCompact K) :
    (zeroFactorMultiplicity f K : ℝ) = ((∑ᶠ z, divisor f K z : ℤ) : ℝ) := by
  classical
  rw [zeroFactorMultiplicity_eq_sum f hK,
    finsum_eq_sum_of_support_subset _ (by simp :
      (divisor f K).support ⊆ ((divisor f K).finiteSupport hK).toFinset)]
  push_cast
  apply sum_congr rfl
  intro z _
  exact_mod_cast Int.natCast_toNat_eq_self.mpr (hf.divisor_nonneg z)

/--
@isnad1 id=eq.2h3v.s7.b17f5ae03450 from=translated src=- shape=6d5683a2 vocab=397c15ff
-/
theorem zeroFactorPolynomial_eq_prod {f : ℂ → ℂ} {K : Set ℂ}
    (hf : AnalyticOnNhd ℂ f K) (hK : IsCompact K) (z : ℂ) :
    zeroFactorPolynomial f K z =
      ∏ u ∈ ((divisor f K).finiteSupport hK).toFinset, (z - u) ^ (divisor f K u).toNat := by
  classical
  let D := divisor f K
  have hfin := D.finiteSupport hK
  have hm : (fun u : ℂ => (fun w : ℂ => w - u) ^ D u).mulSupport ⊆ hfin.toFinset := by
    rw [Function.FactorizedRational.mulSupport]
    simp
  change (∏ᶠ u, (fun w : ℂ => w - u) ^ D u) z = _
  rw [finprod_eq_prod_of_mulSupport_subset _ hm, Finset.prod_apply]
  apply prod_congr rfl
  intro u _
  change (z - u) ^ D u = (z - u) ^ (D u).toNat
  conv_lhs => rw [← Int.natCast_toNat_eq_self.mpr (hf.divisor_nonneg u), zpow_natCast]

/--
@isnad1 id=le.4h4v.s6.1ac246578944 from=translated src=- shape=20aaf85b vocab=cb995110
-/
theorem norm_zeroFactorPolynomial_le {f : ℂ → ℂ} {K : Set ℂ}
    (hf : AnalyticOnNhd ℂ f K) (hK : IsCompact K) (z : ℂ) (R : ℝ)
    (_hR : 0 ≤ R) (hz : ∀ u ∈ K, ‖z - u‖ ≤ R) :
    ‖zeroFactorPolynomial f K z‖ ≤ R ^ zeroFactorMultiplicity f K := by
  classical
  rw [zeroFactorPolynomial_eq_prod hf hK z, norm_prod,
    zeroFactorMultiplicity_eq_sum f hK, ← prod_pow_eq_pow_sum]
  apply prod_le_prod
  · intro u _
    positivity
  · intro u hu
    rw [norm_pow]
    apply pow_le_pow_left₀ (norm_nonneg _) (hz u ?_)
    exact (divisor f K).supportWithinDomain (by simpa using hu)

/--
@isnad1 id=le.4h4v.s6.002d41ec885f from=translated src=- shape=02d082c7 vocab=cb995110
-/
theorem le_norm_zeroFactorPolynomial {f : ℂ → ℂ} {K : Set ℂ}
    (hf : AnalyticOnNhd ℂ f K) (hK : IsCompact K) (z : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hz : ∀ u ∈ K, R ≤ ‖z - u‖) :
    R ^ zeroFactorMultiplicity f K ≤ ‖zeroFactorPolynomial f K z‖ := by
  classical
  rw [zeroFactorPolynomial_eq_prod hf hK z, norm_prod,
    zeroFactorMultiplicity_eq_sum f hK, ← prod_pow_eq_pow_sum]
  apply prod_le_prod
  · intro u _
    positivity
  · intro u hu
    rw [norm_pow]
    apply pow_le_pow_left₀ hR (hz u ?_)
    exact (divisor f K).supportWithinDomain (by simpa using hu)

/--
@isnad1 id=le.1h2v.s7.9d1ca578f260 from=translated src=- shape=23fffd50 vocab=bb86ed26
-/
theorem norm_zeroFactorPolynomial_center_le {f : ℂ → ℂ} (c : ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall c (3 / 2))) :
    ‖zeroFactorPolynomial f (closedBall c (5 / 4)) c‖ ≤
      (5 / 4 : ℝ) ^ zeroFactorMultiplicity f (closedBall c (5 / 4)) := by
  apply norm_zeroFactorPolynomial_le
    (hf.mono (closedBall_subset_closedBall (by norm_num))) (isCompact_closedBall _ _) c
    (5 / 4) (by norm_num)
  intro u hu
  simpa only [norm_sub_rev] using mem_closedBall_iff_norm.mp hu

/--
@isnad1 id=le.2h3v.s7.c03946268903 from=translated src=- shape=7c770305 vocab=6e10d109
-/
theorem norm_zeroFactorPolynomial_sphere_ge {f : ℂ → ℂ} (c : ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall c (3 / 2))) (z : ℂ)
    (hz : z ∈ sphere c (3 / 2)) :
    (1 / 4 : ℝ) ^ zeroFactorMultiplicity f (closedBall c (5 / 4)) ≤
      ‖zeroFactorPolynomial f (closedBall c (5 / 4)) z‖ := by
  apply le_norm_zeroFactorPolynomial
    (hf.mono (closedBall_subset_closedBall (by norm_num))) (isCompact_closedBall _ _) z
    (1 / 4) (by norm_num)
  intro u hu
  have huc : ‖u - c‖ ≤ 5 / 4 := mem_closedBall_iff_norm.mp hu
  have hzc : ‖z - c‖ = 3 / 2 := mem_sphere_iff_norm.mp hz
  have ht := norm_add_le (z - u) (u - c)
  rw [sub_add_sub_cancel, hzc] at ht
  linarith

/--
@isnad1 id=le.2h3v.s7.5dd715ee4e8b from=translated src=- shape=4a0fda97 vocab=198382a6
-/
theorem zero_removal_center_lower {f g : ℂ → ℂ} (c : ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall c (3 / 2)))
    (heq : f c = zeroFactorPolynomial f (closedBall c (5 / 4)) c * g c) :
    ‖f c‖ / (5 / 4 : ℝ) ^ zeroFactorMultiplicity f (closedBall c (5 / 4)) ≤ ‖g c‖ := by
  apply (div_le_iff₀ (by positivity)).mpr
  rw [heq, norm_mul]
  exact (mul_le_mul_of_nonneg_right (norm_zeroFactorPolynomial_center_le c hf)
    (norm_nonneg (g c))).trans_eq (mul_comm _ _)

/--
@isnad1 id=le.5h5v.s8.4135e65f0db7 from=translated src=- shape=83eaa29a vocab=60ed8d66
-/
theorem norm_zero_removal_quotient_le_on_closedBall {f g : ℂ → ℂ} (c : ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall c (3 / 2)))
    (hg : AnalyticOnNhd ℂ g (closedBall c (3 / 2))) (M : ℝ)
    (heq : ∀ z ∈ closedBall c (3 / 2),
      f z = zeroFactorPolynomial f (closedBall c (5 / 4)) z * g z)
    (hM : ∀ z ∈ sphere c (3 / 2), ‖f z‖ ≤ M)
    (z : ℂ) (hz : z ∈ closedBall c (3 / 2)) :
    ‖g z‖ ≤ M * 4 ^ zeroFactorMultiplicity f (closedBall c (5 / 4)) := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := closedBall c (3 / 2)) isBounded_closedBall
    (isClosed_closedBall.diffContOnCl_iff.mpr hg.differentiableOn) _
    (by simpa only [closure_closedBall] using hz)
  intro w hw
  have hwS : w ∈ sphere c (3 / 2) := by
    simpa only [frontier_closedBall c (by norm_num : (3 / 2 : ℝ) ≠ 0)] using hw
  have hprod := hM w hwS
  rw [heq w (sphere_subset_closedBall hwS), norm_mul] at hprod
  have hl := mul_le_mul_of_nonneg_right (norm_zeroFactorPolynomial_sphere_ge c hf w hwS)
    (norm_nonneg (g w))
  have hpow : (1 / 4 : ℝ) ^ zeroFactorMultiplicity f (closedBall c (5 / 4)) > 0 := by positivity
  have hdiv : ‖g w‖ ≤ M / (1 / 4 : ℝ) ^ zeroFactorMultiplicity f (closedBall c (5 / 4)) :=
    (le_div_iff₀ hpow).mpr (by nlinarith)
  simpa only [one_div, inv_pow, div_inv_eq_mul] using hdiv

end TwinPrime.Analytic

import Tengoku.MobiusCpt.MobiusCPT.TestFunctions.Analytic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The pole-free complex boost core

This file contains the pole-free factorisation and the removable-singularity package used to
define the complex boost on analytic test functions.
-/

namespace MobiusCPT

open Filter Set
open scoped ContDiff Topology

noncomputable section

/-- [T26], eq. (3.5); on the unit circle the conformal scalar of the complex boost is the
pole-free product `v_{-τ}`-denominator times `v_{-τ}`-numerator over `z`.
@isnad1 id=eq.0h2v.s8.a3e3f437aa3c from=translated src=- shape=aea9b59e vocab=bd84333f
-/
theorem cosh_add_re_mul_sinh_div (τ : ℂ) (z : Circle) :
    Complex.cosh τ + ((z : ℂ).re : ℂ) * Complex.sinh τ =
      cden (-τ) z * cnum (-τ) z / (z : ℂ) := by
  rw [cosh_add_re_mul_sinh]
  have hzconj : (starRingEnd ℂ) (z : ℂ) = (z : ℂ)⁻¹ := by
    simpa using (Circle.coe_inv_eq_conj z).symm
  rw [hzconj]
  calc
    cden (-τ) z * (Complex.sinh (τ / 2) * (z : ℂ)⁻¹ + Complex.cosh (τ / 2)) =
        cden (-τ) z * (cnum (-τ) z / (z : ℂ)) := by
          congr 1
          rw [cnum_neg]
          field_simp [Circle.coe_ne_zero z]
          ring
    _ = cden (-τ) z * cnum (-τ) z / (z : ℂ) := by rw [mul_div_assoc]

/-- [T26], Definition 3.5; on the closed strip `0 ≤ Im τ ≤ π` the numerator of `v_{-τ}` does not
vanish on the closed upper semicircle: it dominates the denominator in modulus, and the two cannot
vanish together.
@isnad1 id=ne.3h2v.s7.fb7817e68b86 from=translated src=- shape=5696c72c vocab=fdd5251d
-/
theorem cnum_neg_ne_zero_of_upper {τ : ℂ} (h₀ : 0 ≤ τ.im) (h₁ : τ.im ≤ Real.pi)
    {z : Circle} (hz : 0 ≤ (z : ℂ).im) : cnum (-τ) z ≠ 0 := by
  intro hnum
  have hle : ‖cden (-τ) z‖ ≤ 0 := by
    simpa [hnum] using norm_cden_neg_le_norm_cnum_neg h₀ h₁ hz
  have hden : cden (-τ) z = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm hle (norm_nonneg _)
  exact (not_and_cnum_cden_eq_zero (-τ) z) ⟨hnum, hden⟩

/-- [T26], Definition 3.5; the ratio that the removable-singularity extension is built on takes
values in the closed unit disc.
@isnad1 id=le.3h2v.s8.e0a5866b6d83 from=translated src=- shape=0141ffe1 vocab=2a8af540
-/
theorem norm_cden_div_cnum_le_one {τ : ℂ} (h₀ : 0 ≤ τ.im) (h₁ : τ.im ≤ Real.pi)
    {z : Circle} (hz : 0 ≤ (z : ℂ).im) :
    ‖cden (-τ) z / cnum (-τ) z‖ ≤ 1 := by
  rw [Complex.norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr (cnum_neg_ne_zero_of_upper h₀ h₁ hz))).2
  simpa using norm_cden_neg_le_norm_cnum_neg h₀ h₁ hz

/-- [T26], Definition 3.5; the modulus bound is equivalently membership in the closed unit disc.
@isnad1 id=mem.3h2v.s8.802cea9ff459 from=translated src=- shape=03c5b75f vocab=fd17435b
-/
theorem cden_div_cnum_mem_closedBall {τ : ℂ} (h₀ : 0 ≤ τ.im) (h₁ : τ.im ≤ Real.pi)
    {z : Circle} (hz : 0 ≤ (z : ℂ).im) :
    cden (-τ) z / cnum (-τ) z ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_cden_div_cnum_le_one h₀ h₁ hz

/-- [T26], §3; the complex boost fixes the endpoint represented by `1`.
@isnad1 id=eq.1h2v.s8.cb97a59df990 from=translated src=- shape=b5e18f97 vocab=d8bd1f35
-/
theorem cden_div_cnum_of_coe_eq_one {τ : ℂ} {z : Circle} (hz : (z : ℂ) = 1) :
    cden (-τ) z / cnum (-τ) z = 1 := by
  rw [cnum_neg, cden_neg, hz]
  simp only [mul_one]
  rw [Complex.cosh_add_sinh, Complex.sinh_add_cosh]
  exact div_self (Complex.exp_ne_zero _)

/-- [T26], §3; the complex boost fixes the endpoint represented by `-1`.
@isnad1 id=eq.1h2v.s8.f27f23fca5f1 from=translated src=- shape=15669f3e vocab=d8bd1f35
-/
theorem cden_div_cnum_of_coe_eq_neg_one {τ : ℂ} {z : Circle} (hz : (z : ℂ) = -1) :
    cden (-τ) z / cnum (-τ) z = -1 := by
  rw [cnum_neg, cden_neg, hz]
  simp only [mul_neg, mul_one]
  have hnum : -Complex.cosh (τ / 2) + Complex.sinh (τ / 2) =
      -Complex.exp (-(τ / 2)) := by
    calc
      -Complex.cosh (τ / 2) + Complex.sinh (τ / 2) =
          Complex.sinh (τ / 2) - Complex.cosh (τ / 2) := by ring
      _ = -Complex.exp (-(τ / 2)) := Complex.sinh_sub_cosh _
  have hden : -Complex.sinh (τ / 2) + Complex.cosh (τ / 2) =
      Complex.exp (-(τ / 2)) := by
    calc
      -Complex.sinh (τ / 2) + Complex.cosh (τ / 2) =
          Complex.cosh (τ / 2) - Complex.sinh (τ / 2) := by ring
      _ = Complex.exp (-(τ / 2)) := Complex.cosh_sub_sinh _
  rw [hnum, hden, div_neg, div_self (Complex.exp_ne_zero _)]

/-- [T26], Definition 3.5 and the `d = 0` case; `F(w⁻¹)/w`, filled in at the origin by the
derivative. Because `F` vanishes at `∞`, this quotient is the regular function that cancels the
simple pole of `(cosh τ + Re z sinh τ)⁻¹`, so the complex boost can be defined without ever
forming the raw quotient.-/
noncomputable def AnalyticTestFn.invQuot (F : AnalyticTestFn) : ℂ → ℂ :=
  Function.update (fun w => F.invExt w / w) 0 (deriv F.invExt 0)

/-- [T26], Definition 3.5; away from the origin `invQuot` is its literal quotient.
@isnad1 id=eq.1h2v.s5.2b4b4a174699 from=translated src=- shape=b08ee6d6 vocab=4b4f3f2a
-/
theorem AnalyticTestFn.invQuot_of_ne (F : AnalyticTestFn) {w : ℂ} (hw : w ≠ 0) :
    F.invQuot w = F.invExt w / w := by
  simp [AnalyticTestFn.invQuot, hw]

/-- [T26], Definition 3.5; the value of `invQuot` at the removable singularity is the derivative.
@isnad1 id=eq.0h1v.s5.eec05edd7be3 from=translated src=- shape=07b2fe90 vocab=0b494e20
-/
theorem AnalyticTestFn.invQuot_zero (F : AnalyticTestFn) :
    F.invQuot 0 = deriv F.invExt 0 := by
  simp [AnalyticTestFn.invQuot]

/-- [T26], Definition 3.5; multiplying back by `w` recovers `F(w⁻¹)` everywhere, including at
the origin where both sides are `0`.
@isnad1 id=eq.0h2v.s4.e99153d7f570 from=translated src=- shape=a3c0a8ae vocab=62b179e1
-/
theorem AnalyticTestFn.mul_invQuot (F : AnalyticTestFn) (w : ℂ) :
    w * F.invQuot w = F.invExt w := by
  by_cases hw : w = 0
  · subst w
    simp [AnalyticTestFn.invExt, AnalyticTestFn.invQuot]
  · rw [F.invQuot_of_ne hw]
    field_simp

/-- [T26], Definition 3.5; away from the origin the divided function is the literal quotient
`F(w⁻¹)/w`.
@isnad1 id=eq.1h2v.s5.c7d3bc9dd839 from=translated src=- shape=bc18bc6f vocab=b8960fe8
-/
theorem AnalyticTestFn.invQuot_apply (F : AnalyticTestFn) {w : ℂ} (hw : w ≠ 0) :
    F.invQuot w = F.toFun w⁻¹ / w := by
  rw [F.invQuot_of_ne hw, F.invExt_of_ne hw]

/-- [T26], Definition 3.5; the divided inverted function is holomorphic on the open unit disc:
the singularity at the origin is removable because `F(∞) = 0`.
@isnad1 id=differen.0h1v.s6.2a3517737052 from=translated src=- shape=4ee979c2 vocab=93923cb4
-/
theorem AnalyticTestFn.differentiableOn_invQuot (F : AnalyticTestFn) :
    DifferentiableOn ℂ F.invQuot (Metric.ball (0 : ℂ) 1) := by
  let s : Set ℂ := Metric.ball (0 : ℂ) 1
  have hdiv : DifferentiableOn ℂ (fun w : ℂ => F.invExt w / w) (s \ {0}) := by
    apply (F.diffContOnCl_invExt.differentiableOn.mono sdiff_subset).div differentiableOn_id
    intro w hw
    change w ≠ 0
    simpa only [mem_singleton_iff] using hw.2
  have hpunct : DifferentiableOn ℂ F.invQuot (s \ {0}) := by
    apply hdiv.congr
    intro w hw
    exact F.invQuot_of_ne (by simpa only [mem_singleton_iff] using hw.2)
  have hzero : F.invExt 0 = 0 := by
    simp [AnalyticTestFn.invExt]
  have hdiff0 : DifferentiableAt ℂ F.invExt 0 := F.differentiableAt_inv
  have hderiv : HasDerivAt F.invExt (deriv F.invExt 0) 0 := hdiff0.hasDerivAt
  have hupdate :
      Function.update (fun w => (F.invExt w - F.invExt 0) / (w - 0)) 0
          (deriv F.invExt 0) = F.invQuot := by
    funext w
    by_cases hw : w = 0
    · subst w
      simp [AnalyticTestFn.invQuot, hzero]
    · rw [Function.update_of_ne hw, F.invQuot_of_ne hw]
      simp [hzero]
  have hcont : ContinuousAt F.invQuot 0 := by
    rw [← hupdate]
    exact hderiv.continuousAt_div
  have hs : s ∈ 𝓝 (0 : ℂ) := by
    exact Metric.ball_mem_nhds _ one_pos
  exact (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hs).mp
    ⟨hpunct, hcont⟩

/-- [T26], Definition 3.2 and 3.5; the divided inverted function is smooth up to the boundary of
the unit disc, which is where the complex boost reads it.
@isnad1 id=contdiff.0h1v.s5.4049df9ae5ea from=translated src=- shape=300e0554 vocab=59b42aef
-/
theorem AnalyticTestFn.contDiffOn_invQuot (F : AnalyticTestFn) :
    ContDiffOn ℝ ∞ F.invQuot (Metric.closedBall (0 : ℂ) 1) := by
  intro w hw
  by_cases hw0 : w = 0
  · subst w
    have hcomplex : ContDiffOn ℂ ∞ F.invQuot (Metric.ball (0 : ℂ) 1) :=
      F.differentiableOn_invQuot.contDiffOn (n := ∞) Metric.isOpen_ball
    have hreal : ContDiffOn ℝ ∞ F.invQuot (Metric.ball (0 : ℂ) 1) :=
      hcomplex.restrict_scalars ℝ
    have hmem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      simp [Metric.mem_ball]
    exact (hreal 0 hmem).mono_of_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ one_pos))
  · let t : Set ℂ := Metric.closedBall (0 : ℂ) 1 ∩ {u : ℂ | u ≠ 0}
    have htw : w ∈ t := by
      exact ⟨hw, hw0⟩
    have hinv : ContDiffOn ℝ ∞ (fun u : ℂ => u⁻¹) t := by
      apply (contDiffOn_inv (𝕜 := ℝ) (𝕜' := ℂ)).mono
      intro u hu
      exact hu.2
    have hmaps : Set.MapsTo (fun u : ℂ => u⁻¹) t Oexterior := by
      intro u hu
      have hu0 : u ≠ 0 := hu.2
      have hule : ‖u‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hu.1
      have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      show (1 : ℝ) ≤ ‖u⁻¹‖
      rw [norm_inv]
      exact (one_le_inv₀ hupos).2 hule
    have hcomp : ContDiffOn ℝ ∞ (F.toFun ∘ (fun u : ℂ => u⁻¹)) t :=
      F.contDiffOn.comp hinv hmaps
    have hquot : ContDiffOn ℝ ∞ (fun u : ℂ => F.toFun u⁻¹ / u) t := by
      simpa only [Function.comp_apply, div_eq_mul_inv] using hcomp.mul hinv
    have hquot_t : ContDiffWithinAt ℝ ∞ F.invQuot t w := by
      apply (hquot w htw).congr
      · intro u hu
        exact F.invQuot_apply hu.2
      · exact F.invQuot_apply hw0
    have ht_nhds : t ∈ 𝓝[Metric.closedBall (0 : ℂ) 1] w := by
      change Metric.closedBall (0 : ℂ) 1 ∩ {u : ℂ | u ≠ 0} ∈
        𝓝[Metric.closedBall (0 : ℂ) 1] w
      exact inter_mem_nhdsWithin _ (isOpen_ne.mem_nhds hw0)
    exact hquot_t.mono_of_mem_nhdsWithin ht_nhds

end

end MobiusCPT

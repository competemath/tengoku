/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.Seed.Analysis.Analytic.Order
import Tengoku.Seed.NumberTheory.LSeries.Nonvanishing
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.GammaCancellation.TextbookXi
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.Xi.FunctionalEquation
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.Xi.SignTargets

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The zero set of the entire Riemann xi function

This module proves, without an auxiliary correspondence hypothesis, that the
zeros of `entireRiemannXi` are exactly Mathlib's nontrivial zeros of
`riemannZeta`.  It then identifies Mathlib's `RiemannHypothesis` with the
statement that every zero of `entireRiemannXi` lies on the critical line.

The points at which the raw Gamma-factor formula is totalized require some
care.  At `s = 0` the entire xi function is `1 / 2`.  At a negative even
integer, its functional equation moves the value to the zero-free half-plane
`1 < re s`.  Thus no cancellation fact is smuggled into the zero
correspondence as an assumption.
-/

namespace OverflowResidueRH

open Complex
open Filter Topology

/-- The pointwise predicate used by Mathlib's definition of the Riemann
hypothesis: a zeta zero which is neither a trivial negative-even zero nor the
totalized value at `s = 1`.-/
def IsMathlibNontrivialZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧
    (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧
    s ≠ 1

/-- At a regular point, the entire xi definition agrees directly with the
completed-zeta formula.
@isnad1 id=eq.2h1v.s6.1f2542b7252c from=translated src=- shape=c8388633 vocab=8f3b89be
-/
theorem entireRiemannXi_eq_completedRiemannZeta
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    entireRiemannXi s =
      (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
  unfold entireRiemannXi
  rw [completedRiemannZeta_eq]
  exact (xi_completedZeta_correction_algebra hs0 hs1).symm

/-- Away from the totalized point at zero, completed zeta is the Deligne
Gamma factor times Riemann zeta whenever that Gamma factor is nonzero.
@isnad1 id=eq.2h1v.s5.e2079819bb8e from=translated src=- shape=933d9f5b vocab=d81b2980
-/
theorem completedRiemannZeta_eq_GammaReal_mul_riemannZeta
    {s : ℂ} (hs0 : s ≠ 0) (hG : Gammaℝ s ≠ 0) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  have hz := riemannZeta_def_of_ne_zero (s := s) hs0
  rw [hz]
  field_simp [hG]

/-- At regular points, vanishing of the entire xi function is equivalent to
vanishing of Riemann zeta.
@isnad1 id=iff.3h1v.s5.a1a7bb8b74d9 from=translated src=- shape=87592818 vocab=78dd26f4
-/
theorem entireRiemannXi_eq_zero_iff_riemannZeta_eq_zero
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hG : Gammaℝ s ≠ 0) :
    entireRiemannXi s = 0 ↔ riemannZeta s = 0 := by
  rw [entireRiemannXi_eq_completedRiemannZeta hs0 hs1,
      completedRiemannZeta_eq_GammaReal_mul_riemannZeta hs0 hG]
  simp [hs0, sub_ne_zero.mpr hs1, hG]

/-- The entire xi function is nonzero at `s = 0`.
@isnad1 id=ne.0h0v.s3.5d054d8dd55a from=translated src=- shape=3c26ae4f vocab=5134c549
-/
theorem entireRiemannXi_zero_ne :
    entireRiemannXi 0 ≠ 0 := by
  norm_num [entireRiemannXi]

/-- The entire xi function is nonzero at `s = 1`.
@isnad1 id=ne.0h0v.s3.796302f0bf9e from=translated src=- shape=3c26ae4f vocab=5134c549
-/
theorem entireRiemannXi_one_ne :
    entireRiemannXi 1 ≠ 0 := by
  norm_num [entireRiemannXi]

/-- A nontrivial zeta zero is not a pullback of a Gamma pole.
@isnad1 id=not.2h1v.s6.4aff1740f81b from=translated src=- shape=aa6ab141 vocab=5cc9e17f
-/
theorem half_not_mem_gammaPoleSet_of_nontrivial_zeta_zero
    {s : ℂ} (hzeta : riemannZeta s = 0)
    (hnot_trivial : ¬ ∃ n : ℕ, s = -2 * (n + 1)) :
    s / 2 ∉ gammaPoleSet := by
  rintro ⟨n, hn⟩
  by_cases hn0 : n = 0
  · subst n
    have hs0 : s = 0 := by
      linear_combination 2 * hn
    subst s
    norm_num [riemannZeta_zero] at hzeta
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    apply hnot_trivial
    refine ⟨m, ?_⟩
    have hn' : s / 2 = -((m : ℂ) + 1) := by
      simpa using hn
    linear_combination 2 * hn'

/-- Every Mathlib-nontrivial zeta zero is a zero of the entire xi function.
@isnad1 id=eq.3h1v.s6.0a387c205e6d from=translated src=- shape=90c3814f vocab=0a2f27fb
-/
theorem entireRiemannXi_eq_zero_of_nontrivial_zeta_zero
    {s : ℂ} (hzeta : riemannZeta s = 0)
    (hnot_trivial : ¬ ∃ n : ℕ, s = -2 * (n + 1))
    (hs1 : s ≠ 1) :
    entireRiemannXi s = 0 := by
  have hsPole : s / 2 ∉ gammaPoleSet :=
    half_not_mem_gammaPoleSet_of_nontrivial_zeta_zero hzeta hnot_trivial
  rw [← completedXiRawEntireXiOffPolePointwiseFormula.pointwise_eq s hs1 hsPole]
  simp [completedXiFunction, hzeta]

/-- The entire xi function has no zeros in the half-plane `1 < re s`.
@isnad1 id=ne.1h1v.s4.5b1a92cf5ec1 from=translated src=- shape=555d9df8 vocab=77c82b41
-/
theorem entireRiemannXi_ne_zero_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    entireRiemannXi s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have hsPole : s / 2 ∉ gammaPoleSet := by
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp at hre
    have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hgamma : Complex.Gamma (s / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    exact hsPole ⟨n, hn⟩
  have hraw : completedXiFunction s ≠ 0 := by
    unfold completedXiFunction
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero (by norm_num) hs0)
            (sub_ne_zero.mpr hs1))
          (Complex.exp_ne_zero _))
        hgamma)
      (riemannZeta_ne_zero_of_one_lt_re hs)
  rw [completedXiRawEntireXiOffPolePointwiseFormula.pointwise_eq s hs1 hsPole] at hraw
  exact hraw

/-- Negative-even trivial zeta zeros are not zeros of the entire xi function.
The functional equation moves them to the zero-free half-plane.
@isnad1 id=ne.0h1v.s5.0d98b9d1c167 from=translated src=- shape=98817f85 vocab=64746c52
-/
theorem entireRiemannXi_neg_two_mul_nat_add_one_ne_zero (n : ℕ) :
    entireRiemannXi (-2 * ((n : ℂ) + 1)) ≠ 0 := by
  rw [← entireRiemannXi_one_sub]
  apply entireRiemannXi_ne_zero_of_one_lt_re
  norm_num [Complex.sub_re, Complex.mul_re, Complex.add_re]
  exact_mod_cast Nat.zero_lt_succ n

/-- A zero of the entire xi function cannot occur at a pullback of a Gamma
pole.  Negative even points are moved by the functional equation to
`re s > 1`; the remaining pole-pullback point is `s = 0`, where xi is
`1 / 2`.
@isnad1 id=not.1h1v.s5.1aa23f990b90 from=translated src=- shape=14d42a76 vocab=f0250af3
-/
theorem half_not_mem_gammaPoleSet_of_entireRiemannXi_zero
    {s : ℂ} (hxi : entireRiemannXi s = 0) :
    s / 2 ∉ gammaPoleSet := by
  rintro ⟨n, hn⟩
  by_cases hn0 : n = 0
  · subst n
    have hs0 : s = 0 := by
      linear_combination 2 * hn
    subst s
    norm_num [entireRiemannXi] at hxi
  · have hnpos : (0 : ℝ) < n := by
      exact_mod_cast Nat.pos_of_ne_zero hn0
    have hre := congrArg Complex.re hn
    simp at hre
    have hright : 1 < (1 - s).re := by
      rw [Complex.sub_re]
      norm_num
      nlinarith
    apply entireRiemannXi_ne_zero_of_one_lt_re hright
    rw [entireRiemannXi_one_sub]
    exact hxi

/-- A zero of the entire xi function is not the totalized point `s = 1`.
@isnad1 id=ne.1h1v.s4.c3adae59e7cc from=translated src=- shape=ec3adfee vocab=5134c549
-/
theorem ne_one_of_entireRiemannXi_zero
    {s : ℂ} (hxi : entireRiemannXi s = 0) :
    s ≠ 1 := by
  intro hs
  subst s
  norm_num [entireRiemannXi] at hxi

/-- Every zero of the entire xi function is a zero of Mathlib's Riemann zeta
function.
@isnad1 id=eq.1h1v.s4.495684249d88 from=translated src=- shape=dbdd11df vocab=fba8f5a7
-/
theorem riemannZeta_eq_zero_of_entireRiemannXi_zero
    {s : ℂ} (hxi : entireRiemannXi s = 0) :
    riemannZeta s = 0 := by
  have hsPole : s / 2 ∉ gammaPoleSet :=
    half_not_mem_gammaPoleSet_of_entireRiemannXi_zero hxi
  have hs0 : s ≠ 0 := ne_zero_of_half_not_gammaPole hsPole
  have hs1 : s ≠ 1 := ne_one_of_entireRiemannXi_zero hxi
  have hgamma : Complex.Gamma (s / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    exact hsPole ⟨n, hn⟩
  have hraw : completedXiFunction s = 0 := by
    rw [completedXiRawEntireXiOffPolePointwiseFormula.pointwise_eq s hs1 hsPole]
    exact hxi
  rw [completedXiFunction] at hraw
  have hcoefficient :
      (1 / 2 : ℂ) * s * (s - 1)
          * Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))
          * Complex.Gamma (s / 2) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (by norm_num) hs0)
          (sub_ne_zero.mpr hs1))
        (Complex.exp_ne_zero _))
      hgamma
  exact (mul_eq_zero.mp hraw).resolve_left hcoefficient

/-- A zero of the entire xi function is not a trivial negative-even zeta
zero.
@isnad1 id=not.1h1v.s5.c3bad7a41620 from=translated src=- shape=a8f78a57 vocab=64746c52
-/
theorem not_trivial_of_entireRiemannXi_zero
    {s : ℂ} (hxi : entireRiemannXi s = 0) :
    ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
  intro htrivial
  obtain ⟨n, hn⟩ := htrivial
  apply half_not_mem_gammaPoleSet_of_entireRiemannXi_zero hxi
  refine ⟨n + 1, ?_⟩
  rw [hn]
  push_cast
  ring

/-- The zeros of the entire xi function are exactly the nontrivial zeros in
Mathlib's formulation of the Riemann hypothesis.
@isnad1 id=iff.0h1v.s3.b0aa46ba5487 from=translated src=- shape=f72d1292 vocab=1a779c7d
-/
theorem entireRiemannXi_eq_zero_iff_mathlib_nontrivial_zeta_zero
    {s : ℂ} :
    entireRiemannXi s = 0 ↔ IsMathlibNontrivialZetaZero s := by
  constructor
  · intro hxi
    exact ⟨riemannZeta_eq_zero_of_entireRiemannXi_zero hxi,
      not_trivial_of_entireRiemannXi_zero hxi,
      ne_one_of_entireRiemannXi_zero hxi⟩
  · rintro ⟨hzeta, hnot_trivial, hs1⟩
    exact entireRiemannXi_eq_zero_of_nontrivial_zeta_zero hzeta hnot_trivial hs1

/-- Every zero of the entire xi function lies strictly inside the critical
strip.  The right boundary follows from zeta nonvanishing on `re s ≥ 1`; the
left boundary follows by reflecting with the xi functional equation.
@isnad1 id=mem.1h1v.s5.085a07c162d1 from=translated src=- shape=7d06874f vocab=2f03c98b
-/
theorem entireRiemannXi_zero_re_mem_Ioo
    {s : ℂ} (hxi : entireRiemannXi s = 0) :
    s.re ∈ Set.Ioo (0 : ℝ) 1 := by
  have hzeta : riemannZeta s = 0 :=
    riemannZeta_eq_zero_of_entireRiemannXi_zero hxi
  have hre_lt_one : s.re < 1 := by
    apply lt_of_not_ge
    intro hre
    exact (riemannZeta_ne_zero_of_one_le_re hre) hzeta
  have hreflected : entireRiemannXi (1 - s) = 0 := by
    rw [entireRiemannXi_one_sub]
    exact hxi
  have hzeta_reflected : riemannZeta (1 - s) = 0 :=
    riemannZeta_eq_zero_of_entireRiemannXi_zero hreflected
  have hreflected_lt_one : (1 - s).re < 1 := by
    apply lt_of_not_ge
    intro hre
    exact (riemannZeta_ne_zero_of_one_le_re hre) hzeta_reflected
  have hre_pos : 0 < s.re := by
    rw [Complex.sub_re] at hreflected_lt_one
    norm_num at hreflected_lt_one ⊢
    linarith
  exact ⟨hre_pos, hre_lt_one⟩

/-- Consequently, the imaginary coordinate of every centered-pullback zero
lies strictly between `-1/2` and `1/2`.  This is the geometric input that
compares pullback norm shells with zeta-height slabs.
@isnad1 id=lt.1h1v.s5.1de821101241 from=translated src=- shape=dcedf27f vocab=85df402e
-/
theorem entireXiPullback_zero_im_abs_lt_half
    {z : ℂ} (hz : EntireXiPullback z = 0) :
    |z.im| < (1 / 2 : ℝ) := by
  have hstrip := entireRiemannXi_zero_re_mem_Ioo
    (s := (1 / 2 : ℂ) + Complex.I * z) hz
  rw [critical_shift_re] at hstrip
  rw [abs_lt]
  constructor <;> linarith [hstrip.1, hstrip.2]

/-! ### Exact analytic multiplicity across the xi--zeta bridge -/

/-- The local analytic unit relating `entireRiemannXi` to `riemannZeta`
inside the critical strip.-/
private noncomputable def entireRiemannXiZetaUnit (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * Complex.Gammaℝ s

/-- Deligne's real Gamma factor is analytic wherever its argument has
positive real part.  We obtain this without a separate pole-set calculation:
its reciprocal is entire, and is nonzero on this half-plane.-/
private theorem analyticAt_GammaReal_of_re_pos
    {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ Complex.Gammaℝ s := by
  have hinv : AnalyticAt ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv.analyticAt s
  have hinv_ne : (Complex.Gammaℝ s)⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hs)
  have hdouble := hinv.inv hinv_ne
  change AnalyticAt ℂ (fun w : ℂ => ((Complex.Gammaℝ w)⁻¹)⁻¹) s at hdouble
  simpa only [inv_inv] using hdouble

private theorem analyticAt_entireRiemannXiZetaUnit_of_re_pos
    {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ entireRiemannXiZetaUnit s := by
  have hpoly :
      AnalyticAt ℂ (fun w : ℂ => (1 / 2 : ℂ) * w * (w - 1)) s := by
    fun_prop
  exact hpoly.mul (analyticAt_GammaReal_of_re_pos hs)

/-- At a zero of `entireRiemannXi`, the entire xi function agrees in a full
neighborhood with a nonvanishing analytic unit times `riemannZeta`.-/
private theorem
    entireRiemannXi_eventuallyEq_zetaUnit_mul_riemannZeta_at_zero
    {s : ℂ} (hxi : entireRiemannXi s = 0) :
    entireRiemannXi =ᶠ[𝓝 s] entireRiemannXiZetaUnit * riemannZeta := by
  have hstrip := entireRiemannXi_zero_re_mem_Ioo hxi
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hstrip
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    norm_num at hstrip
  have hpos : ∀ᶠ w : ℂ in 𝓝 s, 0 < w.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hstrip.1
  filter_upwards [hpos, eventually_ne_nhds hs0, eventually_ne_nhds hs1]
    with w hwpos hw0 hw1
  change entireRiemannXi w =
    entireRiemannXiZetaUnit w * riemannZeta w
  rw [entireRiemannXi_eq_completedRiemannZeta hw0 hw1,
    completedRiemannZeta_eq_GammaReal_mul_riemannZeta hw0
      (Complex.Gammaℝ_ne_zero_of_re_pos hwpos)]
  unfold entireRiemannXiZetaUnit
  ring

/-- At every zero of `entireRiemannXi`, its analytic order is exactly the
analytic order of `riemannZeta`.  Thus the xi--zeta zero correspondence
preserves multiplicity, rather than merely preserving the zero set.
@isnad1 id=eq.1h1v.s5.8dfefdf8b7dd from=translated src=- shape=147c6a37 vocab=1e349b1f
-/
theorem entireRiemannXi_analyticOrderAt_eq_riemannZeta_of_zero
    {s : ℂ} (hxi : entireRiemannXi s = 0) :
    analyticOrderAt entireRiemannXi s =
      analyticOrderAt riemannZeta s := by
  have hstrip := entireRiemannXi_zero_re_mem_Ioo hxi
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    norm_num at hstrip
  have hunit : AnalyticAt ℂ entireRiemannXiZetaUnit s :=
    analyticAt_entireRiemannXiZetaUnit_of_re_pos hstrip.1
  have hunit_ne : entireRiemannXiZetaUnit s ≠ 0 := by
    unfold entireRiemannXiZetaUnit
    have hs0 : s ≠ 0 := by
      intro hs
      subst s
      norm_num at hstrip
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) hs0)
        (sub_ne_zero.mpr hs1))
      (Complex.Gammaℝ_ne_zero_of_re_pos hstrip.1)
  have hzeta : AnalyticAt ℂ riemannZeta s := by
    exact analyticOn_riemannZeta s (by simpa using hs1)
  rw [analyticOrderAt_congr
    (entireRiemannXi_eventuallyEq_zetaUnit_mul_riemannZeta_at_zero hxi)]
  rw [analyticOrderAt_mul hunit hzeta,
    hunit.analyticOrderAt_eq_zero.mpr hunit_ne, zero_add]

/-- Natural-number form of exact xi--zeta multiplicity preservation.
@isnad1 id=eq.1h1v.s5.f8a4e891c841 from=translated src=- shape=147c6a37 vocab=693bb72f
-/
theorem entireRiemannXi_analyticOrderNatAt_eq_riemannZeta_of_zero
    {s : ℂ} (hxi : entireRiemannXi s = 0) :
    analyticOrderNatAt entireRiemannXi s =
      analyticOrderNatAt riemannZeta s :=
  congrArg ENat.toNat
    (entireRiemannXi_analyticOrderAt_eq_riemannZeta_of_zero hxi)

/-- Exact analytic multiplicity preservation, stated directly for Mathlib's
predicate of a nontrivial zeta zero.
@isnad1 id=eq.1h1v.s5.b38095f2d4d8 from=translated src=- shape=e315fbd1 vocab=6e4ee6fb
-/
theorem entireRiemannXi_analyticOrderAt_eq_riemannZeta_of_mathlib_nontrivial_zero
    {s : ℂ} (hs : IsMathlibNontrivialZetaZero s) :
    analyticOrderAt entireRiemannXi s =
      analyticOrderAt riemannZeta s :=
  entireRiemannXi_analyticOrderAt_eq_riemannZeta_of_zero
    (entireRiemannXi_eq_zero_iff_mathlib_nontrivial_zeta_zero.mpr hs)

/-- Natural-number multiplicity preservation, stated directly for Mathlib's
predicate of a nontrivial zeta zero.
@isnad1 id=eq.1h1v.s5.ca9f5e30b0a3 from=translated src=- shape=e315fbd1 vocab=56be9322
-/
theorem entireRiemannXi_analyticOrderNatAt_eq_riemannZeta_of_mathlib_nontrivial_zero
    {s : ℂ} (hs : IsMathlibNontrivialZetaZero s) :
    analyticOrderNatAt entireRiemannXi s =
      analyticOrderNatAt riemannZeta s :=
  entireRiemannXi_analyticOrderNatAt_eq_riemannZeta_of_zero
    (entireRiemannXi_eq_zero_iff_mathlib_nontrivial_zeta_zero.mpr hs)

/-- Mathlib's Riemann hypothesis is exactly the assertion that all zeros of
the entire xi function lie on the critical line.
@isnad1 id=iff.0h0v.s5.572819e9bb3b from=translated src=- shape=e15090fc vocab=25b220e8
-/
theorem riemannHypothesis_iff_entireRiemannXi_zeros_on_critical_line :
    RiemannHypothesis ↔
      ∀ s : ℂ, entireRiemannXi s = 0 → s.re = 1 / 2 := by
  constructor
  · intro hRH s hxi
    exact hRH s
      (riemannZeta_eq_zero_of_entireRiemannXi_zero hxi)
      (not_trivial_of_entireRiemannXi_zero hxi)
      (ne_one_of_entireRiemannXi_zero hxi)
  · intro hxi s hzeta hnot_trivial hs1
    exact hxi s
      (entireRiemannXi_eq_zero_of_nontrivial_zeta_zero
        hzeta hnot_trivial hs1)

/-- Pulling the entire xi function back along `s = 1 / 2 + I * z`
turns Mathlib's Riemann hypothesis into the literal real-rootedness of
`EntireXiPullback`.
@isnad1 id=iff.0h0v.s4.3cfe64282f88 from=translated src=- shape=8f900334 vocab=935ce66d
-/
theorem riemannHypothesis_iff_entireXiPullback_zeros_real :
    RiemannHypothesis ↔
      ∀ z : ℂ, EntireXiPullback z = 0 → z.im = 0 := by
  rw [riemannHypothesis_iff_entireRiemannXi_zeros_on_critical_line]
  constructor
  · intro hcritical z hz
    have hline := hcritical
      ((1 / 2 : ℂ) + Complex.I * z) hz
    rw [critical_shift_re] at hline
    linarith
  · intro hreal s hs
    let z : ℂ := -Complex.I * (s - (1 / 2 : ℂ))
    have hshift : (1 / 2 : ℂ) + Complex.I * z = s := by
      dsimp [z]
      ring_nf
      rw [Complex.I_sq]
      ring
    have hz : EntireXiPullback z = 0 := by
      unfold EntireXiPullback
      rw [hshift]
      exact hs
    have him : z.im = 0 := hreal z hz
    have hre := critical_shift_re z
    rw [hshift, him] at hre
    simpa using hre

/-- The repository's remaining left-half-plane logarithmic-derivative sign
condition implies Mathlib's literal `RiemannHypothesis`.  All regularity,
Schwarz-reflection, nontriviality, exceptional-point, and zero-correspondence
obligations have been discharged; `h_sign` is the only hypothesis.
@isnad1 id=riemannh.1h0v.s1.b7c3d6070e6a from=translated src=- shape=1d48f1ac vocab=16040785
-/
theorem riemannHypothesis_of_entireXi_leftHalfPlaneLogDerivSign
    (h_sign : EntireXi.leftHalfPlaneLogDerivSign) :
    RiemannHypothesis :=
  riemannHypothesis_iff_entireXiPullback_zeros_real.mpr
    (EntireXiPullback.zeros_real_of_sign h_sign)

end OverflowResidueRH

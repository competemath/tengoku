/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.HadamardProduct.OriginMultiplicityCriterion
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.Xi.RiemannHypothesisBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A strict Lagarias-type criterion

This module states the classical strict right-half-plane sign condition for
Mathlib's entire Riemann xi, proves its exact equivalence with the strict
anti-Herglotz condition for the critical-line pullback, and connects the
generic genus-one theorem to xi under one explicit Hadamard-factorization
package. The package permits a finite zero at the pullback origin; Schwarz
reflection derives the affine slope, and nontriviality derives the prefactor
constant's nonvanishing.

No inhabitant of the factorization package is claimed here. Consequently the
unconditional direction is still sign implies RH; the reverse direction is
conditional on the multiplicity-bearing divisor, summability, and exact
canonical-product identity packaged below.
-/

namespace OverflowResidueRH

/-- The strict right-half-plane logarithmic-derivative condition appearing
in Lagarias's criterion.-/
def EntireXi.rightHalfPlaneStrictLogDerivSign : Prop :=
  ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
    0 < ((deriv entireRiemannXi s) / entireRiemannXi s).re

/-- Punctured-domain formulation of the classical Lagarias positivity
condition. Nonvanishing is stated explicitly so the public theorem does not
depend on Lean's totalized division convention.-/
def EntireXi.LagariasPositivity : Prop :=
  ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
    entireRiemannXi s ≠ 0 ∧
      0 < (logDerivativeResponse entireRiemannXi s).re

/-- The explicit nonvanishing formulation and the totalized strict sign
formulation are equivalent. Strict positivity forces the denominator to be
nonzero because division by zero is totalized to zero.
@isnad1 id=iff.0h0v.s1.23b81db22a50 from=translated src=- shape=25b03439 vocab=cd4d92f4
-/
theorem entireXi_lagariasPositivity_iff_rightHalfPlaneStrictLogDerivSign :
    EntireXi.LagariasPositivity ↔
      EntireXi.rightHalfPlaneStrictLogDerivSign := by
  constructor
  · intro h s hs
    exact (h s hs).2
  · intro h s hs
    have hpos := h s hs
    refine ⟨?_, hpos⟩
    intro hzero
    rw [hzero, div_zero, Complex.zero_re] at hpos
    linarith

/-- Strict anti-Herglotz behavior of the critical-line pullback.-/
def EntireXiPullback.StrictAntiHerglotzSign : Prop :=
  StrictAntiHerglotzUHP (logDerivativeResponse EntireXiPullback)

/-- Differentiating `xi(1 - s) = xi(s)` gives
`xi'(1 - s) = -xi'(s)`.
@isnad1 id=eq.0h1v.s6.28bffd71682c from=translated src=- shape=b597386d vocab=171d02ef
-/
theorem entireRiemannXi_deriv_one_sub (s : ℂ) :
    deriv entireRiemannXi (1 - s) = -deriv entireRiemannXi s := by
  have hinner : HasDerivAt (fun w : ℂ => 1 - w) (-1) s :=
    by
      convert (hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id s) using 1
      all_goals first
        | rfl
        | simp only [zero_sub]
  have houter : HasDerivAt entireRiemannXi
      (deriv entireRiemannXi (1 - s)) (1 - s) :=
    (entireRiemannXi_differentiableAt (1 - s)).hasDerivAt
  have hcomp : HasDerivAt
      (fun w : ℂ => entireRiemannXi (1 - w))
      (deriv entireRiemannXi (1 - s) * (-1)) s := by
    simpa [Function.comp_def] using houter.comp s hinner
  have hfun : (fun w : ℂ => entireRiemannXi (1 - w)) = entireRiemannXi :=
    funext entireRiemannXi_one_sub
  have hderiv_fun :
      deriv (fun w : ℂ => entireRiemannXi (1 - w)) s =
        deriv entireRiemannXi s :=
    congrArg (fun f : ℂ → ℂ => deriv f s) hfun
  have hderiv :
      deriv entireRiemannXi s =
        deriv entireRiemannXi (1 - s) * (-1) := by
    rw [← hderiv_fun]
    exact hcomp.deriv
  have hderiv' :
      deriv entireRiemannXi s = -deriv entireRiemannXi (1 - s) := by
    simpa using hderiv
  have hneg := congrArg Neg.neg hderiv'
  simpa using hneg.symm

/-- Functional equation for the totalized logarithmic derivative.
@isnad1 id=eq.0h1v.s7.97b8718ddaae from=translated src=- shape=287b67af vocab=b79c6836
-/
theorem entireRiemannXi_logDeriv_one_sub (s : ℂ) :
    deriv entireRiemannXi (1 - s) / entireRiemannXi (1 - s) =
      -(deriv entireRiemannXi s / entireRiemannXi s) := by
  rw [entireRiemannXi_deriv_one_sub, entireRiemannXi_one_sub]
  ring

/-- The strict right-half-plane condition for xi is exactly the strict
anti-Herglotz condition for its critical-line pullback. The functional
equation moves the pullback's left half-plane to the classical right half.
@isnad1 id=iff.0h0v.s1.16466f8cfc32 from=translated src=- shape=25b03439 vocab=f2741a5a
-/
theorem entireXi_rightHalfPlaneStrictLogDerivSign_iff_pullback :
    EntireXi.rightHalfPlaneStrictLogDerivSign ↔
      EntireXiPullback.StrictAntiHerglotzSign := by
  constructor
  · intro hright z hz
    rw [EntireXiPullback_logDeriv_chain_rule,
      Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, zero_add, one_mul]
    let s : ℂ := (1 / 2 : ℂ) + Complex.I * z
    have hs_left : s.re < (1 / 2 : ℝ) := by
      change ((1 / 2 : ℂ) + Complex.I * z).re < (1 / 2 : ℝ)
      rw [critical_shift_re]
      linarith
    have hone_right : (1 / 2 : ℝ) < (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have hpos := hright (1 - s) hone_right
    have hfe := congrArg Complex.re (entireRiemannXi_logDeriv_one_sub s)
    rw [Complex.neg_re] at hfe
    change (deriv entireRiemannXi s / entireRiemannXi s).re < 0
    linarith
  · intro hpull s hs
    let u : ℂ := 1 - s
    let z : ℂ := -Complex.I * (u - (1 / 2 : ℂ))
    have hu_left : u.re < (1 / 2 : ℝ) := by
      change (1 - s).re < (1 / 2 : ℝ)
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have hshift : (1 / 2 : ℂ) + Complex.I * z = u := by
      dsimp [z]
      ring_nf
      rw [Complex.I_sq]
      ring
    have hz : 0 < z.im := by
      have hre := critical_shift_re z
      rw [hshift] at hre
      linarith
    have hneg := hpull z hz
    rw [EntireXiPullback_logDeriv_chain_rule,
      Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, zero_add, one_mul, hshift] at hneg
    have hone : 1 - u = s := by
      dsimp [u]
      ring
    have hfe := congrArg Complex.re (entireRiemannXi_logDeriv_one_sub u)
    rw [hone, Complex.neg_re] at hfe
    linarith

/-- The strict right-half-plane Lagarias sign condition implies Mathlib's
literal Riemann hypothesis, unconditionally.
@isnad1 id=riemannh.1h0v.s1.4008ce57e055 from=translated src=- shape=1d48f1ac vocab=7b6c7c52
-/
theorem riemannHypothesis_of_entireXi_rightHalfPlaneStrictLogDerivSign
    (h : EntireXi.rightHalfPlaneStrictLogDerivSign) :
    RiemannHypothesis := by
  have hpull : EntireXiPullback.StrictAntiHerglotzSign :=
    entireXi_rightHalfPlaneStrictLogDerivSign_iff_pullback.mp h
  apply riemannHypothesis_iff_entireXiPullback_zeros_real.mpr
  exact entire_function_roots_real_of_analytic_nontrivial
    EntireXiPullback
    (fun z _hz => EntireXiPullback_analyticAt z)
    EntireXiPullback_nontrivial_holds
    (fun z hz _hz_nonzero => hpull.antiHerglotz z hz)
    (EntireXiPullback_schwarz
      (EntireRiemannXiRegularity_of_schwarz EntireXi.schwarzReflection_holds))

/-- Classical punctured-domain Lagarias positivity implies Mathlib's RH.
@isnad1 id=riemannh.1h0v.s1.dc88764c8c3b from=translated src=- shape=1d48f1ac vocab=bc8e78e0
-/
theorem riemannHypothesis_of_entireXi_lagariasPositivity
    (h : EntireXi.LagariasPositivity) :
    RiemannHypothesis :=
  riemannHypothesis_of_entireXi_rightHalfPlaneStrictLogDerivSign
    (entireXi_lagariasPositivity_iff_rightHalfPlaneStrictLogDerivSign.mp h)

/-- The explicit classical input package for the reverse Lagarias direction.

Besides the exact function identity, this packages a finite multiplicity at
the pullback origin and a repetition-permitting sequence of nonzero remaining
locations with inverse-square summability. The latter implies eventual escape
and hence infinitely many indexed locations. The exact equality encodes the
full divisor and its multiplicities. Nonvanishing of `C` and reality of `b`
are deliberately not fields: they are derived from the pullback's known
nontriviality and Schwarz reflection.-/
structure EntireXiPullbackExpAffineHadamardData : Type where
  originMultiplicity : ℕ
  C : ℂ
  a : ℂ
  b : ℂ
  /-- A multiplicity-bearing enumeration: repeated locations encode repeated
  zeros. This is deliberately not the subtype of distinct xi zeros.-/
  zeroLoc : ℕ → ℂ
  zeroData : NatHadamardZeroInvSqData zeroLoc
  /-- The origin factor records any central zero separately from the nonzero
  sequence. Eventual escape is derived from inverse-square summability rather
  than included as a field.-/
  factorization :
    EntireXiPullback =
      expAffineGenusOneProductWithOriginMultiplicity
        originMultiplicity C a b zeroLoc

/-- Exact factorization plus the known nontriviality of the xi pullback forces
the affine prefactor constant to be nonzero.
@isnad1 id=ne.0h1v.s3.16f79b90881f from=translated src=- shape=a311c14d vocab=42f66c17
-/
theorem EntireXiPullbackExpAffineHadamardData.constant_ne_zero
    (H : EntireXiPullbackExpAffineHadamardData) :
    H.C ≠ 0 := by
  intro hC
  obtain ⟨z, hz⟩ := EntireXiPullback_nontrivial_holds
  apply hz
  rw [H.factorization]
  simp [expAffineGenusOneProductWithOriginMultiplicity,
    expAffineGenusOneProduct, hC]

/-- The factorization records a central zero exactly when the explicit origin
multiplicity is nonzero.
@isnad1 id=iff.0h1v.s4.54fa0499032b from=translated src=- shape=44a7bd5e vocab=75828b43
-/
theorem EntireXiPullbackExpAffineHadamardData.center_zero_iff
    (H : EntireXiPullbackExpAffineHadamardData) :
    EntireXiPullback 0 = 0 ↔ H.originMultiplicity ≠ 0 := by
  rw [H.factorization]
  simp [expAffineGenusOneProductWithOriginMultiplicity,
    expAffineGenusOneProduct, infiniteHadamardProduct_zero,
    H.constant_ne_zero]

/-- The explicit origin exponent in the xi factorization package is exactly
the analytic order of the pullback at the origin.
@isnad1 id=eq.0h1v.s4.1ea907e04918 from=translated src=- shape=aecb75e5 vocab=a593dbd1
-/
theorem EntireXiPullbackExpAffineHadamardData.analyticOrderAt_zero
    (H : EntireXiPullbackExpAffineHadamardData) :
    analyticOrderAt EntireXiPullback 0 =
      (H.originMultiplicity : ℕ∞) := by
  rw [H.factorization]
  exact
    expAffineGenusOneProductWithOriginMultiplicity_analyticOrderAt_zero
      (C := H.C) (a := H.a) (b := H.b)
      H.originMultiplicity H.constant_ne_zero H.zeroLoc H.zeroData

/-- The origin together with the indexed nonzero locations exhausts the zero
set of the full pullback. Repeated indices carry multiplicity, but this theorem
records only set-level equality; an analytic-order theorem is separate.
@isnad1 id=iff.0h2v.s5.db05a18d370e from=translated src=- shape=fdcb5171 vocab=595d526b
-/
theorem EntireXiPullbackExpAffineHadamardData.zero_iff_origin_or_exists_zeroLoc
    (H : EntireXiPullbackExpAffineHadamardData) (z : ℂ) :
    EntireXiPullback z = 0 ↔
      (z = 0 ∧ H.originMultiplicity ≠ 0) ∨
        ∃ i : ℕ, z = H.zeroLoc i := by
  rw [H.factorization]
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hpow | hbase
    · left
      have hz : z = 0 := by
        by_contra hz
        exact (pow_ne_zero H.originMultiplicity hz) hpow
      refine ⟨hz, ?_⟩
      intro hm
      rw [hm] at hpow
      simp at hpow
    · right
      by_contra hindexed
      push Not at hindexed
      have hpref_ne : H.C * Complex.exp (H.a + H.b * z) ≠ 0 :=
        mul_ne_zero H.constant_ne_zero (Complex.exp_ne_zero _)
      have hprod_ne : infiniteHadamardProduct H.zeroLoc z ≠ 0 :=
        H.zeroData.toHadamardZeroInvSqSummability.infiniteProduct_ne_zero hindexed
      exact (mul_ne_zero hpref_ne hprod_ne) hbase
  · rintro (⟨rfl, hm⟩ | ⟨i, rfl⟩)
    · simp [expAffineGenusOneProductWithOriginMultiplicity, hm]
    · unfold expAffineGenusOneProductWithOriginMultiplicity
      unfold expAffineGenusOneProduct
      rw [infiniteHadamardProduct_eq_zero_at_zeroLoc H.zeroData.zero_ne i]
      simp

end OverflowResidueRH

/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.JacobianTwo.JacobianTwo.QuadraticDenominatorDescent
import Tengoku.JacobianTwo.JacobianTwo.QuadraticDirectPackage
import Tengoku.Seed.RingTheory.EuclideanDomain
import Tengoku.Seed.Tactic.FieldSimp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The reduced-center GCD descent

If `h` does not divide `g`, divide both by their gcd.  The center of the
quadratic then has a reduced nonunit denominator `q`, and the centered
residual has denominator `q^2` with numerator coprime to `q`.  The abstract
denominator descent therefore contradicts the polynomial specialization in
the direct quadratic certificate.

This proof uses only gcd identities and coprimality.  No irreducible factor or
valuation is selected.
-/

noncomputable section

open scoped Polynomial Polynomial.Bivariate
open Polynomial

namespace JacobianTwo.QuadraticGCDDescent

open JacobianTwo.QuadraticDenominatorDescent
open JacobianTwo.QuadraticDirectPackage
open JacobianTwo.VariableLeadingQuadratic

variable {K : Type*} [Field K] [CharZero K]

/-- A reduced presentation of the quadratic center and centered residual.
The denominator is a genuine nonunit and both numerators are coprime to it.-/
structure ReducedCenterData (eps : K) (h g f : K[X]) where
  z : K[X]
  q : K[X]
  N : K[X]
  q_ne_zero : q ≠ 0
  q_nonunit : ¬ IsUnit q
  z_coprime_q : IsCoprime z q
  N_coprime_q : IsCoprime N q
  center_eq :
    fractionQuadraticCenter eps h g =
      algebraMap K[X] (FractionRing K[X]) z /
        algebraMap K[X] (FractionRing K[X]) q
  residual_eq :
    fractionQuadraticCenteredResidual eps h g f =
      algebraMap K[X] (FractionRing K[X]) N /
        algebraMap K[X] (FractionRing K[X]) q ^ 2

/-- If `h` does not divide `g`, gcd reduction produces a noncancelling
denominator for both the center and the centered residual.-/
theorem exists_reducedCenterData_of_not_dvd
    {eps : K} {h g f : K[X]}
    (heps : eps ≠ 0) (hh : h ≠ 0) (hnot : ¬ h ∣ g) :
    Nonempty (ReducedCenterData eps h g f) := by
  classical
  letI : GCDMonoid K[X] := EuclideanDomain.gcdMonoid K[X]
  let d : K[X] := GCDMonoid.gcd g h
  let z : K[X] := g / d
  let r : K[X] := h / d
  let q : K[X] := C (2 * eps) * r
  let N : K[X] := f * q ^ 2 - C eps * z ^ 2
  have htwoeps : 2 * eps ≠ 0 := mul_ne_zero two_ne_zero heps
  have hscalar_ne : C (2 * eps) ≠ (0 : K[X]) := C_ne_zero.mpr htwoeps
  have hscalar_unit : IsUnit (C (2 * eps) : K[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr htwoeps)
  have hd_ne : d ≠ 0 := by
    exact gcd_ne_zero_of_right hh
  have hz_factor : d * z = g := by
    exact EuclideanDomain.mul_div_cancel' hd_ne (GCDMonoid.gcd_dvd_left g h)
  have hr_factor : d * r = h := by
    exact EuclideanDomain.mul_div_cancel' hd_ne (GCDMonoid.gcd_dvd_right g h)
  have hr_ne : r ≠ 0 := by
    exact right_div_gcd_ne_zero hh
  have hzr : IsCoprime z r := by
    exact isCoprime_div_gcd_div_gcd hh
  have hq_ne : q ≠ 0 := by
    exact mul_ne_zero hscalar_ne hr_ne
  have hzq : IsCoprime z q := by
    exact (isCoprime_mul_unit_left_right hscalar_unit z r).mpr hzr
  have hq_nonunit : ¬ IsUnit q := by
    intro hq_unit
    have hr_unit : IsUnit r := (IsUnit.mul_iff.mp hq_unit).2
    apply hnot
    rw [← hr_factor]
    exact (hr_unit.mul_right_dvd).2 (GCDMonoid.gcd_dvd_left g h)
  have hCeps_unit : IsUnit (C eps : K[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr heps)
  have hbase : IsCoprime (-(C eps) * z ^ 2) q := by
    have hminusCeps_unit : IsUnit (-(C eps) : K[X]) := hCeps_unit.neg
    exact (isCoprime_mul_unit_left_left hminusCeps_unit (z ^ 2) q).mpr
      hzq.pow_left
  have hNq : IsCoprime N q := by
    have hNform : N = q * (f * q) + (-(C eps) * z ^ 2) := by
      dsimp [N]
      ring
    rw [hNform]
    exact hbase.mul_add_left_left (f * q)
  have hd_map_ne :
      algebraMap K[X] (FractionRing K[X]) d ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective K[X] (FractionRing K[X])).ne hd_ne
  have hq_map_ne :
      algebraMap K[X] (FractionRing K[X]) q ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective K[X] (FractionRing K[X])).ne hq_ne
  have hcenter :
      fractionQuadraticCenter eps h g =
        algebraMap K[X] (FractionRing K[X]) z /
          algebraMap K[X] (FractionRing K[X]) q := by
    simp only [fractionQuadraticCenter, quadraticCenter,
      toPolynomialFractionField]
    rw [← hz_factor, ← hr_factor]
    simp only [map_mul, q, map_ofNat]
    field_simp [hd_map_ne]
  have hresidual :
      fractionQuadraticCenteredResidual eps h g f =
        algebraMap K[X] (FractionRing K[X]) N /
          algebraMap K[X] (FractionRing K[X]) q ^ 2 := by
    simp only [fractionQuadraticCenteredResidual, quadraticCenteredResidual,
      toPolynomialFractionField, hcenter]
    dsimp [N]
    simp only [map_sub, map_mul, map_pow]
    field_simp [hq_map_ne]
  exact ⟨
    { z := z
      q := q
      N := N
      q_ne_zero := hq_ne
      q_nonunit := hq_nonunit
      z_coprime_q := hzq
      N_coprime_q := hNq
      center_eq := hcenter
      residual_eq := hresidual }⟩

/-- The direct fraction-field certificate forces the square root `h` of the
quadratic leading coefficient to divide the linear coefficient `g`.-/
theorem h_dvd_g_of_certificate
    {eps k lam : K} {h g f : K[X]} {P : K[X][Y]}
    {H B : (FractionRing K[X])[X]} {m : ℕ}
    (heps : eps ≠ 0) (hh : h ≠ 0)
    (cert : Certificate eps k lam h g f P H B m) :
    h ∣ g := by
  by_contra hnot
  obtain ⟨data⟩ :=
    exists_reducedCenterData_of_not_dvd (f := f) heps hh hnot
  have hnotmem :
      (algebraMap K[X] (FractionRing K[X]) data.z /
          algebraMap K[X] (FractionRing K[X]) data.q) *
          B.eval (algebraMap K[X] (FractionRing K[X]) f) ∉
        Set.range (algebraMap K[X] (FractionRing K[X])) := by
    apply mul_eval_not_mem_base_of_exists
      (K := K) (R := K[X]) (L := FractionRing K[X])
      data.q data.z data.N f B m
      data.q_ne_zero data.q_nonunit data.z_coprime_q data.N_coprime_q
      cert.oddDegree_eq
    intro j hj
    obtain ⟨S, hScoeff, hSdegree, hSlead⟩ := cert.coefficientWitnesses j hj
    refine ⟨S, ?_, hSdegree, hSlead⟩
    rw [data.residual_eq] at hScoeff
    exact hScoeff
  apply hnotmem
  rw [← data.center_eq]
  simpa only [toPolynomialFractionField] using cert.centerMulEval_mem_base

end JacobianTwo.QuadraticGCDDescent

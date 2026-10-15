/-
Copyright (c) 2026 James Huang, Samuël Borza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Huang, Samuël Borza
-/
module

public import Tengoku.LeanPool.LeanPool.IsTranscendentalPi.SubsetSumPolynomial
public import Tengoku.LeanPool.LeanPool.IsTranscendentalPi.NivenPolynomials
public import Tengoku

/-!
# Scaled auxiliary polynomial

The symmetric polynomial `∑ᵢ T(Xᵢ)` and its evaluation, providing the algebraic
input to the auxiliary integer in Niven's proof.
-/

@[expose] public section

open Polynomial
open Multiset

open scoped Polynomial
open scoped BigOperators

noncomputable section

/-- The symmetric polynomial `∑ᵢ₌₀ⁿ⁻¹ T(Xᵢ)`. -/
def MvPolynomialSumX {R : Type*} [CommSemiring R] (T : Polynomial R) (n : ℕ) :
    MvPolynomial (Fin n) R :=
  ∑ i : Fin n, Polynomial.aeval (MvPolynomial.X i) T

/-- Evaluating `∑ᵢ₌₀ⁿ⁻¹ T(Xᵢ)` at `a` gives `∑ᵢ₌₀ⁿ⁻¹ T(aᵢ)`.
@isnad1 id=eq.0h5v.s8.e90f3047a048 from=translated src=- shape=72b5f048 vocab=817f01d3
-/
lemma aeval_MvPolynomialSumX
    {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (T : Polynomial R) (n : ℕ) (a : Fin n → S) :
    MvPolynomial.aeval (σ := Fin n) (R := R) (S₁ := S) a (MvPolynomialSumX T n) =
      ∑ i : Fin n, Polynomial.aeval (a i) T := by
  rw [MvPolynomialSumX, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  simpa using
    (Polynomial.map_aeval_eq_aeval_map (S := MvPolynomial (Fin n) R) (T := R) (U := S)
    (φ := RingHom.id R) (ψ := (MvPolynomial.aeval (σ := Fin n) (R := R) (S₁ := S) a).toRingHom)
    (h := by ext r; simp) (p := T) (a := MvPolynomial.X i))

/-- The polynomial `∑ᵢ₌₀ⁿ⁻¹ T(Xᵢ)` is symmetric in the variables `X₀, …, Xₙ₋₁`.
@isnad1 id=issymmet.0h3v.s4.f8e64e7af20a from=translated src=- shape=1823459f vocab=44a6645b
-/
lemma MvPolynomialSumX_isSymmetric {R : Type*} [CommSemiring R] (T : Polynomial R) (n : ℕ) :
    MvPolynomial.IsSymmetric (MvPolynomialSumX T n) := by
  intro e
  rw [MvPolynomialSumX, map_sum]
  simp_rw [MvPolynomial.rename_polynomial_aeval_X]
  exact (Equiv.sum_comp e fun i : Fin n => Polynomial.aeval (MvPolynomial.X i) T)

/-- For `P = ∑ₖ₌₀ⁿ⁻¹ cₖ Xᵏ`, this defines `∑ₖ (cₖ / cᵏ) (x₁ᵏ + ⋯ + xₙᵏ)`. -/
def scaledMvPolynomial {R K : Type*} [CommSemiring R] [Semifield K] [Algebra R K]
    (P : Polynomial R) (c : K) (n : ℕ) : MvPolynomial (Fin n) K :=
    ∑ k ∈ Finset.range (P.natDegree + 1),
      MvPolynomial.C ((algebraMap R K (P.coeff k)) / c ^ k) * MvPolynomial.psum (Fin n) K k

/-- `∑ⱼ₌₀ⁿ⁻¹ Gₚ(aⱼ) = (1 / p!) ∑ᵢ₌ₚ^deg(Fₚ) ∑ⱼ₌₀ⁿ⁻¹ Fₚ⁽ⁱ⁾(aⱼ)`.
@isnad1 id=eq.0h6v.s9.84a98c19bf57 from=translated src=- shape=5b00642a vocab=b650e58d
-/
lemma sum_aeval_Gp_eq_one_div_factorial_sum_iterate_derivative_Fp
    {R K : Type*} [CommSemiring R] [Field K] [CharZero K] [Algebra R K]
    (Q : R[X]) (p n : ℕ) (a : Fin n → K) :
    (∑ j : Fin n, aeval (a j) (Gp Q p))
      = (1 / (p.factorial : K)) * (∑ i ∈ Finset.Icc p (Fp Q p).natDegree,
          ∑ j : Fin n, aeval (a j) ((derivative^[i]) (Fp Q p))) := by
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p)]
  rw [mul_comm, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  simpa [sumStartpDerivFp] using
    congrArg (fun P : R[X] => aeval (a j) P)
      (factorise_sumIteratedDerivPoly Q p).symm

/-- The integer coefficients `cˢ⁻ᵏ · (i! / p!) · (k-Coeff of Sₚ)`. -/
def ScaledCoeffDerivFp (T : ℤ[X]) (c : ℤ) (p s i k : ℕ) : ℤ :=
  (c ^ (s - k)) * (((i.factorial / p.factorial : ℕ) : ℤ) * (Sp T p i).coeff k)

/-- The symmetric polynomial encoding the scaled `i`-th derivative of `Fₚ` through power
sums, i.e. `∑ₖ₌₀^deg(Fₚ) cˢ⁻ᵏ · (i! / p!) · (k-Coeff of Sₚ) · (X₀ᵏ + ⋯ + Xₙ₋₁ᵏ)` . -/
def RpolyFp (T : ℤ[X]) (c : ℤ) (p s i n : ℕ) : MvPolynomial (Fin n) ℤ :=
  ∑ k ∈ Finset.range ((Fp T p).natDegree + 1),
    MvPolynomial.C (ScaledCoeffDerivFp T c p s i k) * MvPolynomial.psum (Fin n) ℤ k

/-- `((cˢ⁻ᵏ) / p!) · (k-th coeff of Fₚ⁽ⁱ⁾) = cˢ⁻ᵏ · (i! / p!) · (k-Coeff of Sₚ)`.
@isnad1 id=eq.1h7v.s8.f98de3d0ff34 from=translated src=- shape=62dbf604 vocab=169feaef
-/
lemma ScaledCoeffDerivFp_from_Sp
    {K : Type*} [Field K] [CharZero K] [Algebra ℤ K]
    (T : ℤ[X]) (c : ℤ) (p s i k : ℕ) (hpi : p ≤ i) :
    c ^ (s - k) / p.factorial * ((derivative^[i] (Fp T p)).coeff k : K)
      = algebraMap ℤ K (ScaledCoeffDerivFp T c p s i k) := by
  rw [iterate_derivative_Fp_eq_factorial_Sp T p i]
  simp only [nsmul_eq_mul, coeff_natCast_mul, Int.cast_mul, Int.cast_natCast, ScaledCoeffDerivFp,
    Int.natCast_ediv, eq_intCast, Int.cast_pow]
  rw [Int.cast_div (by exact_mod_cast Nat.factorial_dvd_factorial hpi)
    (by exact_mod_cast Nat.factorial_ne_zero p)]
  field_simp
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm]

/-- Evaluating ``∑ₖ (cₖ / cᵏ) (x₁ᵏ + ⋯ + xₙᵏ)` at `(c a₀, …, c aₙ₋₁)` gives the scaled sum
`(cˢ / p!) ∑ⱼ₌₀ⁿ⁻¹ Fₚ⁽ⁱ⁾(aⱼ)`.
@isnad1 id=eq.3h7v.s9.3d2e043f6f52 from=translated src=- shape=75460038 vocab=02c0aab3
-/
lemma aeval_RpolyFp_derivative_Fp
    (T : ℤ[X]) (c : ℤ) (p s i n : ℕ) (a : Fin n → ℂ)
    (hpi : p ≤ i) (hs : ((derivative^[i]) (Fp T p)).natDegree ≤ s) (hc : c ≠ 0) :
    MvPolynomial.aeval (σ := Fin n) (R := ℤ) (S₁ := ℂ) (fun m => c * a m)
      (RpolyFp T c p s i n) =
        (c ^ s / p.factorial) * ∑ m : Fin n, aeval (a m) (derivative^[i] (Fp T p)) := by
  rw [RpolyFp, map_sum]
  simp_rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.psum, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Polynomial.aeval_eq_sum_range' (p := (derivative^[i]) (Fp T p))
    (n := (Fp T p).natDegree + 1) (x := a m)]
  · simp_rw [Algebra.smul_def, map_pow, MvPolynomial.aeval_X, mul_pow]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    by_cases hks : k ≤ s
    · rw [← ScaledCoeffDerivFp_from_Sp (K := ℂ) T c p s i k hpi, pow_sub₀ _ (by exact_mod_cast hc)
        hks]
      field_simp [pow_ne_zero k (by exact_mod_cast hc),
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p)]
      rw [algebraMap_int_eq, eq_intCast]
      ring
    · rw [← ScaledCoeffDerivFp_from_Sp (K := ℂ) T c p s i k hpi]
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt hs (lt_of_not_ge hks))]
      simp
  · refine lt_of_le_of_lt
      (((Polynomial.natDegree_iterate_derivative (Fp T p) i).trans (Nat.sub_le _ _)).trans ?_)
      (Nat.lt_succ_self _)
    exact le_rfl

/-- The polynomial `∑ₖ₌₀^deg(Fₚ) cˢ⁻ᵏ · (i! / p!) · (k-Coeff of Sₚ) · (X₀ᵏ + ⋯ + Xₙ₋₁ᵏ)`
is symmetric.
@isnad1 id=issymmet.0h6v.s4.797d8476625e from=translated src=- shape=e9887f36 vocab=643b2b32
-/
lemma RpolyFp_isSymmetric (T : ℤ[X]) (c : ℤ) (p s i n : ℕ) :
    MvPolynomial.IsSymmetric (RpolyFp T c p s i n) := by
  intro e
  simp [RpolyFp]

/-- Suppose that `T = c T` with `T ∈ ℤ[X]`, `T' ∈ ℚ[X]`, and `c ∈ ℤ`. If `a₀, …, aₙ₋₁` are the
roots of `T'` in `ℂ`, then evaluating
`∑ₖ₌₀^deg(Fₚ) cˢ⁻ᵏ · (i! / p!) · (k-Coeff of Sₚ) · (X₀ᵏ + ⋯ + Xₙ₋₁ᵏ)`
at `(c a₀, …, c aₙ₋₁)` gives an integer polynomial expression in the coefficients `T`.
@isnad1 id=ex.5h8v.s9.f06e6864f2ec from=translated src=- shape=cec804fd vocab=d3257211
-/
lemma RpolyFp_at_c_mul_eq_poly_of_monicRescaleOf
    (T : ℤ[X]) (T' : ℚ[X]) (c : ℤ) (p s i d : ℕ) (a : Fin d → ℂ)
    (hc : c ≠ 0) (hmonic : T'.Monic) (hd : T'.natDegree = d)
    (hT : T.map (Int.castRingHom ℚ) = C (c : ℚ) * T')
    (hroots' : T'.aroots ℂ = valuesFin a) :
    ∃ Q : MvPolynomial (Fin d) ℤ,
      MvPolynomial.aeval (σ := Fin d) (R := ℤ) (S₁ := ℂ)
        (fun j : Fin d => (c : ℂ) * a j) (RpolyFp T c p s i d)
      = algebraMap ℤ ℂ (MvPolynomial.aeval (σ := Fin d) (R := ℤ) (S₁ := ℤ)
        (fun j : Fin d => (-1) ^ (j.1 + 1) * (monicRescaleOf T d c).coeff (d - (j.1 + 1))) Q) :=
  symmetric_poly_at_roots_eq_poly_of_esymm
    (B := monicRescaleOf T d c)
    (a := fun j : Fin d => (c : ℂ) * a j)
    (hmonic := monic_monicRescaleOf T d c)
    (hroots := aroots_monicRescaleOf T T' d c a hc hmonic hd hT hroots')
    (P := RpolyFp T c p s i d)
    (hP := RpolyFp_isSymmetric T c p s i d)

/-- The integer witness for evaluating
`∑ₖ₌₀^deg(Fₚ) cˢ⁻ᵏ · (i! / p!) · (k-Coeff of Sₚ) · (X₀ᵏ + ⋯ + X_{d-1}ᵏ)`
at `(c a₀, …, c a_{d-1})`. -/
def intAevalRpoly
    (T : ℤ[X]) (T' : ℚ[X]) (c : ℤ) (p s d : ℕ) (a : Fin d → ℂ) (hc : c ≠ 0) (hmonic : T'.Monic)
    (hd : T'.natDegree = d) (hT : T.map (Int.castRingHom ℚ) = C (c : ℚ) * T')
    (hroots' : T'.aroots ℂ = valuesFin a) :
    ℕ → ℤ := fun i =>
      MvPolynomial.aeval (σ := Fin d) (R := ℤ) (S₁ := ℤ)
        (fun j : Fin d => (-1) ^ (j.1 + 1) * (monicRescaleOf T d c).coeff (d - (j.1 + 1)))
        (Classical.choose
          (RpolyFp_at_c_mul_eq_poly_of_monicRescaleOf T T' c p s i d a hc hmonic hd hT hroots'))

/-- The integer witness for `cᵖᵈ⁻¹ ∑ₘ Gₚ(aₘ)`. -/
def intSumAevalGp
    (T : ℤ[X]) (T' : ℚ[X]) (c : ℤ) (d : ℕ) (a : Fin d → ℂ) (hc : c ≠ 0) (hmonic : T'.Monic)
    (hd : T'.natDegree = d) (hT : T.map (Int.castRingHom ℚ) = C (c : ℚ) * T')
    (hroots' : T'.aroots ℂ = valuesFin a) :
    ℕ → ℤ := fun p =>
      ∑ i ∈ Finset.Icc p (Fp T p).natDegree,
        intAevalRpoly T T' c p (p * d - 1) d a hc hmonic hd hT hroots' i

/-- Suppose that `T = c T` with `T ∈ ℤ[X]`, `T' ∈ ℚ[X]` monic of degree `d`, and `c ∈ ℤ`.
If `a₀, …, aₙ₋₁` are the roots of `T'` in `ℂ`, then the sum `c^(p * d - 1) ∑_m Gₚ(a_m)`
is an integer.
@isnad1 id=eq.6h6v.s8.c2b0c5daac3e from=translated src=- shape=8d340771 vocab=053afef8
-/
lemma SumAevalGp_as_intSumAevalGp
    (T : ℤ[X]) (T' : ℚ[X]) (c : ℤ) (p d : ℕ) (a : Fin d → ℂ)
    (hc : c ≠ 0) (hp : 0 < p) (hmonic : T'.Monic) (hd : T'.natDegree = d)
    (hT : T.map (Int.castRingHom ℚ) = C (c : ℚ) * T')
    (hroots' : T'.aroots ℂ = valuesFin a) :
    ((c : ℂ) ^ (p * d - 1)) * (∑ m : Fin d, aeval (a m) (Gp T p)) =
      (intSumAevalGp T T' c d a hc hmonic hd hT hroots' p : ℂ) := by
  rw [intSumAevalGp, sum_aeval_Gp_eq_one_div_factorial_sum_iterate_derivative_Fp T p d a,
    ← mul_assoc, Finset.mul_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hpi : p ≤ i := (Finset.mem_Icc.mp hi).1
  have hT0 : T ≠ 0 := RescaledOf_nonZero T T' c hc hmonic.ne_zero hT
  have hs' := natDegree_iterate_derivative_Fp_le T p i hT0
  rw [RescaledOf_natDegree T T' c hc hT, hd] at hs'
  have hdeg : ((derivative^[i]) (Fp T p)).natDegree ≤ p * d - 1 := by omega
  apply Eq.trans
  · simpa [div_eq_mul_inv] using
      (aeval_RpolyFp_derivative_Fp T c p (p * d - 1) i d a hpi hdeg hc).symm
  · simpa [intSumAevalGp, intAevalRpoly] using
      Classical.choose_spec (RpolyFp_at_c_mul_eq_poly_of_monicRescaleOf
                              T T' c p (p * d - 1) i d a hc hmonic hd hT hroots')

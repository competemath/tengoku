import Tengoku
import Tengoku.Seed.Algebra.Polynomial.Roots
import Tengoku.Seed.RingTheory.Localization.Integral
import Tengoku.Seed.FieldTheory.Perfect
import Tengoku.Seed.RingTheory.Polynomial.Resultant.Basic
import Tengoku.Seed.RingTheory.Localization.FractionRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Remove repeated factors over the fraction field, clear denominators,
and use a resultant to obtain simple roots outside a finite input set.
The new relation contains every root of the original relation there; no
smoothness or semialgebraic projection is assumed. This is local algebra
for regularizing curve parametrizations, not an argument at infinity. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Polynomial

theorem fraction_polynomial_dvd_clear_denominator
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (P Q : Polynomial R)
    (h : P.map (algebraMap R K) ∣ Q.map (algebraMap R K)) :
    ∃ c : R, c ≠ 0 ∧ P ∣ C c * Q := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨c, hc, he⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) T
  refine ⟨c, nonZeroDivisors.ne_zero hc, ?_⟩
  refine ⟨IsLocalization.integerNormalization (nonZeroDivisors R) T, ?_⟩
  apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_mul, he, hT]
  rw [← algebraMap_smul K c T, smul_eq_C_mul]
  ring

theorem exists_generically_separable_polynomial
    {R K : Type*} [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K]
    (P : Polynomial R) (hP : P ≠ 0) :
    ∃ Q : Polynomial R, Q ≠ 0 ∧ (Q.map (algebraMap R K)).Separable ∧
      ∃ c : R, c ≠ 0 ∧ ∃ n : ℕ, P ∣ C c * Q ^ n := by
  have hPK : P.map (algebraMap R K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (IsFractionRing.injective R K)).mpr hP
  obtain ⟨q, n, hsq, _, hdiv⟩ := exists_squarefree_dvd_pow_of_ne_zero hPK
  have hsep : q.Separable := PerfectField.separable_iff_squarefree.mpr hsq
  let Q := IsLocalization.integerNormalization (nonZeroDivisors R) q
  obtain ⟨b, hb, he⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) q
  have hbK : algebraMap R K b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero hb)
  have he' : Q.map (algebraMap R K) = C (algebraMap R K b) * q := by
    rw [he, ← algebraMap_smul K b q, smul_eq_C_mul]
  have hQsep : (Q.map (algebraMap R K)).Separable := by
    rw [he']
    exact hsep.unit_mul (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hbK))
  have hdiv' : P.map (algebraMap R K) ∣ (Q ^ n).map (algebraMap R K) := by
    rw [Polynomial.map_pow, he', mul_pow]
    exact dvd_mul_of_dvd_right hdiv _
  obtain ⟨c, hc, hd⟩ := fraction_polynomial_dvd_clear_denominator P (Q ^ n) hdiv'
  exact ⟨Q, fun h => hQsep.ne_zero (by rw [h, Polynomial.map_zero]), hQsep, c, hc, n, hd⟩

theorem fraction_separable_resultant_ne_zero
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (Q : Polynomial R) (hQ : (Q.map (algebraMap R K)).Separable) :
    Q.resultant Q.derivative ≠ 0 := by
  have h := Polynomial.resultant_ne_zero _ _ hQ
  rw [Polynomial.derivative_map,
    Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective R K),
    Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective R K),
    Polynomial.resultant_map_map] at h
  exact fun hz => h (by rw [hz, map_zero])

theorem polynomial_simple_relation_outside_finite
    (P : Polynomial (Polynomial ℝ)) (hP : P ≠ 0) :
    ∃ Q : Polynomial (Polynomial ℝ), Q ≠ 0 ∧ ∃ E : Set ℝ, E.Finite ∧
      ∀ x ∉ E, ∀ y : ℝ, (P.map (Polynomial.evalRingHom x)).eval y = 0 →
        (Q.map (Polynomial.evalRingHom x)).eval y = 0 ∧
        ((Q.map (Polynomial.evalRingHom x)).derivative).eval y ≠ 0 := by
  obtain ⟨Q, hQ, hsep, c, hc, n, hdiv⟩ :=
    exists_generically_separable_polynomial (K := FractionRing (Polynomial ℝ)) P hP
  have hres := fraction_separable_resultant_ne_zero Q hsep
  let D := c * Q.leadingCoeff * Q.resultant Q.derivative
  have hD : D ≠ 0 := mul_ne_zero
    (mul_ne_zero hc (Polynomial.leadingCoeff_ne_zero.mpr hQ)) hres
  refine ⟨Q, hQ, {x | D.eval x = 0}, Polynomial.finite_setOfPred_isRoot hD, ?_⟩
  intro x hx y hy
  change D.eval x ≠ 0 at hx
  have hx' : c.eval x ≠ 0 ∧ Q.leadingCoeff.eval x ≠ 0 ∧
      (Q.resultant Q.derivative).eval x ≠ 0 := by
    simpa only [ne_eq, D, Polynomial.eval_mul, mul_eq_zero, not_or, and_assoc] using hx
  have hroot : (Q.map (Polynomial.evalRingHom x)).eval y = 0 := by
    have hv := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero
      (Polynomial.map_dvd (Polynomial.evalRingHom x) hdiv) hy
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.coe_evalRingHom] at hv
    exact eq_zero_of_pow_eq_zero (Or.resolve_left (mul_eq_zero.mp hv) hx'.1)
  refine ⟨hroot, ?_⟩
  intro hder
  by_cases hdeg : Q.natDegree = 0
  · have heq := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    have hz : Q.leadingCoeff.eval x = 0 := by
      rw [← Polynomial.coeff_natDegree, hdeg]
      rw [heq] at hroot
      simpa only [Polynomial.map_C, Polynomial.eval_C, Polynomial.coe_evalRingHom] using hroot
    exact hx'.2.1 hz
  · obtain ⟨a, b, _, _, hab⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
      Q Q.derivative le_rfl le_rfl (Or.inl hdeg)
    have he := congrArg (fun W : Polynomial (Polynomial ℝ) =>
      (W.map (Polynomial.evalRingHom x)).eval y) hab
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.coe_evalRingHom, ← Polynomial.derivative_map,
      hroot, hder, zero_mul, zero_add] at he
    exact hx'.2.2 he.symm

end
end DuistermaatVanDerKallen

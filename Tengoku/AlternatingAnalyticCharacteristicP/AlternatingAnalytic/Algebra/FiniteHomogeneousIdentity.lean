import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Algebra.FullPolarization
import Tengoku.Seed.FieldTheory.Finite.Polynomial
import Tengoku.Seed.RingTheory.MvPolynomial.Homogeneous

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Homogeneous identity principle over a finite field

A homogeneous form of degree `e ≤ q` that vanishes on `F_q^m` is zero (Lemma B.7), also for
coefficients in an extension field or in a vector space. As a consequence, two `k`-linear maps
over `F_q` with `k ≤ q` and the same diagonal have the same grouped polarization sums.
-/

namespace AlternatingAnalytic

open MvPolynomial
open scoped Classical

universe u v

variable {σ : Type v} {R : Type u} [Fintype σ] [Field R]

/-- A homogeneous polynomial at a coordinate unit vector reads its pure-power coefficient.-/
theorem homogeneous_eval_coordinate (p : MvPolynomial σ R) {e : ℕ}
    (hp : p.IsHomogeneous e) (i : σ) :
    MvPolynomial.eval (Pi.single i 1) p = p.coeff (Finsupp.single i e) := by
  classical
  rw [MvPolynomial.eval_eq']
  rw [Finset.sum_eq_single (Finsupp.single i e)]
  · simp [Finsupp.single_apply]
  · intro d hd hdi
    have hdegree : d.degree = e := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hp (MvPolynomial.mem_support_iff.mp hd)
    have hex : ∃ j, j ≠ i ∧ d j ≠ 0 := by
      by_contra h
      push Not at h
      have hvalue : d i = e := by
        rw [← hdegree, Finsupp.degree_eq_sum]
        symm
        apply Finset.sum_eq_single i
        · intro j _ hji
          exact h j hji
        · simp
      apply hdi
      ext j
      by_cases hji : j = i
      · subst j
        simp [hvalue]
      · simp [hji, h j hji]
    obtain ⟨j, hji, hj⟩ := hex
    have hz : (∏ a, (Pi.single i (1 : R) a) ^ d a) = (0 : R) := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [hji, hj]
    rw [hz, mul_zero]
  · intro h
    simp [MvPolynomial.notMem_support_iff.mp h]

/-- A multi-index whose degree equals one of its entries is a pure power.-/
theorem finsupp_eq_single_of_degree_eq {d : σ →₀ ℕ} {i : σ} (h : d.degree = d i) :
    d = Finsupp.single i (d i) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · have hpair : d i + d j ≤ d.degree := by
      rw [Finsupp.degree_eq_sum]
      have hsub : ({i, j} : Finset σ) ⊆ Finset.univ := Finset.subset_univ _
      have hs := Finset.sum_le_sum_of_subset_of_nonneg (f := d) hsub (fun _ _ _ => Nat.zero_le _)
      simpa [Finset.sum_pair (Ne.symm hji)] using hs
    have hj : d j = 0 := by omega
    simp [hji, hj]

/-- A homogeneous form of degree `e ≤ q` vanishing on all points is zero. The case `e = q`
is allowed; it fails for inhomogeneous polynomials.-/
theorem finiteField_homogeneous_eq_zero_sameUniverse {σ : Type u} [Fintype σ] [Fintype R]
    (p : MvPolynomial σ R) {e : ℕ} (hp : p.IsHomogeneous e)
    (he : e ≤ Fintype.card R) (hvanish : ∀ x : σ → R, MvPolynomial.eval x p = 0) :
    p = 0 := by
  classical
  apply MvPolynomial.eq_zero_of_eval_eq_zero σ R p hvanish
  rw [MvPolynomial.mem_restrictDegree]
  intro d hd i
  have hc : p.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  have hdegree : d.degree = e := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hp hc
  have hle : d i ≤ e := (Finsupp.le_degree i d).trans_eq hdegree
  by_contra hbad
  have hq : d i = Fintype.card R := by omega
  have hdi : d i = e := by omega
  have hdform : d = Finsupp.single i e := by
    simpa only [hdi] using finsupp_eq_single_of_degree_eq (hdegree.trans hdi.symm)
  have hpure : p.coeff (Finsupp.single i e) = 0 :=
    (homogeneous_eval_coordinate p hp i).symm.trans (hvanish (Pi.single i 1))
  apply hc
  rw [hdform]
  exact hpure

/-- The homogeneous identity principle, with variables and coefficients in any universes.-/
theorem finiteField_homogeneous_eq_zero [Fintype R]
    (p : MvPolynomial σ R) {e : ℕ} (hp : p.IsHomogeneous e)
    (he : e ≤ Fintype.card R) (hvanish : ∀ x : σ → R, MvPolynomial.eval x p = 0) :
    p = 0 := by
  classical
  let equiv : σ ≃ ULift.{u} (Fin (Fintype.card σ)) :=
    (Fintype.equivFin σ).trans Equiv.ulift.symm
  apply (MvPolynomial.rename_eq_zero_iff_of_injective p equiv.injective).mp
  apply finiteField_homogeneous_eq_zero_sameUniverse (MvPolynomial.rename equiv p)
    hp.rename_isHomogeneous he
  intro x
  rw [MvPolynomial.eval_rename]
  exact hvanish _

end AlternatingAnalytic

namespace VectorPolynomial

variable {R Y σ : Type*} [Field R] [Fintype R] [Fintype σ]
  [AddCommGroup Y] [Module R Y]

end VectorPolynomial

namespace AlternatingAnalytic

variable {R L σ : Type*} [Field R] [Fintype R] [Field L] [Algebra R L] [Fintype σ]

end AlternatingAnalytic

namespace MultilinearMap

variable {K A Y J : Type*} [Field K] [AddCommGroup A] [Module K A]
  [AddCommGroup Y] [Module K Y] [Fintype J] {k : ℕ}

/-- Every nonzero diagonal coefficient of a `k`-linear map has degree `k`.-/
theorem diagonalCoefficients_degree
    (M : MultilinearMap K (fun _ : Fin k => A) Y) (b : J → A)
    (α : J →₀ ℕ) (hα : M.diagonalCoefficients b α ≠ 0) : α.degree = k := by
  classical
  by_contra hdegree
  apply hα
  have hz := M.sumOfType_eq_zero_of_sum_ne b (fun j => α j)
    (by simpa only [Finsupp.degree_eq_sum] using hdegree)
  have heq := M.diagonalCoefficients_apply b (fun j => α j)
  simpa using heq.trans hz

end MultilinearMap

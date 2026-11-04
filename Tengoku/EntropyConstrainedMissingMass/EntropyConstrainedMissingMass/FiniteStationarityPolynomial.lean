import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.ObjectiveCalculus
import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.BranchEntropy
import Tengoku.Seed.Algebra.Polynomial.Roots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Appendix C's nonzero stationarity polynomial, including its root bound. -/
open Polynomial Set
namespace EntropyConstrainedMissingMass
noncomputable section

/-- The Appendix C polynomial, parametrized by the repeated multiplicity `m=N-1`.-/
def finiteStationarityPolynomial (m t : ℕ) : Polynomial ℝ :=
  C (m : ℝ)^t * (1-X)^(t-1) * (1-C ((t : ℝ)+1)*X) -
    (C ((m : ℝ)-1)+X)^(t-1) * (C ((t : ℝ)+1)*X+C ((m : ℝ)-(t : ℝ)-1))

/--
@isnad1 id=eq.0h3v.s7.2f19aecf124b from=translated src=- shape=50dd989e vocab=6c62f564
-/
theorem eval_finiteStationarityPolynomial (m t : ℕ) (z : ℝ) :
    (finiteStationarityPolynomial m t).eval z =
      (m : ℝ)^t*(1-z)^(t-1)*(1-((t : ℝ)+1)*z) -
      ((m : ℝ)-1+z)^(t-1)*(((t : ℝ)+1)*z+(m : ℝ)-(t : ℝ)-1) := by
  simp only [finiteStationarityPolynomial, eval_sub, eval_mul, eval_pow, eval_C, eval_one, eval_X, eval_add]
  ring

/--
@isnad1 id=ne.2h2v.s5.2949ccd02089 from=translated src=- shape=74ce10c0 vocab=0cdd9aea
-/
theorem finiteStationarityPolynomial_ne_zero {m t : ℕ} (hm : 0 < m) (ht : 1 ≤ t) :
    finiteStationarityPolynomial m t ≠ 0 := by
  intro he
  have hz : (finiteStationarityPolynomial m t).eval 1 = 0 := by rw [he]; simp
  rw [eval_finiteStationarityPolynomial] at hz
  have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  by_cases ht1 : t = 1
  · subst t
    norm_num at hz
    nlinarith
  · have htp : 0 < t-1 := by omega
    simp only [sub_self, zero_pow htp.ne', mul_zero, zero_mul, mul_one,
      sub_add_cancel, zero_sub, neg_eq_zero] at hz
    have heq : (t : ℝ)+1+(m : ℝ)-(t : ℝ)-1 = m := by ring
    rw [heq] at hz
    exact (mul_pos (pow_pos hmpos _) hmpos).ne' hz

/-- The stationarity polynomial has degree at most the integer sample size.
@isnad1 id=le.1h2v.s4.95bc53e51043 from=translated src=- shape=95bb35d5 vocab=41605e05
-/
theorem natDegree_finiteStationarityPolynomial_le (m t : ℕ) (ht : 1 ≤ t) :
    (finiteStationarityPolynomial m t).natDegree ≤ t := by
  have hlin₁ : ((1 : Polynomial ℝ)-X).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp only [natDegree_one, natDegree_X]; decide)
  have hlin₂ : ((1 : Polynomial ℝ)-C ((t : ℝ)+1)*X).natDegree ≤ 1 := by
    apply (natDegree_sub_le _ _).trans
    exact max_le (by simp only [natDegree_one]; decide)
      ((natDegree_C_mul_le _ _).trans (le_of_eq natDegree_X))
  have hlin₃ : (C ((m : ℝ)-1)+X).natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans (by simp only [natDegree_C, natDegree_X]; decide)
  have hlin₄ : (C ((t : ℝ)+1)*X+C ((m : ℝ)-(t : ℝ)-1)).natDegree ≤ 1 := by
    apply (natDegree_add_le _ _).trans
    exact max_le ((natDegree_C_mul_le _ _).trans (le_of_eq natDegree_X))
      (by simp only [natDegree_C]; decide)
  have hp₁ : ((1-X)^(t-1) : Polynomial ℝ).natDegree ≤ t-1 := by
    rw [natDegree_pow]
    exact (Nat.mul_le_mul_left (t-1) hlin₁).trans_eq (Nat.mul_one _)
  have hp₂ : ((C ((m : ℝ)-1)+X)^(t-1) : Polynomial ℝ).natDegree ≤ t-1 := by
    rw [natDegree_pow]
    exact (Nat.mul_le_mul_left (t-1) hlin₃).trans_eq (Nat.mul_one _)
  unfold finiteStationarityPolynomial
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · have hc : (C (m : ℝ)^t : Polynomial ℝ).natDegree = 0 := by
      simp only [natDegree_pow, natDegree_C, mul_zero]
    have hleft : (C (m : ℝ)^t*(1-X)^(t-1) : Polynomial ℝ).natDegree ≤ t-1 := by
      have he := (natDegree_mul_le (p := C (m : ℝ)^t) (q := (1-X)^(t-1))).trans
        (Nat.add_le_add_left hp₁ _)
      simpa only [hc, zero_add] using he
    exact (natDegree_mul_le.trans (Nat.add_le_add hleft hlin₂)).trans (by omega)
  · exact (natDegree_mul_le.trans (Nat.add_le_add hp₂ hlin₄)).trans (by omega)

/-- The finite set of feasible interior stationary parameters.-/
def finiteStationaryRoots (m t : ℕ) (h : ℝ) : Finset ℝ := by
  classical
  exact (finiteStationarityPolynomial m t).roots.toFinset.filter
    (fun z => z ∈ Ioo (0 : ℝ) 1 ∧ branchEntropy m z ≤ h)

/--
@isnad1 id=le.1h3v.s4.ba79ef25f00e from=translated src=- shape=3c2c8155 vocab=71f46910
-/
theorem card_finiteStationaryRoots_le (m t : ℕ) (ht : 1 ≤ t) (h : ℝ) :
    (finiteStationaryRoots m t h).card ≤ t := by
  classical
  exact (Finset.card_filter_le _ _).trans ((Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' _).trans (natDegree_finiteStationarityPolynomial_le m t ht)))

end
end EntropyConstrainedMissingMass

import Tengoku.Rankamplificationtotient.RankAmplification.SmoothNumberBounds
import Tengoku.Rankamplificationtotient.RankAmplification.MertensComparison

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The totient weight in the smooth-predecessor argument Pomerance--Shparlinski's first reduction weights a smooth cofactor `m` by `m / φ(m)`. -/

namespace RankAmplification

open scoped BigOperators Nat.Prime

noncomputable section

/-- The real totient weight used in the smooth-predecessor prime argument.-/
def totientWeight (m : ℕ) : ℝ :=
  (m : ℝ) / (m.totient : ℝ)

/-- The finite Euler product representation of the totient weight.-/
def totientEulerWeight (m : ℕ) : ℝ :=
  ∏ p ∈ m.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹

/--
@isnad1 id=eq.0h1v.s5.71cc91fdd4e1 from=translated src=- shape=f01920cd vocab=f7b65907
-/
theorem totient_cast_eq_mul_prod_factors_real (m : ℕ) :
    (m.totient : ℝ) =
      (m : ℝ) * ∏ p ∈ m.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (Rat.castHom ℝ) (Nat.totient_eq_mul_prod_factors m)
  simpa using h

/--
@isnad1 id=lt.1h1v.s5.1f82ace69611 from=translated src=- shape=12f0010c vocab=8fde40d2
-/
theorem primeEulerFactor_pos {p : ℕ} (hp : p.Prime) :
    0 < (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact inv_pos.mpr (sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1))

/--
@isnad1 id=le.1h1v.s5.4e0467d4fa7b from=translated src=- shape=12f0010c vocab=929ff588
-/
theorem one_le_primeEulerFactor {p : ℕ} (hp : p.Prime) :
    1 ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hden : 0 < 1 - (p : ℝ)⁻¹ :=
    sub_pos.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt))
  exact (one_le_inv₀ hden).2 (by linarith [inv_nonneg.mpr hp0.le])

/--
@isnad1 id=eq.1h1v.s4.f76dbe32c26b from=translated src=- shape=5313247f vocab=f7895a40
-/
theorem totientWeight_eq_eulerWeight {m : ℕ} (hm : m ≠ 0) :
    totientWeight m = totientEulerWeight m := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hprodPos : 0 < ∏ p ∈ m.primeFactors, (1 - (p : ℝ)⁻¹) := by
    apply Finset.prod_pos
    intro p hp
    have pp := Nat.prime_of_mem_primeFactors hp
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast pp.one_lt))
  rw [totientWeight, totientEulerWeight, totient_cast_eq_mul_prod_factors_real,
    div_eq_mul_inv, mul_inv_rev]
  calc
    (m : ℝ) * ((∏ p ∈ m.primeFactors, (1 - (p : ℝ)⁻¹))⁻¹ * (m : ℝ)⁻¹) =
        (∏ p ∈ m.primeFactors, (1 - (p : ℝ)⁻¹))⁻¹ * ((m : ℝ) * (m : ℝ)⁻¹) := by
      ring
    _ = (∏ p ∈ m.primeFactors, (1 - (p : ℝ)⁻¹))⁻¹ := by
      rw [mul_inv_cancel₀ hmR, mul_one]
    _ = ∏ p ∈ m.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
      rw [Finset.prod_inv_distrib]

/-- Smoothness places the Euler support inside the Mertens product.
@isnad1 id=le.1h2v.s3.07aa5ac370fb from=translated src=- shape=0069f895 vocab=f462835b
-/
theorem totientEulerWeight_le_mertensProduct {R m : ℕ} (hm : IsSmooth R m) :
    totientEulerWeight m ≤ mertensProduct R := by
  unfold totientEulerWeight mertensProduct
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    exact Nat.mem_primesLE.mpr
      ⟨hm.2 p hp, Nat.prime_of_mem_primeFactors hp⟩
  · intro p hp
    exact (primeEulerFactor_pos (Nat.prime_of_mem_primeFactors hp)).le
  · intro p hp _
    exact one_le_primeEulerFactor (Nat.prime_of_mem_primesLE hp)

/--
@isnad1 id=le.1h2v.s3.0edf4d6663ec from=translated src=- shape=0069f895 vocab=ebbb4892
-/
theorem totientWeight_le_mertensProduct {R m : ℕ} (hm : IsSmooth R m) :
    totientWeight m ≤ mertensProduct R := by
  rw [totientWeight_eq_eulerWeight hm.1]
  exact totientEulerWeight_le_mertensProduct hm

/-- Finite weighted smooth sum occurring in Pomerance--Shparlinski Lemma 1.-/
def finiteSmoothTotientWeightSum (R X : ℕ) : ℝ :=
  ∑ m ∈ finiteSmoothSet R X, totientWeight m

/--
@isnad1 id=le.0h2v.s4.be7b493d420c from=translated src=- shape=5ffe46ab vocab=3337a4bf
-/
theorem finiteSmoothTotientWeightSum_nonneg (R X : ℕ) :
    0 ≤ finiteSmoothTotientWeightSum R X := by
  unfold finiteSmoothTotientWeightSum totientWeight
  positivity

/-- The exact finite upper bound needed before inserting a smooth-number estimate.
@isnad1 id=le.0h2v.s4.40fa12e5dda5 from=translated src=- shape=ddfef398 vocab=a7545717
-/
theorem finiteSmoothTotientWeightSum_le (R X : ℕ) :
    finiteSmoothTotientWeightSum R X ≤
      mertensProduct R * finiteSmoothCount R X := by
  rw [finiteSmoothTotientWeightSum, finiteSmoothCount]
  calc
    ∑ m ∈ finiteSmoothSet R X, totientWeight m ≤
        ∑ _m ∈ finiteSmoothSet R X, mertensProduct R := by
      apply Finset.sum_le_sum
      intro m hm
      exact totientWeight_le_mertensProduct (mem_finiteSmoothSet.mp hm).2.2
    _ = mertensProduct R * (finiteSmoothSet R X).card := by
      simp [mul_comm]

/-- An explicit `O(log R)` form using the unconditional Mertens comparison.
@isnad1 id=le.1h2v.s6.3745170fda2c from=translated src=- shape=ac74b4e0 vocab=a0f5e4da
-/
theorem finiteSmoothTotientWeightSum_le_log {R X : ℕ} (hR : 3 ≤ R) :
    finiteSmoothTotientWeightSum R X ≤
      (Real.exp (4 * Real.log 4) * (1 + Real.log R)) * finiteSmoothCount R X := by
  calc
    finiteSmoothTotientWeightSum R X ≤
        mertensProduct R * finiteSmoothCount R X := finiteSmoothTotientWeightSum_le R X
    _ ≤ (Real.exp (4 * Real.log 4) * (1 + Real.log R)) * finiteSmoothCount R X := by
      gcongr
      exact mertensProduct_le_log R hR

/-- Full-range Rankin specialization for the weighted smooth sum.
@isnad1 id=le.4h2v.s7.8d0a219007ff from=translated src=- shape=bae65bc5 vocab=b9f47f87
-/
theorem finiteSmoothTotientWeightSum_le_full_paper_error {R X : ℕ}
    (hX : 0 < X) (hR : 3 ≤ R) (hu : 1 < rankinU X R)
    (huSqrt : rankinU X R ≤ Real.sqrt R) :
    finiteSmoothTotientWeightSum R X ≤
      (Real.exp (4 * Real.log 4) * (1 + Real.log R)) *
        ((X : ℝ) * Real.exp
          (-rankinU X R * Real.log (rankinU X R) + fullPaperDivisorError R X)) := by
  calc
    finiteSmoothTotientWeightSum R X ≤
        (Real.exp (4 * Real.log 4) * (1 + Real.log R)) * finiteSmoothCount R X :=
      finiteSmoothTotientWeightSum_le_log hR
    _ ≤ (Real.exp (4 * Real.log 4) * (1 + Real.log R)) *
        ((X : ℝ) * Real.exp
          (-rankinU X R * Real.log (rankinU X R) + fullPaperDivisorError R X)) := by
      apply mul_le_mul_of_nonneg_left
        (finiteSmoothCount_le_full_paper_error hX (hR.trans' (by norm_num)) hu huSqrt)
      exact mul_nonneg (Real.exp_pos _).le
        (add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast (show 1 ≤ R by omega))))

end

end RankAmplification

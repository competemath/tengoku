import Tengoku.FormalizeTubalDemystPaper.TubalTensor.Prerequisites.Norms
import Tengoku.Seed.Analysis.InnerProductSpace.PiL2
import Tengoku.Seed.Analysis.InnerProductSpace.Orthonormal
import Tengoku.Seed.Analysis.RCLike.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/Prerequisites/EckartYoung.lean
  Classical matrix Eckart-Young theorem (proved).

  The classical matrix Eckart-Young theorem is proved from three main ingredients:
  1. Unitary invariance of the Frobenius norm (frobNormSq_unitary_mul_left/right)
  2. Reduction to diagonal case via the SVD factorization
  3. The diagonal Eckart-Young inequality (frob_ge_tail_diag)
-/

namespace TubalTensor

open Matrix Complex BigOperators
open scoped ComplexOrder

/-! ## Eckart-Young reduction lemmas -/

/-- rank(Uᴴ * B * V) ≤ k when rank(B) ≤ k and U, V are unitary.-/
theorem rank_conj_le {m p : ℕ}
    (U : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin p) (Fin p) ℂ)
    (hU : IsUnitary U) (hV : IsUnitary V)
    (B : Matrix (Fin m) (Fin p) ℂ) (k : ℕ) (hB : B.rank ≤ k) :
    (Uᴴ * B * V).rank ≤ k := by
  have hUHdet : IsUnit Uᴴ.det := by
    rw [det_conjTranspose]
    exact (isUnit_det_of_left_inverse hU.conjTranspose_mul_self).star
  have hVdet : IsUnit V.det :=
    isUnit_det_of_left_inverse hV.conjTranspose_mul_self
  calc (Uᴴ * B * V).rank
      = (Uᴴ * (B * V)).rank := by rw [Matrix.mul_assoc]
    _ = (B * V).rank := rank_mul_eq_right_of_isUnit_det _ _ hUHdet
    _ = B.rank := rank_mul_eq_left_of_isUnit_det _ _ hVdet
    _ ≤ k := hB

/-! ## Core diagonal Eckart-Young inequality -/

/-- The squared Frobenius norm of a difference with a truncated SVD-diagonal matrix
    equals the sum of squared tail singular values.-/
theorem frobNormSq_svdDiag_sub_trunc {m p : ℕ} {S : Matrix (Fin m) (Fin p) ℝ}
    (hS : IsSVDDiag S) (k : ℕ) :
    frobNormSq (toComplexMatrix S - toComplexMatrix (svdTrunc S hS k)) =
    ∑ i : Fin m, ∑ j : Fin p,
      if ¬((i : ℕ) < k) ∧ (i : ℕ) = (j : ℕ) then Complex.normSq (↑(S i j)) else 0 := by
  simp only [frobNormSq]
  congr 1; funext i; congr 1; funext j
  simp only [Matrix.sub_apply, toComplexMatrix, Matrix.map_apply, svdTrunc]
  -- The svdTrunc condition is: (i : ℕ) < k ∧ (i : ℕ) = (j : ℕ)
  -- The target condition is: ¬((i : ℕ) < k) ∧ (i : ℕ) = (j : ℕ)
  by_cases hik : (i : ℕ) < k
  · by_cases hij : (i : ℕ) = (j : ℕ)
    · -- i < k and i = j: svdTrunc keeps the value, so difference is 0
      rw [ite_eq_left ⟨hik, hij⟩, ite_eq_right (by push Not; exact fun h => absurd hik (not_lt.mpr h))]
      simp [sub_self]
    · -- i < k and i ≠ j: svdTrunc is 0, S is 0 (off-diagonal)
      rw [ite_eq_right (not_and_of_not_right _ hij), ite_eq_right (not_and_of_not_right _ hij)]
      simp [hS.1 i j hij]
  · by_cases hij : (i : ℕ) = (j : ℕ)
    · -- i ≥ k and i = j: svdTrunc is 0, S i j = σᵢ
      rw [ite_eq_right (not_and_of_not_left _ hik), ite_eq_left ⟨hik, hij⟩]
      simp
    · -- i ≥ k and i ≠ j: both are 0
      rw [ite_eq_right (not_and_of_not_left _ hik), ite_eq_right (not_and_of_not_right _ hij)]
      simp [hS.1 i j hij]

/-- Weighted sum inequality: if a is non-increasing and nonneg, w ∈ [0,1], ∑w ≤ k,
    then ∑ a_i w_i ≤ ∑_{i<k} a_i.

    Proof: Write ∑ a_i w_i = ∑_{i<k} a_i w_i + ∑_{i≥k} a_i w_i.
    The first sum ≤ ∑_{i<k} a_i (since w_i ≤ 1).
    The second sum: for i ≥ k, a_i ≤ a_{k'} for any k' < k (non-increasing).
    So ∑_{i≥k} a_i w_i ≤ a_{k'} · ∑_{i≥k} w_i for a suitable k'.
    And ∑_{i≥k} w_i = ∑ w_i - ∑_{i<k} w_i ≤ k - ∑_{i<k} w_i.
    Combining: ∑ a_i w_i ≤ ∑_{i<k} a_i w_i + a_{k'} · (k - ∑_{i<k} w_i).
    The difference from ∑_{i<k} a_i is bounded using a_i ≥ a_{k'} for i < k.-/
theorem weighted_sum_le_head {n : ℕ} (a w : Fin n → ℝ) (k : ℕ)
    (ha_nonneg : ∀ i, 0 ≤ a i)
    (ha_mono : ∀ i j : Fin n, i ≤ j → a j ≤ a i)
    (hw_range : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (hw_sum : ∑ i, w i ≤ k) :
    ∑ i, a i * w i ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), a i := by
  -- Each term a_i * w_i ≤ a_i since w_i ≤ 1 and a_i ≥ 0
  -- For k ≥ n: RHS = ∑ a_i, and ∑ a_i w_i ≤ ∑ a_i since w_i ≤ 1
  by_cases hkn : n ≤ k
  · have : Finset.univ.filter (fun i : Fin n => (i : ℕ) < k) = Finset.univ := by
      ext i; simp; omega
    rw [this]
    exact Finset.sum_le_sum fun i _ => by nlinarith [(hw_range i).2, ha_nonneg i]
  · push Not at hkn
    -- Write ∑ a_i w_i = ∑ a_i - ∑ a_i (1-w_i)
    -- and ∑_{i<k} a_i = ∑ a_i - ∑_{i≥k} a_i
    -- So we need ∑ a_i (1-w_i) ≥ ∑_{i≥k} a_i
    -- i.e., ∑_{i<k} a_i (1-w_i) + ∑_{i≥k} a_i (1-w_i) ≥ ∑_{i≥k} a_i · 1
    -- i.e., ∑_{i<k} a_i (1-w_i) ≥ ∑_{i≥k} a_i · w_i
    -- Split the sum
    set S_lo := Finset.univ.filter (fun i : Fin n => (i : ℕ) < k)
    set S_hi := Finset.univ.filter (fun i : Fin n => ¬((i : ℕ) < k))
    have hunion : S_lo ∪ S_hi = Finset.univ := by
      ext i; simp [S_lo, S_hi]; omega
    have hdisj : Disjoint S_lo S_hi :=
      Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
    -- Split the total sum
    have hsplit : ∑ i, a i * w i = ∑ i ∈ S_lo, a i * w i + ∑ i ∈ S_hi, a i * w i := by
      rw [← Finset.sum_union hdisj, hunion]
    -- It suffices to show ∑_{i≥k} a_i w_i ≤ ∑_{i<k} a_i (1-w_i)
    -- because then ∑ a_i w_i = ∑_{lo} a_i w_i + ∑_{hi} a_i w_i
    --                         ≤ ∑_{lo} a_i w_i + ∑_{lo} a_i (1-w_i) = ∑_{lo} a_i
    suffices hsuff : ∑ i ∈ S_hi, a i * w i ≤ ∑ i ∈ S_lo, a i * (1 - w i) by
      rw [hsplit]
      have key : ∑ i ∈ S_lo, a i * w i + ∑ i ∈ S_lo, a i * (1 - w i) = ∑ i ∈ S_lo, a i := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      linarith
    -- Prove ∑_{i≥k} a_i w_i ≤ ∑_{i<k} a_i (1-w_i)
    -- Use pivot value ak = a(k)
    set ak := a ⟨k, hkn⟩
    -- For j ∈ S_hi (j ≥ k): a j ≤ ak since j ≥ k and a non-increasing
    have hhi : ∀ j ∈ S_hi, a j ≤ ak := by
      intro j hj; simp [S_hi] at hj
      exact ha_mono ⟨k, hkn⟩ j (Fin.mk_le_mk.mpr (Nat.le_of_lt_succ (Nat.lt_succ_of_le hj)))
    -- For i ∈ S_lo (i < k): ak ≤ a i since i ≤ k and a non-increasing
    have hlo : ∀ i ∈ S_lo, ak ≤ a i := by
      intro i hi; simp [S_lo] at hi
      exact ha_mono i ⟨k, hkn⟩ (Fin.mk_le_mk.mpr (Nat.le_of_lt hi))
    -- ∑_{hi} a_i w_i ≤ ak · ∑_{hi} w_i
    have h1 : ∑ j ∈ S_hi, a j * w j ≤ ak * ∑ j ∈ S_hi, w j := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j hj => by nlinarith [hhi j hj, (hw_range j).1]
    -- ak · ∑_{lo} (1-w_i) ≤ ∑_{lo} a_i (1-w_i)
    have h2 : ak * ∑ i ∈ S_lo, (1 - w i) ≤ ∑ i ∈ S_lo, a i * (1 - w i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i hi => by nlinarith [hlo i hi, (hw_range i).2]
    -- ∑_{hi} w_i ≤ ∑_{lo} (1-w_i)
    -- This follows from: ∑ w_i ≤ k and |S_lo| = k
    have hcard : (S_lo.card : ℝ) = k := by
      suffices h : S_lo.card = k by exact_mod_cast h
      change (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k)).card = k
      rw [show (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k)) =
        Finset.Iio (⟨k, hkn⟩ : Fin n) from by ext; simp [Fin.lt_def]]
      exact Fin.card_Iio _
    have h3 : ∑ j ∈ S_hi, w j ≤ ∑ i ∈ S_lo, (1 - w i) := by
      -- ∑_{lo} (1-w_i) = |S_lo| - ∑_{lo} w_i = k - ∑_{lo} w_i
      have heq : ∑ i ∈ S_lo, (1 - w i) = ↑S_lo.card - ∑ i ∈ S_lo, w i := by
        rw [Finset.sum_sub_distrib]; simp [Finset.sum_const, nsmul_eq_mul]
      -- ∑_{hi} w_i = ∑ w_i - ∑_{lo} w_i ≤ k - ∑_{lo} w_i
      have htotal : ∑ i ∈ S_lo, w i + ∑ i ∈ S_hi, w i = ∑ i, w i := by
        rw [← Finset.sum_union hdisj, hunion]
      linarith [hcard]
    -- Combine using ak ≥ 0
    have hak : 0 ≤ ak := ha_nonneg _
    linarith [mul_le_mul_of_nonneg_left h3 hak]

/-! ### Bessel's inequality for row vectors -/

/-! ## Classical matrix Eckart-Young theorem -/

end TubalTensor

import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
import Tengoku.Seed.Data.Nat.Choose.Sum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Volume polynomials for ranked path-token covers

This file isolates the exact finite summation identity used in the general volume lower bound.
The geometric lattice-ball count is proved separately.
-/

open scoped BigOperators

namespace BurningPath

/-- The Delannoy polynomial that counts an ambient integer `ℓ₁` ball.-/
def latticeBallPolynomial (k r : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1), 2 ^ j * k.choose j * r.choose j

/-- The sum of the ambient ball bounds at radii `0, ..., t - 1`.-/
def cumulativeLatticeBallPolynomial (k t : ℕ) : ℕ :=
  ∑ r ∈ Finset.range t, latticeBallPolynomial k r

/-- The closed form occurring on the right side of the exact general lower bound.-/
def rankedVolumePolynomial (k t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1), 2 ^ j * k.choose j * t.choose (j + 1)

/-- Hockey-stick identity in precisely the indexing used by ranked covers.-/
theorem sum_range_choose (t j : ℕ) :
    ∑ r ∈ Finset.range t, r.choose j = t.choose (j + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ, ih]
      simpa [add_comm] using (Nat.choose_succ_succ' t j).symm

/-- Summing the exact ambient ball polynomials gives the ranked volume polynomial.-/
theorem cumulativeLatticeBallPolynomial_eq (k t : ℕ) :
    cumulativeLatticeBallPolynomial k t = rankedVolumePolynomial k t := by
  simp only [cumulativeLatticeBallPolynomial, latticeBallPolynomial, rankedVolumePolynomial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum, sum_range_choose]

/-- The two-dimensional ranked volume polynomial has the cubic closed form before division.-/
theorem three_mul_rankedVolumePolynomial_two (t : ℕ) :
    3 * rankedVolumePolynomial 2 t = t * (2 * t ^ 2 + 1) := by
  induction t with
  | zero => simp [rankedVolumePolynomial]
  | succ t ih =>
      simp only [rankedVolumePolynomial, Finset.sum_range_succ, Nat.reduceAdd,
        Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self, Nat.choose_succ_succ',
        pow_zero, pow_one, one_mul, Nat.reducePow, Finset.sum_range_zero,
        Finset.sum_range_succ] at ih ⊢
      cases t with
      | zero => norm_num at ih ⊢
      | succ t =>
          have hchoose := Nat.choose_succ_right_eq (t + 1) 1
          simp only [Nat.choose_one_right, Nat.add_sub_cancel] at hchoose
          nlinarith

/-- The exact expression used in the required two-token lower bound.-/
theorem rankedVolumePolynomial_two (t : ℕ) :
    rankedVolumePolynomial 2 t = t * (2 * t ^ 2 + 1) / 3 := by
  refine (Nat.div_eq_of_eq_mul_left (by norm_num : 0 < 3) ?_).symm
  simpa [mul_comm] using (three_mul_rankedVolumePolynomial_two t).symm

/-- The `j = 0` summand shows that the ranked volume polynomial is at least its length.-/
theorem le_rankedVolumePolynomial (k t : ℕ) :
    t ≤ rankedVolumePolynomial k t := by
  have hzero : 0 ∈ Finset.range (k + 1) := by simp
  calc
    t = 2 ^ 0 * k.choose 0 * t.choose (0 + 1) := by simp
    _ ≤ rankedVolumePolynomial k t := by
      unfold rankedVolumePolynomial
      exact Finset.single_le_sum
        (f := fun j ↦ 2 ^ j * k.choose j * t.choose (j + 1))
        (fun _ _ ↦ Nat.zero_le _) hzero

/-- The predicate whose least witness is the exact volume threshold.-/
def IsVolumeThresholdLength (k N t : ℕ) : Prop :=
  1 ≤ t ∧ N ≤ rankedVolumePolynomial k t

theorem exists_isVolumeThresholdLength (k N : ℕ) :
    ∃ t, IsVolumeThresholdLength k N t := by
  refine ⟨N + 1, Nat.succ_le_succ (Nat.zero_le N), ?_⟩
  exact (Nat.le_succ N).trans (le_rankedVolumePolynomial k (N + 1))

/-- The exact minimum appearing in the general volume lower bound.-/
noncomputable def volumeThreshold (k N : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_isVolumeThresholdLength k N)

theorem volumeThreshold_spec (k N : ℕ) :
    IsVolumeThresholdLength k N (volumeThreshold k N) := by
  classical
  exact Nat.find_spec (exists_isVolumeThresholdLength k N)

theorem volumeThreshold_min {k N t : ℕ} (h : IsVolumeThresholdLength k N t) :
    volumeThreshold k N ≤ t := by
  classical
  exact Nat.find_min' (exists_isVolumeThresholdLength k N) h

/-- In dimension two, the threshold predicate is the required cubic inequality.-/
theorem isVolumeThresholdLength_two_iff (N t : ℕ) :
    IsVolumeThresholdLength 2 N t ↔
      1 ≤ t ∧ N ≤ t * (2 * t ^ 2 + 1) / 3 := by
  simp only [IsVolumeThresholdLength, rankedVolumePolynomial_two]

/-- The exact cubic threshold in the required intermediate two-token proposition.-/
noncomputable def twoTokenCubicThreshold (N : ℕ) : ℕ :=
  volumeThreshold 2 N

theorem twoTokenCubicThreshold_spec (N : ℕ) :
    1 ≤ twoTokenCubicThreshold N ∧
      N ≤ twoTokenCubicThreshold N *
        (2 * twoTokenCubicThreshold N ^ 2 + 1) / 3 := by
  exact (isVolumeThresholdLength_two_iff N (volumeThreshold 2 N)).mp
    (volumeThreshold_spec 2 N)

theorem twoTokenCubicThreshold_min {N t : ℕ}
    (h : 1 ≤ t ∧ N ≤ t * (2 * t ^ 2 + 1) / 3) :
    twoTokenCubicThreshold N ≤ t := by
  exact volumeThreshold_min ((isVolumeThresholdLength_two_iff N t).mpr h)

end BurningPath

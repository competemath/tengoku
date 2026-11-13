import Tengoku.Rankamplificationtotient.RankAmplification.Definitions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Finite counting API Membership and elementary support lemmas for the exact finite sets used in the paper. -/

namespace RankAmplification

@[simp]
theorem mem_shiftedEqualTotientSet {x h n : ℕ} :
    n ∈ shiftedEqualTotientSet x h ↔
      1 ≤ n ∧ n ≤ x ∧ n.totient = (n + h).totient := by
  simp [shiftedEqualTotientSet, and_assoc]

@[simp]
theorem mem_smoothTotientSet {X Y m : ℕ} :
    m ∈ smoothTotientSet X Y ↔ 1 ≤ m ∧ m ≤ X ∧ IsSmooth Y m.totient := by
  classical
  simp [smoothTotientSet, and_assoc]

@[simp]
theorem mem_nonsmoothShiftedSet {x h y n : ℕ} :
    n ∈ nonsmoothShiftedSet x h y ↔
      1 ≤ n ∧ n ≤ x ∧ n.totient = (n + h).totient ∧
        y < largestPrimeFactor n.totient := by
  simp [nonsmoothShiftedSet, and_assoc]

@[simp]
theorem mem_aboveCutoffDiagonalSet {x h Y n : ℕ} :
    n ∈ aboveCutoffDiagonalSet x h Y ↔
      1 ≤ n ∧ n ≤ x ∧ IsAboveCutoffDiagonal h Y n := by
  classical
  simp [aboveCutoffDiagonalSet, and_assoc]

@[simp]
theorem radical_zero : radical 0 = 1 := by
  simp [radical, primeSupport]

@[simp]
theorem radical_one : radical 1 = 1 := by
  simp [radical, primeSupport]

theorem primeSupport_radical (n : ℕ) : primeSupport (radical n) = primeSupport n := by
  simpa [radical, primeSupport] using Nat.primeFactors_prod_primeFactors n

theorem radical_eq_radical_iff {m n : ℕ} :
    radical m = radical n ↔ primeSupport m = primeSupport n := by
  constructor
  · intro h
    simpa only [primeSupport_radical] using congrArg primeSupport h
  · intro h
    simp only [radical, h]

theorem one_le_largestPrimeFactor (n : ℕ) : 1 ≤ largestPrimeFactor n :=
  le_max_left 1 ((primeSupport n).sup id)

theorem IsSmooth.largestPrimeFactor_le {y n : ℕ} (hy : 1 ≤ y) (hn : IsSmooth y n) :
    largestPrimeFactor n ≤ y := by
  rw [largestPrimeFactor, max_le_iff]
  exact ⟨hy, Finset.sup_le fun p hp ↦ hn.2 p hp⟩

theorem isSmooth_iff_largestPrimeFactor_le {y n : ℕ} (hy : 1 ≤ y) (hn : n ≠ 0) :
    IsSmooth y n ↔ largestPrimeFactor n ≤ y := by
  constructor
  · exact fun h ↦ h.largestPrimeFactor_le hy
  · intro h
    refine ⟨hn, fun p hp ↦ ?_⟩
    exact (Finset.le_sup hp).trans (le_max_right 1 ((primeSupport n).sup id) |>.trans h)

@[simp]
theorem isSmooth_one (y : ℕ) : IsSmooth y 1 := by
  simp [IsSmooth, primeSupport]

@[simp]
theorem largePrimeRank_zero (y : ℕ) : largePrimeRank y 0 = 0 := by
  simp [largePrimeRank, primeSupport]

@[simp]
theorem largePrimeRank_one (y : ℕ) : largePrimeRank y 1 = 0 := by
  simp [largePrimeRank, primeSupport]

theorem nonsmoothShiftedSet_subset (x h y : ℕ) :
    nonsmoothShiftedSet x h y ⊆ shiftedEqualTotientSet x h := by
  intro n hn
  exact Finset.mem_of_mem_filter n hn

theorem aboveCutoffDiagonalSet_subset_Icc (x h Y : ℕ) :
    aboveCutoffDiagonalSet x h Y ⊆ Finset.Icc 1 x := by
  classical
  intro n hn
  exact Finset.mem_of_mem_filter n hn

end RankAmplification

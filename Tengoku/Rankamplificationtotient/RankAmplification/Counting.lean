import Tengoku.Rankamplificationtotient.RankAmplification.Definitions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Finite counting API Membership and elementary support lemmas for the exact finite sets used in the paper. -/

namespace RankAmplification

/--
@isnad1 id=iff.0h3v.s5.c102db9e0e39 from=translated src=- shape=55ee6539 vocab=fa46fc8b
-/
@[simp]
theorem mem_shiftedEqualTotientSet {x h n : ℕ} :
    n ∈ shiftedEqualTotientSet x h ↔
      1 ≤ n ∧ n ≤ x ∧ n.totient = (n + h).totient := by
  simp [shiftedEqualTotientSet, and_assoc]

/--
@isnad1 id=iff.0h3v.s5.b3feba1eec52 from=translated src=- shape=fc50b65a vocab=52e5a142
-/
@[simp]
theorem mem_smoothTotientSet {X Y m : ℕ} :
    m ∈ smoothTotientSet X Y ↔ 1 ≤ m ∧ m ≤ X ∧ IsSmooth Y m.totient := by
  classical
  simp [smoothTotientSet, and_assoc]

/--
@isnad1 id=iff.0h4v.s5.cb577a25946b from=translated src=- shape=864cdce3 vocab=a452f1cc
-/
@[simp]
theorem mem_nonsmoothShiftedSet {x h y n : ℕ} :
    n ∈ nonsmoothShiftedSet x h y ↔
      1 ≤ n ∧ n ≤ x ∧ n.totient = (n + h).totient ∧
        y < largestPrimeFactor n.totient := by
  simp [nonsmoothShiftedSet, and_assoc]

/--
@isnad1 id=iff.0h4v.s5.f9e37e2b9378 from=translated src=- shape=dede7a53 vocab=6da10863
-/
@[simp]
theorem mem_aboveCutoffDiagonalSet {x h Y n : ℕ} :
    n ∈ aboveCutoffDiagonalSet x h Y ↔
      1 ≤ n ∧ n ≤ x ∧ IsAboveCutoffDiagonal h Y n := by
  classical
  simp [aboveCutoffDiagonalSet, and_assoc]

/--
@isnad1 id=eq.0h0v.s3.17f91ae3d3d2 from=translated src=- shape=3c26ae4f vocab=e86c8a4b
-/
@[simp]
theorem radical_zero : radical 0 = 1 := by
  simp [radical, primeSupport]

/--
@isnad1 id=eq.0h0v.s3.e9af0612b2c5 from=translated src=- shape=3c26ae4f vocab=e86c8a4b
-/
@[simp]
theorem radical_one : radical 1 = 1 := by
  simp [radical, primeSupport]

/--
@isnad1 id=eq.0h1v.s3.95578c905617 from=translated src=- shape=c45f922a vocab=0ee7bf66
-/
theorem primeSupport_radical (n : ℕ) : primeSupport (radical n) = primeSupport n := by
  simpa [radical, primeSupport] using Nat.primeFactors_prod_primeFactors n

/--
@isnad1 id=iff.0h2v.s4.7495a648be37 from=translated src=- shape=16b1afe9 vocab=0ee7bf66
-/
theorem radical_eq_radical_iff {m n : ℕ} :
    radical m = radical n ↔ primeSupport m = primeSupport n := by
  constructor
  · intro h
    simpa only [primeSupport_radical] using congrArg primeSupport h
  · intro h
    simp only [radical, h]

/--
@isnad1 id=le.0h1v.s3.2e685e9e66f6 from=translated src=- shape=8a62b088 vocab=21271302
-/
theorem one_le_largestPrimeFactor (n : ℕ) : 1 ≤ largestPrimeFactor n :=
  le_max_left 1 ((primeSupport n).sup id)

/--
@isnad1 id=le.2h2v.s4.1fe4cf09c530 from=translated src=- shape=632dbebe vocab=e55baa8f
-/
theorem IsSmooth.largestPrimeFactor_le {y n : ℕ} (hy : 1 ≤ y) (hn : IsSmooth y n) :
    largestPrimeFactor n ≤ y := by
  rw [largestPrimeFactor, max_le_iff]
  exact ⟨hy, Finset.sup_le fun p hp ↦ hn.2 p hp⟩

/--
@isnad1 id=iff.2h2v.s5.700f9e3d7dae from=translated src=- shape=f9a86d5c vocab=e55baa8f
-/
theorem isSmooth_iff_largestPrimeFactor_le {y n : ℕ} (hy : 1 ≤ y) (hn : n ≠ 0) :
    IsSmooth y n ↔ largestPrimeFactor n ≤ y := by
  constructor
  · exact fun h ↦ h.largestPrimeFactor_le hy
  · intro h
    refine ⟨hn, fun p hp ↦ ?_⟩
    exact (Finset.le_sup hp).trans (le_max_right 1 ((primeSupport n).sup id) |>.trans h)

/--
@isnad1 id=issmooth.0h1v.s3.cc106e99a693 from=translated src=- shape=3d52821e vocab=8d708023
-/
@[simp]
theorem isSmooth_one (y : ℕ) : IsSmooth y 1 := by
  simp [IsSmooth, primeSupport]

/--
@isnad1 id=eq.0h1v.s4.e0b92f55eb4b from=translated src=- shape=1d838610 vocab=08825419
-/
@[simp]
theorem largePrimeRank_zero (y : ℕ) : largePrimeRank y 0 = 0 := by
  simp [largePrimeRank, primeSupport]

/--
@isnad1 id=eq.0h1v.s4.e1b4554b1abf from=translated src=- shape=1d838610 vocab=08825419
-/
@[simp]
theorem largePrimeRank_one (y : ℕ) : largePrimeRank y 1 = 0 := by
  simp [largePrimeRank, primeSupport]

/--
@isnad1 id=le.0h3v.s4.3a6e6bfb3f4d from=translated src=- shape=202d3bc8 vocab=a1fb9173
-/
theorem nonsmoothShiftedSet_subset (x h y : ℕ) :
    nonsmoothShiftedSet x h y ⊆ shiftedEqualTotientSet x h := by
  intro n hn
  exact Finset.mem_of_mem_filter n hn

/--
@isnad1 id=le.0h3v.s4.2ea4653de96b from=translated src=- shape=c9dde482 vocab=f780bf86
-/
theorem aboveCutoffDiagonalSet_subset_Icc (x h Y : ℕ) :
    aboveCutoffDiagonalSet x h Y ⊆ Finset.Icc 1 x := by
  classical
  intro n hn
  exact Finset.mem_of_mem_filter n hn

end RankAmplification

import Tengoku.Rankamplificationtotient.RankAmplification.SmoothTransfer
import Tengoku.Rankamplificationtotient.RankAmplification.Provider

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Exact finite stratification by large-prime rank This file formalizes the set partitions used in Sections 4--8. -/

namespace RankAmplification

/-- Shifted equal-totient solutions whose common totient has exactly large-prime rank `r`.-/
noncomputable def exactRankShiftedSet (x h y r : ℕ) : Finset ℕ := by
  classical
  exact (shiftedEqualTotientSet x h).filter fun n ↦ largePrimeRank y n.totient = r

/-- Cardinality of the exact-rank shifted stratum.-/
noncomputable def exactRankShiftedCount (x h y r : ℕ) : ℕ :=
  (exactRankShiftedSet x h y r).card

/-- Shifted equal-totient solutions whose common totient has large-prime rank at least `R`.-/
noncomputable def atLeastRankShiftedSet (x h y R : ℕ) : Finset ℕ := by
  classical
  exact (shiftedEqualTotientSet x h).filter fun n ↦ R ≤ largePrimeRank y n.totient

/-- Cardinality of the rank-at-least-`R` shifted stratum.-/
noncomputable def atLeastRankShiftedCount (x h y R : ℕ) : ℕ :=
  (atLeastRankShiftedSet x h y R).card

/-- The union of all exact shifted strata of rank strictly below `R`.-/
noncomputable def belowRankShiftedSet (x h y R : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range R).biUnion fun r ↦ exactRankShiftedSet x h y r

/-- The union of exact shifted strata with ranks `1,…,J-1`.-/
noncomputable def intermediateRankShiftedSet (x h y J : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico 1 J).biUnion fun r ↦ exactRankShiftedSet x h y r

@[simp]
theorem mem_exactRankShiftedSet {x h y r n : ℕ} :
    n ∈ exactRankShiftedSet x h y r ↔
      n ∈ shiftedEqualTotientSet x h ∧ largePrimeRank y n.totient = r := by
  classical
  simp [exactRankShiftedSet]

@[simp]
theorem mem_atLeastRankShiftedSet {x h y R n : ℕ} :
    n ∈ atLeastRankShiftedSet x h y R ↔
      n ∈ shiftedEqualTotientSet x h ∧ R ≤ largePrimeRank y n.totient := by
  classical
  simp [atLeastRankShiftedSet]

@[simp]
theorem mem_belowRankShiftedSet {x h y R n : ℕ} :
    n ∈ belowRankShiftedSet x h y R ↔
      n ∈ shiftedEqualTotientSet x h ∧ largePrimeRank y n.totient < R := by
  classical
  constructor
  · intro hn
    obtain ⟨r, hr, hnr⟩ := Finset.mem_biUnion.mp hn
    have hrlt : r < R := Finset.mem_range.mp hr
    have hnData := mem_exactRankShiftedSet.mp hnr
    exact ⟨hnData.1, hnData.2.symm ▸ hrlt⟩
  · rintro ⟨hn, hrank⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨largePrimeRank y n.totient, Finset.mem_range.mpr hrank,
      mem_exactRankShiftedSet.mpr ⟨hn, rfl⟩⟩

@[simp]
theorem mem_intermediateRankShiftedSet {x h y J n : ℕ} :
    n ∈ intermediateRankShiftedSet x h y J ↔
      n ∈ shiftedEqualTotientSet x h ∧
        1 ≤ largePrimeRank y n.totient ∧ largePrimeRank y n.totient < J := by
  classical
  constructor
  · intro hn
    obtain ⟨r, hr, hnr⟩ := Finset.mem_biUnion.mp hn
    have hrData := Finset.mem_Ico.mp hr
    have hnData := mem_exactRankShiftedSet.mp hnr
    refine ⟨hnData.1, ?_, ?_⟩
    · simpa only [hnData.2] using hrData.1
    · simpa only [hnData.2] using hrData.2
  · rintro ⟨hn, hrankOne, hrankJ⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨largePrimeRank y n.totient, Finset.mem_Ico.mpr ⟨hrankOne, hrankJ⟩,
      mem_exactRankShiftedSet.mpr ⟨hn, rfl⟩⟩

/-- Every exact-rank stratum is part of the shifted solution set.-/
theorem exactRankShiftedSet_subset_shiftedEqualTotientSet (x h y r : ℕ) :
    exactRankShiftedSet x h y r ⊆ shiftedEqualTotientSet x h := by
  intro n hn
  exact (mem_exactRankShiftedSet.mp hn).1

/-- Every at-least-rank stratum is part of the shifted solution set.-/
theorem atLeastRankShiftedSet_subset_shiftedEqualTotientSet (x h y R : ℕ) :
    atLeastRankShiftedSet x h y R ⊆ shiftedEqualTotientSet x h := by
  intro n hn
  exact (mem_atLeastRankShiftedSet.mp hn).1

/-- Increasing the prime cutoff can only decrease the large-prime rank.-/
theorem largePrimeRank_anti_cutoff {y Y n : ℕ} (hyY : y ≤ Y) :
    largePrimeRank Y n ≤ largePrimeRank y n := by
  rw [largePrimeRank, largePrimeRank]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hpData := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpData.1, hyY.trans_lt hpData.2⟩
  · intro p _ _
    exact Nat.zero_le _

/-! ## Disjointness and finite partitions -/

/-- Two different exact-rank strata are disjoint.-/
theorem exactRankShiftedSet_disjoint {x h y r s : ℕ} (hrs : r ≠ s) :
    Disjoint (exactRankShiftedSet x h y r) (exactRankShiftedSet x h y s) := by
  rw [Finset.disjoint_left]
  intro n hnr hns
  have hrankR := (mem_exactRankShiftedSet.mp hnr).2
  have hrankS := (mem_exactRankShiftedSet.mp hns).2
  exact hrs (hrankR.symm.trans hrankS)

/-- Any finite collection of exact-rank strata is pairwise disjoint.-/
theorem exactRankShiftedSet_pairwiseDisjoint (x h y : ℕ) (s : Finset ℕ) :
    (s : Set ℕ).PairwiseDisjoint fun r ↦ exactRankShiftedSet x h y r := by
  intro r _ t _ hrt
  exact exactRankShiftedSet_disjoint hrt

/-- The below-`R` and at-least-`R` strata are disjoint.-/
theorem belowRankShiftedSet_disjoint_atLeastRankShiftedSet (x h y R : ℕ) :
    Disjoint (belowRankShiftedSet x h y R) (atLeastRankShiftedSet x h y R) := by
  rw [Finset.disjoint_left]
  intro n hbelow hatLeast
  have hlt := (mem_belowRankShiftedSet.mp hbelow).2
  have hle := (mem_atLeastRankShiftedSet.mp hatLeast).2
  exact (Nat.not_lt_of_ge hle) hlt

/-- Every shifted solution lies either below rank `R` or at rank at least `R`.-/
theorem belowRankShiftedSet_union_atLeastRankShiftedSet (x h y R : ℕ) :
    belowRankShiftedSet x h y R ∪ atLeastRankShiftedSet x h y R =
      shiftedEqualTotientSet x h := by
  ext n
  rw [Finset.mem_union, mem_belowRankShiftedSet, mem_atLeastRankShiftedSet]
  constructor
  · rintro (⟨hn, _⟩ | ⟨hn, _⟩)
    · exact hn
    · exact hn
  · intro hn
    rcases lt_or_ge (largePrimeRank y n.totient) R with hrank | hrank
    · exact Or.inl ⟨hn, hrank⟩
    · exact Or.inr ⟨hn, hrank⟩

/-- Cardinality of a finite union of exact-rank strata is the sum of their cardinalities.-/
theorem belowRankShiftedSet_card_eq_sum (x h y R : ℕ) :
    (belowRankShiftedSet x h y R).card =
      ∑ r ∈ Finset.range R, exactRankShiftedCount x h y r := by
  rw [belowRankShiftedSet,
    Finset.card_biUnion (exactRankShiftedSet_pairwiseDisjoint x h y (Finset.range R))]
  rfl

/-- Exact finite count partition at an arbitrary rank threshold.-/
theorem shiftedEqualTotientCount_eq_sum_exactRank_add_atLeastRank (x h y R : ℕ) :
    shiftedEqualTotientCount x h =
      (∑ r ∈ Finset.range R, exactRankShiftedCount x h y r) +
        atLeastRankShiftedCount x h y R := by
  rw [shiftedEqualTotientCount, ← belowRankShiftedSet_union_atLeastRankShiftedSet x h y R,
    Finset.card_union_of_disjoint
      (belowRankShiftedSet_disjoint_atLeastRankShiftedSet x h y R),
    belowRankShiftedSet_card_eq_sum, atLeastRankShiftedCount]

/-- Rank at least zero imposes no restriction.-/
theorem atLeastRankShiftedSet_zero (x h y : ℕ) :
    atLeastRankShiftedSet x h y 0 = shiftedEqualTotientSet x h := by
  ext n
  simp

/-- Count form of the rank-at-least-zero identity.-/
theorem atLeastRankShiftedCount_zero (x h y : ℕ) :
    atLeastRankShiftedCount x h y 0 = shiftedEqualTotientCount x h := by
  rw [atLeastRankShiftedCount, atLeastRankShiftedSet_zero, shiftedEqualTotientCount]

/-! ## Monotonicity -/

/-- Exact-rank strata are monotone in the ambient size cutoff.-/
theorem exactRankShiftedSet_mono_size {W X h y r : ℕ} (hWX : W ≤ X) :
    exactRankShiftedSet W h y r ⊆ exactRankShiftedSet X h y r := by
  intro n hn
  have hnData := mem_exactRankShiftedSet.mp hn
  have hbase := mem_shiftedEqualTotientSet.mp hnData.1
  apply mem_exactRankShiftedSet.mpr
  refine ⟨mem_shiftedEqualTotientSet.mpr ⟨hbase.1, hbase.2.1.trans hWX, hbase.2.2⟩, hnData.2⟩

/-- At-least-rank strata are monotone in the ambient size cutoff.-/
theorem atLeastRankShiftedSet_mono_size {W X h y R : ℕ} (hWX : W ≤ X) :
    atLeastRankShiftedSet W h y R ⊆ atLeastRankShiftedSet X h y R := by
  intro n hn
  have hnData := mem_atLeastRankShiftedSet.mp hn
  have hbase := mem_shiftedEqualTotientSet.mp hnData.1
  apply mem_atLeastRankShiftedSet.mpr
  refine ⟨mem_shiftedEqualTotientSet.mpr ⟨hbase.1, hbase.2.1.trans hWX, hbase.2.2⟩, hnData.2⟩

/-- Cardinal monotonicity of exact-rank strata in the size cutoff.-/
theorem exactRankShiftedCount_mono_size {W X h y r : ℕ} (hWX : W ≤ X) :
    exactRankShiftedCount W h y r ≤ exactRankShiftedCount X h y r := by
  exact Finset.card_le_card (exactRankShiftedSet_mono_size hWX)

/-- Cardinal monotonicity of at-least-rank strata in the size cutoff.-/
theorem atLeastRankShiftedCount_mono_size {W X h y R : ℕ} (hWX : W ≤ X) :
    atLeastRankShiftedCount W h y R ≤ atLeastRankShiftedCount X h y R := by
  exact Finset.card_le_card (atLeastRankShiftedSet_mono_size hWX)

/-- Raising the rank threshold shrinks the at-least-rank stratum.-/
theorem atLeastRankShiftedSet_anti_threshold {x h y R S : ℕ} (hRS : R ≤ S) :
    atLeastRankShiftedSet x h y S ⊆ atLeastRankShiftedSet x h y R := by
  intro n hn
  have hnData := mem_atLeastRankShiftedSet.mp hn
  exact mem_atLeastRankShiftedSet.mpr ⟨hnData.1, hRS.trans hnData.2⟩

/-- Cardinal antitonicity in the rank threshold.-/
theorem atLeastRankShiftedCount_anti_threshold {x h y R S : ℕ} (hRS : R ≤ S) :
    atLeastRankShiftedCount x h y S ≤ atLeastRankShiftedCount x h y R := by
  exact Finset.card_le_card (atLeastRankShiftedSet_anti_threshold hRS)

/-- Raising the rank threshold enlarges the below-rank union.-/
theorem belowRankShiftedSet_mono_threshold {x h y R S : ℕ} (hRS : R ≤ S) :
    belowRankShiftedSet x h y R ⊆ belowRankShiftedSet x h y S := by
  intro n hn
  have hnData := mem_belowRankShiftedSet.mp hn
  exact mem_belowRankShiftedSet.mpr ⟨hnData.1, hnData.2.trans_le hRS⟩

/-- Increasing the prime cutoff shrinks every at-least-rank stratum.-/
theorem atLeastRankShiftedSet_anti_cutoff {x h y Y R : ℕ} (hyY : y ≤ Y) :
    atLeastRankShiftedSet x h Y R ⊆ atLeastRankShiftedSet x h y R := by
  intro n hn
  have hnData := mem_atLeastRankShiftedSet.mp hn
  apply mem_atLeastRankShiftedSet.mpr
  exact ⟨hnData.1, hnData.2.trans (largePrimeRank_anti_cutoff hyY)⟩

/-- Cardinal antitonicity of at-least-rank strata in the prime cutoff.-/
theorem atLeastRankShiftedCount_anti_cutoff {x h y Y R : ℕ} (hyY : y ≤ Y) :
    atLeastRankShiftedCount x h Y R ≤ atLeastRankShiftedCount x h y R := by
  exact Finset.card_le_card (atLeastRankShiftedSet_anti_cutoff hyY)

/-- Increasing the prime cutoff enlarges the below-rank union.-/
theorem belowRankShiftedSet_mono_cutoff {x h y Y R : ℕ} (hyY : y ≤ Y) :
    belowRankShiftedSet x h y R ⊆ belowRankShiftedSet x h Y R := by
  intro n hn
  have hnData := mem_belowRankShiftedSet.mp hn
  apply mem_belowRankShiftedSet.mpr
  exact ⟨hnData.1, (largePrimeRank_anti_cutoff hyY).trans_lt hnData.2⟩

/-- An exact rank above a threshold lies in the corresponding at-least-rank stratum.-/
theorem exactRankShiftedSet_subset_atLeastRankShiftedSet {x h y R r : ℕ} (hRr : R ≤ r) :
    exactRankShiftedSet x h y r ⊆ atLeastRankShiftedSet x h y R := by
  intro n hn
  have hnData := mem_exactRankShiftedSet.mp hn
  apply mem_atLeastRankShiftedSet.mpr
  exact ⟨hnData.1, hnData.2 ▸ hRr⟩

/-- Cardinal form of exact-rank containment in an at-least-rank stratum.-/
theorem exactRankShiftedCount_le_atLeastRankShiftedCount {x h y R r : ℕ} (hRr : R ≤ r) :
    exactRankShiftedCount x h y r ≤ atLeastRankShiftedCount x h y R := by
  exact Finset.card_le_card (exactRankShiftedSet_subset_atLeastRankShiftedSet hRr)

/-! ## Rank zero and the nonsmooth branch -/

/-- The exact rank-zero stratum is precisely the smooth shifted branch.-/
theorem exactRankShiftedSet_zero (x h y : ℕ) :
    exactRankShiftedSet x h y 0 = smoothShiftedSet x h y := by
  ext n
  rw [mem_exactRankShiftedSet, mem_smoothShiftedSet_iff_rank_zero]

/-- Count form of the rank-zero/smooth identity.-/
theorem exactRankShiftedCount_zero (x h y : ℕ) :
    exactRankShiftedCount x h y 0 = smoothShiftedCount x h y := by
  rw [exactRankShiftedCount, exactRankShiftedSet_zero, smoothShiftedCount]

/-- The exact rank-zero stratum grows with the prime cutoff.-/
theorem exactRankShiftedSet_zero_mono_cutoff {x h y Y : ℕ} (hyY : y ≤ Y) :
    exactRankShiftedSet x h y 0 ⊆ exactRankShiftedSet x h Y 0 := by
  rw [exactRankShiftedSet_zero, exactRankShiftedSet_zero]
  intro n hn
  have hnData := mem_smoothShiftedSet.mp hn
  exact mem_smoothShiftedSet.mpr
    ⟨hnData.1, hnData.2.1, hnData.2.2.1, hnData.2.2.2.mono hyY⟩

/-- Cardinal monotonicity of the rank-zero stratum in the prime cutoff.-/
theorem exactRankShiftedCount_zero_mono_cutoff {x h y Y : ℕ} (hyY : y ≤ Y) :
    exactRankShiftedCount x h y 0 ≤ exactRankShiftedCount x h Y 0 := by
  exact Finset.card_le_card (exactRankShiftedSet_zero_mono_cutoff hyY)

/-- For `1 ≤ y`, rank at least one is exactly the paper's nonsmooth branch.-/
theorem atLeastRankShiftedSet_one_eq_nonsmoothShiftedSet {x h y : ℕ} (hy : 1 ≤ y) :
    atLeastRankShiftedSet x h y 1 = nonsmoothShiftedSet x h y := by
  ext n
  rw [mem_atLeastRankShiftedSet, mem_nonsmoothShiftedSet]
  constructor
  · rintro ⟨hn, hrank⟩
    have hnData := mem_shiftedEqualTotientSet.mp hn
    refine ⟨hnData.1, hnData.2.1, hnData.2.2, ?_⟩
    have hnpos : 0 < n := zero_lt_one.trans_le hnData.1
    have hnotSmooth : ¬IsSmooth y n.totient := by
      intro hsmooth
      have hzero := (largePrimeRank_totient_eq_zero_iff_isSmooth hnpos).mpr hsmooth
      omega
    have htotient : n.totient ≠ 0 := (Nat.totient_pos.mpr hnpos).ne'
    have hnotle : ¬largestPrimeFactor n.totient ≤ y := by
      intro hle
      exact hnotSmooth ((isSmooth_iff_largestPrimeFactor_le hy htotient).mpr hle)
    exact Nat.lt_of_not_ge hnotle
  · rintro ⟨hn, hnx, heq, hlpf⟩
    have hnpos : 0 < n := zero_lt_one.trans_le hn
    refine ⟨mem_shiftedEqualTotientSet.mpr ⟨hn, hnx, heq⟩, ?_⟩
    have hrankNe : largePrimeRank y n.totient ≠ 0 := by
      intro hrank
      have hsmooth := (largePrimeRank_totient_eq_zero_iff_isSmooth hnpos).mp hrank
      exact (Nat.not_lt_of_ge (hsmooth.largestPrimeFactor_le hy)) hlpf
    omega

/-- Count form of the rank-at-least-one/nonsmooth identity.-/
theorem atLeastRankShiftedCount_one_eq_nonsmoothShiftedCount {x h y : ℕ} (hy : 1 ≤ y) :
    atLeastRankShiftedCount x h y 1 = nonsmoothShiftedCount x h y := by
  rw [atLeastRankShiftedCount, atLeastRankShiftedSet_one_eq_nonsmoothShiftedSet hy,
    nonsmoothShiftedCount]

/-- Every positive exact-rank stratum lies in the nonsmooth branch.-/
theorem exactRankShiftedSet_subset_nonsmoothShiftedSet {x h y r : ℕ}
    (hy : 1 ≤ y) (hr : 1 ≤ r) :
    exactRankShiftedSet x h y r ⊆ nonsmoothShiftedSet x h y := by
  rw [← atLeastRankShiftedSet_one_eq_nonsmoothShiftedSet hy]
  exact exactRankShiftedSet_subset_atLeastRankShiftedSet hr

/-- Cardinal form of positive exact-rank containment in the nonsmooth branch.-/
theorem exactRankShiftedCount_le_nonsmoothShiftedCount {x h y r : ℕ}
    (hy : 1 ≤ y) (hr : 1 ≤ r) :
    exactRankShiftedCount x h y r ≤ nonsmoothShiftedCount x h y := by
  exact Finset.card_le_card (exactRankShiftedSet_subset_nonsmoothShiftedSet hy hr)

/-! ## Successive and truncated rank decompositions -/

/-- One step of the rank filtration: rank at least `R` is the disjoint union of exact rank `R` and rank at least `R+1`.-/
theorem exactRankShiftedSet_union_atLeastRankShiftedSet_succ (x h y R : ℕ) :
    exactRankShiftedSet x h y R ∪ atLeastRankShiftedSet x h y (R + 1) =
      atLeastRankShiftedSet x h y R := by
  ext n
  rw [Finset.mem_union, mem_exactRankShiftedSet, mem_atLeastRankShiftedSet,
    mem_atLeastRankShiftedSet]
  constructor
  · rintro (⟨hn, hrank⟩ | ⟨hn, hrank⟩)
    · exact ⟨hn, hrank ▸ le_rfl⟩
    · exact ⟨hn, (Nat.le_add_right R 1).trans hrank⟩
  · rintro ⟨hn, hrank⟩
    rcases eq_or_lt_of_le hrank with heq | hlt
    · exact Or.inl ⟨hn, heq.symm⟩
    · exact Or.inr ⟨hn, hlt⟩

/-- The two pieces in the successive rank decomposition are disjoint.-/
theorem exactRankShiftedSet_disjoint_atLeastRankShiftedSet_succ (x h y R : ℕ) :
    Disjoint (exactRankShiftedSet x h y R) (atLeastRankShiftedSet x h y (R + 1)) := by
  rw [Finset.disjoint_left]
  intro n hexact hatLeast
  have heq := (mem_exactRankShiftedSet.mp hexact).2
  have hle := (mem_atLeastRankShiftedSet.mp hatLeast).2
  rw [heq] at hle
  omega

/-- Cardinal recurrence for successive rank thresholds.-/
theorem atLeastRankShiftedCount_eq_exactRank_add_succ (x h y R : ℕ) :
    atLeastRankShiftedCount x h y R =
      exactRankShiftedCount x h y R + atLeastRankShiftedCount x h y (R + 1) := by
  rw [atLeastRankShiftedCount,
    ← exactRankShiftedSet_union_atLeastRankShiftedSet_succ x h y R,
    Finset.card_union_of_disjoint
      (exactRankShiftedSet_disjoint_atLeastRankShiftedSet_succ x h y R),
    exactRankShiftedCount, atLeastRankShiftedCount]

/-- The intermediate ranks `1,…,J-1` are disjoint from rank at least `J`.-/
theorem intermediateRankShiftedSet_disjoint_atLeastRankShiftedSet (x h y J : ℕ) :
    Disjoint (intermediateRankShiftedSet x h y J) (atLeastRankShiftedSet x h y J) := by
  rw [Finset.disjoint_left]
  intro n hintermediate hatLeast
  have hlt := (mem_intermediateRankShiftedSet.mp hintermediate).2.2
  have hle := (mem_atLeastRankShiftedSet.mp hatLeast).2
  exact (Nat.not_lt_of_ge hle) hlt

/-- The nonsmooth branch is exactly ranks `1,…,J-1` together with rank at least `J`.-/
theorem intermediateRankShiftedSet_union_atLeastRankShiftedSet_eq_nonsmooth
    {x h y J : ℕ} (hy : 1 ≤ y) (hJ : 1 ≤ J) :
    intermediateRankShiftedSet x h y J ∪ atLeastRankShiftedSet x h y J =
      nonsmoothShiftedSet x h y := by
  ext n
  rw [Finset.mem_union]
  constructor
  · rintro (hintermediate | hatLeast)
    · have hData := mem_intermediateRankShiftedSet.mp hintermediate
      have hOne : n ∈ atLeastRankShiftedSet x h y 1 :=
        mem_atLeastRankShiftedSet.mpr ⟨hData.1, hData.2.1⟩
      rwa [atLeastRankShiftedSet_one_eq_nonsmoothShiftedSet hy] at hOne
    · have hData := mem_atLeastRankShiftedSet.mp hatLeast
      have hOne : n ∈ atLeastRankShiftedSet x h y 1 :=
        mem_atLeastRankShiftedSet.mpr ⟨hData.1, hJ.trans hData.2⟩
      rwa [atLeastRankShiftedSet_one_eq_nonsmoothShiftedSet hy] at hOne
  · intro hnonsmooth
    have hOne : n ∈ atLeastRankShiftedSet x h y 1 := by
      rwa [atLeastRankShiftedSet_one_eq_nonsmoothShiftedSet hy]
    have hData := mem_atLeastRankShiftedSet.mp hOne
    rcases lt_or_ge (largePrimeRank y n.totient) J with hlt | hle
    · exact Or.inl (mem_intermediateRankShiftedSet.mpr ⟨hData.1, hData.2, hlt⟩)
    · exact Or.inr (mem_atLeastRankShiftedSet.mpr ⟨hData.1, hle⟩)

/-- Cardinality of the finite intermediate-rank union.-/
theorem intermediateRankShiftedSet_card_eq_sum (x h y J : ℕ) :
    (intermediateRankShiftedSet x h y J).card =
      ∑ r ∈ Finset.Ico 1 J, exactRankShiftedCount x h y r := by
  rw [intermediateRankShiftedSet,
    Finset.card_biUnion (exactRankShiftedSet_pairwiseDisjoint x h y (Finset.Ico 1 J))]
  rfl

/-- **Exact rank truncation used in Sections 4--8.** The nonsmooth count is the sum of ranks `1,…,J-1` and the rank-at-least-`J` remainder.-/
theorem nonsmoothShiftedCount_eq_sum_exactRank_add_atLeastRank
    {x h y J : ℕ} (hy : 1 ≤ y) (hJ : 1 ≤ J) :
    nonsmoothShiftedCount x h y =
      (∑ r ∈ Finset.Ico 1 J, exactRankShiftedCount x h y r) +
        atLeastRankShiftedCount x h y J := by
  rw [nonsmoothShiftedCount,
    ← intermediateRankShiftedSet_union_atLeastRankShiftedSet_eq_nonsmooth hy hJ,
    Finset.card_union_of_disjoint
      (intermediateRankShiftedSet_disjoint_atLeastRankShiftedSet x h y J),
    intermediateRankShiftedSet_card_eq_sum, atLeastRankShiftedCount]

/-- Full finite decomposition into the smooth branch, ranks `1,…,J-1`, and rank at least `J`.-/
theorem shiftedEqualTotientCount_eq_smooth_add_sum_exactRank_add_atLeastRank
    {x h y J : ℕ} (hy : 1 ≤ y) (hJ : 1 ≤ J) :
    shiftedEqualTotientCount x h = smoothShiftedCount x h y +
      (∑ r ∈ Finset.Ico 1 J, exactRankShiftedCount x h y r) +
        atLeastRankShiftedCount x h y J := by
  rw [shiftedEqualTotientCount_eq_smooth_add_nonsmooth hy,
    nonsmoothShiftedCount_eq_sum_exactRank_add_atLeastRank hy hJ, Nat.add_assoc]

/-! ## Provider consequences -/

/-- A prime provider above `y` contributes at least one occurrence to the large-prime rank of the totient represented by a skeleton.-/
theorem LargePrimeSkeleton.one_le_largePrimeRank_totient {h n p y : ℕ}
    (s : LargePrimeSkeleton h n p) (hp : p.Prime) (hyp : y < p) :
    1 ≤ largePrimeRank y n.totient := by
  have hm₁pos : 0 < s.m1 := by
    apply Nat.pos_of_ne_zero
    intro hm₁
    apply s.q1_not_dvd_m1
    rw [hm₁]
    exact dvd_zero s.q1
  have hnpos : 0 < n := by
    rw [s.n_eq]
    exact mul_pos hm₁pos s.q1_prime.pos
  have htotient : n.totient ≠ 0 := (Nat.totient_pos.mpr hnpos).ne'
  have htotientEq : n.totient = s.m1.totient * (s.q1 - 1) :=
    totient_eq_cofactor_mul_pred s.q1_prime s.n_eq s.q1_not_dvd_m1
  have hqpred : s.q1 - 1 = s.k1 * p := by
    rw [s.q1_eq]
    omega
  have hpdiv : p ∣ n.totient := by
    refine ⟨s.m1.totient * s.k1, ?_⟩
    rw [htotientEq, hqpred]
    ac_rfl
  have hpsupport : p ∈ primeSupport n.totient :=
    Nat.mem_primeFactors.mpr ⟨hp, hpdiv, htotient⟩
  have hpfilter : p ∈ (primeSupport n.totient).filter (y < ·) :=
    Finset.mem_filter.mpr ⟨hpsupport, hyp⟩
  have hfactorPos : 0 < n.totient.factorization p :=
    hp.factorization_pos_of_dvd htotient hpdiv
  have hfactorLe : n.totient.factorization p ≤ largePrimeRank y n.totient := by
    rw [largePrimeRank]
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hpfilter
  omega

/-- The balance and cofactor fields of a skeleton imply equality of its two totients.-/
theorem LargePrimeSkeleton.totient_eq_shifted_totient {h n p : ℕ}
    (s : LargePrimeSkeleton h n p) :
    n.totient = (n + h).totient := by
  have htotient₁ : n.totient = s.m1.totient * (s.q1 - 1) :=
    totient_eq_cofactor_mul_pred s.q1_prime s.n_eq s.q1_not_dvd_m1
  have htotient₂ : (n + h).totient = s.m2.totient * (s.q2 - 1) :=
    totient_eq_cofactor_mul_pred s.q2_prime s.shifted_eq s.q2_not_dvd_m2
  have hq₁pred : s.q1 - 1 = s.k1 * p := by
    rw [s.q1_eq]
    omega
  have hq₂pred : s.q2 - 1 = s.k2 * p := by
    rw [s.q2_eq]
    omega
  calc
    n.totient = s.m1.totient * (s.q1 - 1) := htotient₁
    _ = s.m1.totient * (s.k1 * p) := by rw [hq₁pred]
    _ = p * (s.k1 * s.m1.totient) := by ac_rfl
    _ = p * (s.k2 * s.m2.totient) := by rw [s.balance]
    _ = s.m2.totient * (s.k2 * p) := by ac_rfl
    _ = s.m2.totient * (s.q2 - 1) := by rw [hq₂pred]
    _ = (n + h).totient := htotient₂.symm

/-- A skeleton with a prime provider above `y` belongs to the rank-at-least-one shifted stratum whenever its represented integer lies below the ambient cutoff.-/
theorem LargePrimeSkeleton.mem_atLeastRankShiftedSet_one {x h n p y : ℕ}
    (s : LargePrimeSkeleton h n p) (hp : p.Prime) (hyp : y < p) (hnx : n ≤ x) :
    n ∈ atLeastRankShiftedSet x h y 1 := by
  have hm₁pos : 0 < s.m1 := by
    apply Nat.pos_of_ne_zero
    intro hm₁
    apply s.q1_not_dvd_m1
    rw [hm₁]
    exact dvd_zero s.q1
  have hnpos : 0 < n := by
    rw [s.n_eq]
    exact mul_pos hm₁pos s.q1_prime.pos
  apply mem_atLeastRankShiftedSet.mpr
  refine ⟨mem_shiftedEqualTotientSet.mpr
    ⟨hnpos, hnx, s.totient_eq_shifted_totient⟩, ?_⟩
  exact s.one_le_largePrimeRank_totient hp hyp

end RankAmplification

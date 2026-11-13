import Tengoku.Rankamplificationtotient.RankAmplification.CofactorCount
import Tengoku.Rankamplificationtotient.RankAmplification.LargeCofactorFamily

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Small- and large-cofactor partition of skeleton families This module supplies the exact finite partition used in Section 4 and combines Corollary 3.4 with the large-cofactor family bound. -/

namespace RankAmplification

noncomputable section

/-- Restrict a subtype index along an inclusion of finite sets.-/
def restrictFinsetIndex {S T : Finset ℕ} (hTS : T ⊆ S) (n : {n // n ∈ T}) :
    {n // n ∈ S} :=
  ⟨n.1, hTS n.2⟩

/-- Restrict a chosen provider function to a smaller finite family.-/
def restrictProvider {S T : Finset ℕ} (hTS : T ⊆ S)
    (provider : (n : {n // n ∈ S}) → ℕ) (n : {n // n ∈ T}) : ℕ :=
  provider (restrictFinsetIndex hTS n)

/-- Restrict chosen skeleton data to a smaller finite family.-/
def restrictSkeleton {h : ℕ} {S T : Finset ℕ} (hTS : T ⊆ S)
    (provider : (n : {n // n ∈ S}) → ℕ)
    (skeleton : (n : {n // n ∈ S}) → LargePrimeSkeleton h n.1 (provider n))
    (n : {n // n ∈ T}) :
    LargePrimeSkeleton h n.1 (restrictProvider hTS provider n) :=
  skeleton (restrictFinsetIndex hTS n)

/-- Product of the two cofactors of the chosen skeleton at `n`, and zero off the family.-/
def skeletonCofactorProduct {h : ℕ} (S : Finset ℕ)
    (provider : (n : {n // n ∈ S}) → ℕ)
    (skeleton : (n : {n // n ∈ S}) → LargePrimeSkeleton h n.1 (provider n))
    (n : ℕ) : ℕ :=
  if hn : n ∈ S then
    (skeleton ⟨n, hn⟩).m1 * (skeleton ⟨n, hn⟩).m2
  else 0

theorem skeletonCofactorProduct_of_mem {h : ℕ} {S : Finset ℕ}
    {provider : (n : {n // n ∈ S}) → ℕ}
    {skeleton : (n : {n // n ∈ S}) → LargePrimeSkeleton h n.1 (provider n)}
    {n : ℕ} (hn : n ∈ S) :
    skeletonCofactorProduct S provider skeleton n =
      (skeleton ⟨n, hn⟩).m1 * (skeleton ⟨n, hn⟩).m2 := by
  simp [skeletonCofactorProduct, hn]

/-- Skeletons in the small-cofactor range.-/
def smallCofactorSkeletonSet {h : ℕ} (S : Finset ℕ)
    (provider : (n : {n // n ∈ S}) → ℕ)
    (skeleton : (n : {n // n ∈ S}) → LargePrimeSkeleton h n.1 (provider n))
    (X : ℕ) : Finset ℕ :=
  S.filter fun n ↦ skeletonCofactorProduct S provider skeleton n ≤ X

/-- Skeletons in the complementary large-cofactor range.-/
def largeCofactorSkeletonSet {h : ℕ} (S : Finset ℕ)
    (provider : (n : {n // n ∈ S}) → ℕ)
    (skeleton : (n : {n // n ∈ S}) → LargePrimeSkeleton h n.1 (provider n))
    (X : ℕ) : Finset ℕ :=
  S.filter fun n ↦ X < skeletonCofactorProduct S provider skeleton n

@[simp]
theorem mem_smallCofactorSkeletonSet {h X n : ℕ} {S : Finset ℕ}
    {provider : (n : {n // n ∈ S}) → ℕ}
    {skeleton : (n : {n // n ∈ S}) → LargePrimeSkeleton h n.1 (provider n)} :
    n ∈ smallCofactorSkeletonSet S provider skeleton X ↔
      n ∈ S ∧ skeletonCofactorProduct S provider skeleton n ≤ X := by
  simp [smallCofactorSkeletonSet]

@[simp]
theorem mem_largeCofactorSkeletonSet {h X n : ℕ} {S : Finset ℕ}
    {provider : (n : {n // n ∈ S}) → ℕ}
    {skeleton : (n : {n // n ∈ S}) → LargePrimeSkeleton h n.1 (provider n)} :
    n ∈ largeCofactorSkeletonSet S provider skeleton X ↔
      n ∈ S ∧ X < skeletonCofactorProduct S provider skeleton n := by
  simp [largeCofactorSkeletonSet]

theorem smallCofactorSkeletonSet_subset {h X : ℕ} (S : Finset ℕ)
    (provider : (n : {n // n ∈ S}) → ℕ)
    (skeleton : (n : {n // n ∈ S}) → LargePrimeSkeleton h n.1 (provider n)) :
    smallCofactorSkeletonSet S provider skeleton X ⊆ S := by
  intro n hn
  exact (mem_smallCofactorSkeletonSet.mp hn).1

theorem largeCofactorSkeletonSet_subset {h X : ℕ} (S : Finset ℕ)
    (provider : (n : {n // n ∈ S}) → ℕ)
    (skeleton : (n : {n // n ∈ S}) → LargePrimeSkeleton h n.1 (provider n)) :
    largeCofactorSkeletonSet S provider skeleton X ⊆ S := by
  intro n hn
  exact (mem_largeCofactorSkeletonSet.mp hn).1

/-- Exact disjoint partition at any cofactor-product threshold.-/
theorem small_union_large_eq {h X : ℕ} (S : Finset ℕ)
    (provider : (n : {n // n ∈ S}) → ℕ)
    (skeleton : (n : {n // n ∈ S}) → LargePrimeSkeleton h n.1 (provider n)) :
    smallCofactorSkeletonSet S provider skeleton X ∪
      largeCofactorSkeletonSet S provider skeleton X = S := by
  ext n
  by_cases hn : n ∈ S
  · by_cases hsmall : skeletonCofactorProduct S provider skeleton n ≤ X
    · simp [hn, hsmall, Nat.not_lt_of_ge hsmall]
    · have hlarge : X < skeletonCofactorProduct S provider skeleton n :=
        Nat.lt_of_not_ge hsmall
      simp [hn, hsmall, hlarge]
  · simp [hn]

theorem small_disjoint_large {h X : ℕ} (S : Finset ℕ)
    (provider : (n : {n // n ∈ S}) → ℕ)
    (skeleton : (n : {n // n ∈ S}) → LargePrimeSkeleton h n.1 (provider n)) :
    Disjoint (smallCofactorSkeletonSet S provider skeleton X)
      (largeCofactorSkeletonSet S provider skeleton X) := by
  rw [Finset.disjoint_left]
  intro n hnSmall hnLarge
  exact (Nat.not_lt_of_ge (mem_smallCofactorSkeletonSet.mp hnSmall).2)
    (mem_largeCofactorSkeletonSet.mp hnLarge).2

theorem card_eq_small_add_large {h X : ℕ} (S : Finset ℕ)
    (provider : (n : {n // n ∈ S}) → ℕ)
    (skeleton : (n : {n // n ∈ S}) → LargePrimeSkeleton h n.1 (provider n)) :
    S.card = (smallCofactorSkeletonSet S provider skeleton X).card +
      (largeCofactorSkeletonSet S provider skeleton X).card := by
  rw [← Finset.card_union_of_disjoint (small_disjoint_large S provider skeleton),
    small_union_large_eq S provider skeleton]

/-- Corollary 3.4 applied directly to the small half of a chosen skeleton family.-/
theorem card_smallCofactorSkeletonSet_le {h X : ℕ} (hodd : Odd h) (S : Finset ℕ)
    (provider : (n : {n // n ∈ S}) → ℕ)
    (skeleton : (n : {n // n ∈ S}) → LargePrimeSkeleton h n.1 (provider n)) :
    ((smallCofactorSkeletonSet S provider skeleton X).card : ℝ) ≤
      X * (1 + Real.log X) := by
  let T := smallCofactorSkeletonSet S provider skeleton X
  have hTS : T ⊆ S := smallCofactorSkeletonSet_subset S provider skeleton
  let providerT := restrictProvider hTS provider
  let skeletonT := restrictSkeleton hTS provider skeleton
  apply card_skeletonNumbers_le_cofactor_bound hodd T providerT skeletonT
  intro n
  have hnSmall := mem_smallCofactorSkeletonSet.mp n.2
  have hprod := hnSmall.2
  rw [skeletonCofactorProduct_of_mem hnSmall.1] at hprod
  simpa [T, providerT, skeletonT, restrictSkeleton, restrictFinsetIndex] using hprod

end

end RankAmplification

import Tengoku.Rankamplificationtotient.RankAmplification.CofactorCount
import Tengoku.Rankamplificationtotient.RankAmplification.DivisorSmoothTail

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Smooth ordered factor pairs This module formalizes the exact divisor-counting reindexing in equation (4.6). -/

namespace RankAmplification

noncomputable section

/-- Positive ordered pairs whose product is at most `X` and `R`-smooth.-/
noncomputable def smoothFactorPairSet (R X : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (cofactorPairSet X).filter fun k ↦ IsSmooth R (k.1 * k.2)

/--
@isnad1 id=iff.0h4v.s6.8eb640c8b93d from=translated src=- shape=a813811e vocab=8c680568
-/
@[simp]
theorem mem_smoothFactorPairSet {R X k₁ k₂ : ℕ} :
    (k₁, k₂) ∈ smoothFactorPairSet R X ↔
      1 ≤ k₁ ∧ 1 ≤ k₂ ∧ k₁ * k₂ ≤ X ∧ IsSmooth R (k₁ * k₂) := by
  classical
  simp [smoothFactorPairSet, and_assoc]

/-- The product map sends every smooth factor pair to the finite smooth census.
@isnad1 id=mapsto.0h2v.s5.5c95b1703adc from=translated src=- shape=52ca5237 vocab=dc416557
-/
theorem smoothFactorPairSet_product_mapsTo (R X : ℕ) :
    ((smoothFactorPairSet R X : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).MapsTo
      (fun k ↦ k.1 * k.2) (finiteSmoothSet R X : Set ℕ) := by
  intro k hk
  obtain ⟨hk₁, hk₂, hkX, hsmooth⟩ := mem_smoothFactorPairSet.mp hk
  exact mem_finiteSmoothSet.mpr ⟨Nat.mul_pos hk₁ hk₂, hkX, hsmooth⟩

/-- A fixed-product fibre of positive ordered factor pairs has exactly `τ(m)` elements.
@isnad1 id=eq.1h3v.s6.8d81a5f95858 from=translated src=- shape=11f03ece vocab=2aeda562
-/
theorem smoothFactorPair_fiber_card_eq_divisors {R X m : ℕ}
    (hm : m ∈ finiteSmoothSet R X) :
    ((smoothFactorPairSet R X).filter fun k ↦ k.1 * k.2 = m).card = m.divisors.card := by
  classical
  let F := (smoothFactorPairSet R X).filter fun k ↦ k.1 * k.2 = m
  have hmData := mem_finiteSmoothSet.mp hm
  change F.card = m.divisors.card
  apply Finset.card_bij (fun k _ ↦ k.1)
  · intro k hk
    have hk' := Finset.mem_filter.mp hk
    have hprod : k.1 * k.2 = m := hk'.2
    apply Nat.mem_divisors.mpr
    refine ⟨?_, Nat.one_le_iff_ne_zero.mp hmData.1⟩
    exact ⟨k.2, hprod.symm⟩
  · intro a ha b hb hab
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    have haData := mem_smoothFactorPairSet.mp ha'.1
    apply Prod.ext hab
    apply Nat.mul_left_cancel haData.1
    calc
      a.1 * a.2 = m := ha'.2
      _ = b.1 * b.2 := hb'.2.symm
      _ = a.1 * b.2 := by rw [hab]
  · intro d hd
    have hdData := Nat.mem_divisors.mp hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdData.1 hmData.1
    have hdm : d ≤ m := Nat.le_of_dvd hmData.1 hdData.1
    have hquotpos : 0 < m / d := Nat.div_pos hdm hdpos
    have hprod : d * (m / d) = m := Nat.mul_div_cancel' hdData.1
    have hsmoothprod : IsSmooth R (d * (m / d)) := by
      rw [hprod]
      exact hmData.2.2
    refine ⟨(d, m / d), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨mem_smoothFactorPairSet.mpr
      ⟨hdpos, hquotpos, hprod.le.trans hmData.2.1, hsmoothprod⟩, hprod⟩

/-- Exact natural-cardinality form of the reindexing in (4.6).
@isnad1 id=eq.0h2v.s4.0ef1e0523da9 from=translated src=- shape=251fdd0f vocab=92f411e0
-/
theorem card_smoothFactorPairSet_eq_sum_divisors (R X : ℕ) :
    (smoothFactorPairSet R X).card =
      ∑ m ∈ finiteSmoothSet R X, m.divisors.card := by
  classical
  calc
    (smoothFactorPairSet R X).card =
        ∑ m ∈ finiteSmoothSet R X,
          ((smoothFactorPairSet R X).filter fun k ↦ k.1 * k.2 = m).card :=
      Finset.card_eq_sum_card_fiberwise (smoothFactorPairSet_product_mapsTo R X)
    _ = ∑ m ∈ finiteSmoothSet R X, m.divisors.card := by
      apply Finset.sum_congr rfl
      intro m hm
      exact smoothFactorPair_fiber_card_eq_divisors hm

/-- Exact real-valued identity with the paper's `Ψτ(X,R)`.
@isnad1 id=eq.0h2v.s4.985d71bf6461 from=translated src=- shape=51b252d7 vocab=324a1441
-/
theorem card_smoothFactorPairSet_cast_eq (R X : ℕ) :
    ((smoothFactorPairSet R X).card : ℝ) = finiteDivisorWeightedSmoothCount R X := by
  rw [card_smoothFactorPairSet_eq_sum_divisors, Nat.cast_sum,
    finiteDivisorWeightedSmoothCount_eq]

/-- Dropping the `+1` terms in two provider forms gives the cutoff used in (4.6).
@isnad1 id=le.2h4v.s6.0dfe400bec0e from=translated src=- shape=050e4ee5 vocab=dc46af4e
-/
theorem multiplier_product_le_div_sq {p k₁ k₂ X : ℕ} (hp : 0 < p)
    (hprovider : (k₁ * p + 1) * (k₂ * p + 1) ≤ X) :
    k₁ * k₂ ≤ X / p ^ 2 := by
  have hleft : k₁ * p ≤ k₁ * p + 1 := Nat.le_add_right _ _
  have hright : k₂ * p ≤ k₂ * p + 1 := Nat.le_add_right _ _
  have hmul : (k₁ * p) * (k₂ * p) ≤ X :=
    (Nat.mul_le_mul hleft hright).trans hprovider
  rw [Nat.le_div_iff_mul_le (pow_pos hp 2)]
  calc
    k₁ * k₂ * p ^ 2 = (k₁ * p) * (k₂ * p) := by ring
    _ ≤ X := hmul

/-- Any finite family of actual provider multiplier pairs is bounded by the smooth census in (4.6).
@isnad1 id=le.2h3v.s7.8d8690aa5ac8 from=translated src=- shape=ebaa7bfb vocab=cbea4598
-/
theorem card_providerMultiplierFamily_cast_le {p X : ℕ} (hp : 0 < p)
    (S : Finset (ℕ × ℕ))
    (hS : ∀ k ∈ S,
      1 ≤ k.1 ∧ 1 ≤ k.2 ∧ IsSmooth p (k.1 * k.2) ∧
        (k.1 * p + 1) * (k.2 * p + 1) ≤ X) :
    (S.card : ℝ) ≤ finiteDivisorWeightedSmoothCount p (X / p ^ 2) := by
  have hsubset : S ⊆ smoothFactorPairSet p (X / p ^ 2) := by
    intro k hk
    obtain ⟨hk₁, hk₂, hsmooth, hprovider⟩ := hS k hk
    exact mem_smoothFactorPairSet.mpr
      ⟨hk₁, hk₂, multiplier_product_le_div_sq hp hprovider, hsmooth⟩
  have hcard : S.card ≤ (smoothFactorPairSet p (X / p ^ 2)).card :=
    Finset.card_le_card hsubset
  calc
    (S.card : ℝ) ≤ ((smoothFactorPairSet p (X / p ^ 2)).card : ℝ) := by exact_mod_cast hcard
    _ = finiteDivisorWeightedSmoothCount p (X / p ^ 2) :=
      card_smoothFactorPairSet_cast_eq _ _

end

end RankAmplification

import Tengoku.Rankamplificationtotient.RankAmplification.SmallCofactor
import Tengoku.Seed.NumberTheory.Harmonic.Bounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Counting small cofactor pairs The elementary divisor-hyperbola estimate completing the counting part of Corollary 3.4. -/

namespace RankAmplification

open scoped BigOperators

noncomputable section

/-- Dependent-pair encoding of positive ordered pairs with product at most `X`.-/
def cofactorPairSigma (X : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.Icc 1 X).sigma fun m ↦ Finset.Icc 1 (X / m)

private def sigmaNatToPair : (Σ _ : ℕ, ℕ) ↪ (ℕ × ℕ) where
  toFun z := (z.1, z.2)
  inj' := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq] at h
    cases h.1
    cases h.2
    rfl

/-- The same finite collection as ordinary ordered pairs.-/
def cofactorPairSet (X : ℕ) : Finset (ℕ × ℕ) :=
  (cofactorPairSigma X).map sigmaNatToPair

/--
@isnad1 id=iff.0h3v.s6.684fe609f22d from=translated src=- shape=bdb56928 vocab=6566a491
-/
@[simp]
theorem mem_cofactorPairSet {X m₁ m₂ : ℕ} :
    (m₁, m₂) ∈ cofactorPairSet X ↔ 1 ≤ m₁ ∧ 1 ≤ m₂ ∧ m₁ * m₂ ≤ X := by
  classical
  constructor
  · intro hmem
    obtain ⟨z, hz, hzEq⟩ := Finset.mem_map.mp hmem
    obtain ⟨a, b⟩ := z
    simp only [sigmaNatToPair] at hzEq
    obtain ⟨rfl, rfl⟩ := hzEq
    have hz' := Finset.mem_sigma.mp hz
    have ha := Finset.mem_Icc.mp hz'.1
    have hb := Finset.mem_Icc.mp hz'.2
    exact ⟨ha.1, hb.1, by
      rw [mul_comm, ← Nat.le_div_iff_mul_le ha.1]
      exact hb.2⟩
  · rintro ⟨hm₁, hm₂, hprod⟩
    have hm₁X : m₁ ≤ X := by
      calc
        m₁ = m₁ * 1 := (Nat.mul_one m₁).symm
        _ ≤ m₁ * m₂ := Nat.mul_le_mul_left m₁ hm₂
        _ ≤ X := hprod
    apply Finset.mem_map.mpr
    refine ⟨⟨m₁, m₂⟩, ?_, rfl⟩
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hm₁, hm₁X⟩, Finset.mem_Icc.mpr ⟨hm₂, ?_⟩⟩
    rw [Nat.le_div_iff_mul_le hm₁, mul_comm]
    exact hprod

/--
@isnad1 id=eq.0h1v.s5.f9f866400b62 from=translated src=- shape=bb5f4c8a vocab=298f82b0
-/
theorem card_cofactorPairSet_eq_sum_div (X : ℕ) :
    (cofactorPairSet X).card = ∑ m ∈ Finset.Icc 1 X, X / m := by
  classical
  rw [cofactorPairSet, Finset.card_map, cofactorPairSigma, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro m hm
  simp [Nat.card_Icc]

/--
@isnad1 id=le.0h1v.s5.d80069626fe2 from=translated src=- shape=f7f6b3f3 vocab=258be4c3
-/
theorem real_harmonic_sum_le (X : ℕ) :
    (∑ m ∈ Finset.Icc 1 X, (m : ℝ)⁻¹) ≤ 1 + Real.log X := by
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
    Rat.cast_ofNat] using harmonic_le_one_add_log X

/-- Explicit divisor-hyperbola bound: at most `X(1+log X)` positive ordered pairs.
@isnad1 id=le.0h1v.s5.2aea17bc396d from=translated src=- shape=16417a38 vocab=d6723f65
-/
theorem card_cofactorPairSet_cast_le (X : ℕ) :
    ((cofactorPairSet X).card : ℝ) ≤ X * (1 + Real.log X) := by
  rw [card_cofactorPairSet_eq_sum_div, Nat.cast_sum]
  calc
    (∑ m ∈ Finset.Icc 1 X, ((X / m : ℕ) : ℝ)) ≤
        ∑ m ∈ Finset.Icc 1 X, (X : ℝ) * (m : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro m hm
      have hcast := Nat.cast_div_le (α := ℝ) (m := X) (n := m)
      simpa only [div_eq_mul_inv] using hcast
    _ = (X : ℝ) * ∑ m ∈ Finset.Icc 1 X, (m : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ (X : ℝ) * (1 + Real.log X) :=
      mul_le_mul_of_nonneg_left (real_harmonic_sum_le X) (Nat.cast_nonneg X)

/-- Fully quantitative finite form of Corollary 3.4 for any chosen family of skeletons.
@isnad1 id=le.2h5v.s7.63c1615b8a9f from=translated src=- shape=b8be98b0 vocab=cfc48fff
-/
theorem card_skeletonNumbers_le_cofactor_bound {h X : ℕ} (hodd : Odd h) (S : Finset ℕ)
    (provider : (x : {n // n ∈ S}) → ℕ)
    (skeleton : (x : {n // n ∈ S}) → LargePrimeSkeleton h x.1 (provider x))
    (hsmall : ∀ x, (skeleton x).m1 * (skeleton x).m2 ≤ X) :
    (S.card : ℝ) ≤ X * (1 + Real.log X) := by
  let imagePairs := S.attach.image fun x ↦ ((skeleton x).m1, (skeleton x).m2)
  have hsubset : imagePairs ⊆ cofactorPairSet X := by
    intro pair hpair
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hpair
    exact mem_cofactorPairSet.mpr
      ⟨(skeleton x).m1_pos, (skeleton x).m2_pos, hsmall x⟩
  have hcard : imagePairs.card ≤ (cofactorPairSet X).card := Finset.card_le_card hsubset
  have himage : imagePairs.card = S.card :=
    card_cofactorPair_image_eq hodd S provider skeleton
  rw [himage] at hcard
  exact (Nat.cast_le.mpr hcard).trans (card_cofactorPairSet_cast_le X)

end

end RankAmplification

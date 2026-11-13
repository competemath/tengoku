import Tengoku.Rankamplificationtotient.RankAmplification.LargeCofactor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Finite families of large-cofactor skeletons This file completes the combinatorial summation step in Section 4. -/

namespace RankAmplification

open scoped BigOperators

noncomputable section

/-- The three numerical parameters that determine the two provider primes.-/
structure ProviderCode where
  /-- Large prime supplied to the two affine provider forms.-/
  p : ℕ
  /-- Multiplier in the first provider form.-/
  k1 : ℕ
  /-- Multiplier in the second provider form.-/
  k2 : ℕ
  deriving DecidableEq

/-- Product of the two affine provider forms encoded by a code.-/
def ProviderCode.denominator (c : ProviderCode) : ℕ :=
  (c.k1 * c.p + 1) * (c.k2 * c.p + 1)

private def sigmaToProviderCode : (Σ _ : ℕ, ℕ × ℕ) ↪ ProviderCode where
  toFun z := ⟨z.1, z.2.1, z.2.2⟩
  inj' := by
    rintro ⟨p, k₁, k₂⟩ ⟨q, l₁, l₂⟩ h
    cases h
    rfl

/-- The finite universe of codes used in the large-cofactor sum.-/
def largeCofactorCodeSet (x y P : ℕ) : Finset ProviderCode :=
  ((Finset.Ioc y P).sigma fun p ↦ smoothFactorPairSet p ((2 * x * y) / p ^ 2)).map
    sigmaToProviderCode

/--
@isnad1 id=iff.0h4v.s6.0ec7ce397bce from=translated src=- shape=607f3fa2 vocab=30733246
-/
@[simp]
theorem mem_largeCofactorCodeSet {x y P : ℕ} {c : ProviderCode} :
    c ∈ largeCofactorCodeSet x y P ↔
      y < c.p ∧ c.p ≤ P ∧
        (c.k1, c.k2) ∈ smoothFactorPairSet c.p ((2 * x * y) / c.p ^ 2) := by
  constructor
  · intro hc
    obtain ⟨z, hz, hzc⟩ := Finset.mem_map.mp hc
    obtain ⟨p, k₁, k₂⟩ := z
    have hzData := Finset.mem_sigma.mp hz
    have hpData := Finset.mem_Ioc.mp hzData.1
    cases hzc
    exact ⟨hpData.1, hpData.2, hzData.2⟩
  · rintro ⟨hyp, hpP, hk⟩
    apply Finset.mem_map.mpr
    refine ⟨⟨c.p, (c.k1, c.k2)⟩, ?_, rfl⟩
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Ioc.mpr ⟨hyp, hpP⟩, hk⟩

/-- The code attached to a chosen skeleton.-/
def providerCodeOf {h : ℕ} {S : Finset ℕ}
    (provider : (n : {n // n ∈ S}) → ℕ)
    (skeleton : (n : {n // n ∈ S}) → LargePrimeSkeleton h n.1 (provider n))
    (n : {n // n ∈ S}) : ProviderCode :=
  ⟨provider n, (skeleton n).k1, (skeleton n).k2⟩

/-- The finite set of codes that actually occur in a chosen skeleton family.-/
def providerCodeImage {h : ℕ} (S : Finset ℕ)
    (provider : (n : {n // n ∈ S}) → ℕ)
    (skeleton : (n : {n // n ∈ S}) → LargePrimeSkeleton h n.1 (provider n)) :
    Finset ProviderCode :=
  S.attach.image (providerCodeOf provider skeleton)

/-- Exact fibre decomposition of a finite skeleton family by `(p,k₁,k₂)`.
@isnad1 id=eq.0h4v.s7.73791d981664 from=translated src=- shape=977bfa4d vocab=990fe6f8
-/
theorem card_eq_sum_providerCode_fibers {h : ℕ} (S : Finset ℕ)
    (provider : (n : {n // n ∈ S}) → ℕ)
    (skeleton : (n : {n // n ∈ S}) → LargePrimeSkeleton h n.1 (provider n)) :
    S.card = ∑ c ∈ providerCodeImage S provider skeleton,
      (S.attach.filter fun n ↦ providerCodeOf provider skeleton n = c).card := by
  let f := providerCodeOf provider skeleton
  have hmaps : (S.attach : Set {n // n ∈ S}).MapsTo f
      (providerCodeImage S provider skeleton : Set ProviderCode) := by
    intro n hn
    exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
  simpa [providerCodeImage, f] using Finset.card_eq_sum_card_fiberwise hmaps

private def subtypeNatEmbedding {S : Finset ℕ} : {n // n ∈ S} ↪ ℕ where
  toFun n := n.1
  inj' _ _ h := Subtype.ext h

/-- A fixed-code fibre occupies at most one residue class modulo the product of its providers.
@isnad1 id=le.3h6v.s7.1232d8c552e0 from=translated src=- shape=bac74952 vocab=6c6db0d1
-/
theorem providerCode_fiber_card_le {x h : ℕ} (S : Finset ℕ)
    (provider : (n : {n // n ∈ S}) → ℕ)
    (skeleton : (n : {n // n ∈ S}) → LargePrimeSkeleton h n.1 (provider n))
    (hnx : ∀ n : {n // n ∈ S}, n.1 ≤ x) (hh : 0 < h)
    (hph : ∀ n : {n // n ∈ S}, h < provider n)
    (c : ProviderCode) :
    (S.attach.filter fun n ↦ providerCodeOf provider skeleton n = c).card ≤
      x / c.denominator + 1 := by
  let F := S.attach.filter fun n ↦ providerCodeOf provider skeleton n = c
  by_cases hF : F = ∅
  · simp [F, hF]
  · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hF
    have haData := Finset.mem_filter.mp ha
    have haCode : providerCodeOf provider skeleton a = c := haData.2
    have hpEq : provider a = c.p := congrArg ProviderCode.p haCode
    have hk1Eq : (skeleton a).k1 = c.k1 := congrArg ProviderCode.k1 haCode
    have hk2Eq : (skeleton a).k2 = c.k2 := congrArg ProviderCode.k2 haCode
    have hq1 : (c.k1 * c.p + 1).Prime := by
      rw [← hpEq, ← hk1Eq, ← (skeleton a).q1_eq]
      exact (skeleton a).q1_prime
    have hq2 : (c.k2 * c.p + 1).Prime := by
      rw [← hpEq, ← hk2Eq, ← (skeleton a).q2_eq]
      exact (skeleton a).q2_prime
    have hk1pos : 0 < c.k1 := by simpa [← hk1Eq] using (skeleton a).k1_pos
    have hpc : h < c.p := by simpa [← hpEq] using hph a
    have hcq1 : c.p < c.k1 * c.p + 1 := by
      calc
        c.p = 1 * c.p := (Nat.one_mul c.p).symm
        _ ≤ c.k1 * c.p := Nat.mul_le_mul_right c.p hk1pos
        _ < c.k1 * c.p + 1 := Nat.lt_succ_self _
    have hlarge : ∀ r : ℕ, r.Prime → r ∣ c.k1 * c.p + 1 → h < r := by
      intro r hr hrd
      have hre : r = c.k1 * c.p + 1 := (Nat.prime_dvd_prime_iff_eq hr hq1).mp hrd
      rw [hre]
      exact hpc.trans hcq1
    have hsubset : F.map subtypeNatEmbedding ⊆
        shiftedDivisibilitySet x h (c.k1 * c.p + 1) (c.k2 * c.p + 1) := by
      intro n hn
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hn
      have hbCode : providerCodeOf provider skeleton b = c := (Finset.mem_filter.mp hb).2
      have hpEq' : provider b = c.p := congrArg ProviderCode.p hbCode
      have hk1Eq' : (skeleton b).k1 = c.k1 := congrArg ProviderCode.k1 hbCode
      have hk2Eq' : (skeleton b).k2 = c.k2 := congrArg ProviderCode.k2 hbCode
      have hbpos : 0 < b.1 := by
        rw [(skeleton b).n_eq]
        exact Nat.mul_pos (skeleton b).m1_pos (skeleton b).q1_prime.pos
      apply mem_shiftedDivisibilitySet.mpr
      refine ⟨hbpos, hnx b, ?_, ?_⟩
      · rw [← hpEq', ← hk1Eq', ← (skeleton b).q1_eq]
        exact (skeleton b).q1_dvd
      · rw [← hpEq', ← hk2Eq', ← (skeleton b).q2_eq]
        exact (skeleton b).q2_dvd
    have hcardMap : (F.map subtypeNatEmbedding).card ≤
        (shiftedDivisibilitySet x h (c.k1 * c.p + 1) (c.k2 * c.p + 1)).card :=
      Finset.card_le_card hsubset
    have hresidue := shiftedDivisibilitySet_card_le (x := x) hh hq1.pos hq2.pos hlarge
    simpa [F, ProviderCode.denominator] using hcardMap.trans hresidue

/-- The provider prime is below the square-root endpoint forced by `q₁q₂ ≤ 2xy`.
@isnad1 id=le.5h6v.s6.fbce63acecb5 from=translated src=- shape=14f3470d vocab=394ee238
-/
theorem LargePrimeSkeleton.provider_le_sqrt_two_mul_xy {h n p x y : ℕ}
    (s : LargePrimeSkeleton h n p) (hnx : n ≤ x) (hy : 0 < y) (hhy : h ≤ y)
    (hxy : y ≤ x) (hlarge : x / y < s.m1 * s.m2) :
    p ≤ (2 * x * y).sqrt := by
  apply Nat.le_sqrt'.2
  have hpq1 : p ≤ s.q1 := by
    rw [s.q1_eq]
    calc
      p = 1 * p := (Nat.one_mul p).symm
      _ ≤ s.k1 * p := Nat.mul_le_mul_right p s.k1_pos
      _ ≤ s.k1 * p + 1 := Nat.le_add_right _ _
  have hpq2 : p ≤ s.q2 := by
    rw [s.q2_eq]
    calc
      p = 1 * p := (Nat.one_mul p).symm
      _ ≤ s.k2 * p := Nat.mul_le_mul_right p s.k2_pos
      _ ≤ s.k2 * p + 1 := Nat.le_add_right _ _
  calc
    p ^ 2 = p * p := pow_two p
    _ ≤ s.q1 * s.q2 := Nat.mul_le_mul hpq1 hpq2
    _ ≤ 2 * x * y := s.provider_product_le_two_mul_xy hnx hy hhy hxy hlarge

/-- Every actual large-cofactor code belongs to the canonical finite code universe.
@isnad1 id=le.7h6v.s8.fc5659245856 from=translated src=- shape=d4d4c0ed vocab=9fe845b3
-/
theorem providerCodeImage_subset_largeCofactorCodeSet {x h y : ℕ} (S : Finset ℕ)
    (provider : (n : {n // n ∈ S}) → ℕ)
    (skeleton : (n : {n // n ∈ S}) → LargePrimeSkeleton h n.1 (provider n))
    (hnx : ∀ n : {n // n ∈ S}, n.1 ≤ x)
    (hp : ∀ n : {n // n ∈ S}, (provider n).Prime)
    (hyp : ∀ n : {n // n ∈ S}, y < provider n)
    (hy : 0 < y) (hhy : h ≤ y) (hxy : y ≤ x)
    (hlarge : ∀ n : {n // n ∈ S}, x / y < (skeleton n).m1 * (skeleton n).m2) :
    providerCodeImage S provider skeleton ⊆
      largeCofactorCodeSet x y (2 * x * y).sqrt := by
  intro c hc
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hc
  let s := skeleton n
  apply mem_largeCofactorCodeSet.mpr
  refine ⟨hyp n, s.provider_le_sqrt_two_mul_xy (hnx n) hy hhy hxy (hlarge n), ?_⟩
  exact s.multiplier_pair_mem_large_cofactor_set (hnx n) (hp n).pos hy hhy hxy (hlarge n)

end

end RankAmplification

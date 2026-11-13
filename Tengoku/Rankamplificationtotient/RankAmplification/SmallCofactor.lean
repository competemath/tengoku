import Tengoku.Rankamplificationtotient.RankAmplification.Provider
import Tengoku.Rankamplificationtotient.RankAmplification.Elementary
import Tengoku.Seed.Tactic.FieldSimp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Uniqueness at fixed small cofactors This file formalizes the arithmetic uniqueness argument of paper Lemma 3.3. -/

namespace RankAmplification

/-- The numerator obtained by multiplying the reduced Euler factors belonging to a prime set.-/
def eulerNumerator (s : Finset ℕ) : ℕ := ∏ p ∈ s, (p - 1)

/-- The denominator obtained by multiplying the reduced Euler factors belonging to a prime set.-/
def eulerDenominator (s : Finset ℕ) : ℕ := ∏ p ∈ s, p

/-- A finite product of Euler factors is the quotient of the corresponding integral products.
@isnad1 id=eq.1h1v.s6.599a61c873f0 from=translated src=- shape=1d5b9293 vocab=6a7eb38c
-/
theorem prod_eulerFactor_eq_div (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, (1 - (p : ℚ)⁻¹)) = (eulerNumerator s : ℚ) / eulerDenominator s := by
  classical
  rw [eulerNumerator, eulerDenominator, Nat.cast_prod, Nat.cast_prod]
  calc
    (∏ p ∈ s, (1 - (p : ℚ)⁻¹)) =
        ∏ p ∈ s, ((p - 1 : ℕ) : ℚ) / (p : ℚ) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hpprime := hs p hp
      have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpprime.ne_zero
      rw [Nat.cast_sub hpprime.one_le]
      field_simp [hpQ]
      norm_num
    _ = (∏ p ∈ s, ((p - 1 : ℕ) : ℚ)) / ∏ p ∈ s, (p : ℚ) :=
      Finset.prod_div_distrib (s := s) _ _

/-- Cross-multiplying equal Euler ratios gives an integral identity on their prime supports.
@isnad1 id=eq.3h2v.s6.391a37afbf85 from=translated src=- shape=d43a0be2 vocab=5e6f37cd
-/
theorem euler_products_cross_eq_of_totient_cross_eq {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcross : a.totient * b = b.totient * a) :
    eulerNumerator (primeSupport a) * eulerDenominator (primeSupport b) =
      eulerNumerator (primeSupport b) * eulerDenominator (primeSupport a) := by
  have hcrossQ : (a.totient : ℚ) * (b : ℚ) = (b.totient : ℚ) * (a : ℚ) := by
    exact_mod_cast hcross
  have hratio : (a.totient : ℚ) / a = (b.totient : ℚ) / b :=
    (div_eq_div_iff (Nat.cast_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr hb)).mpr hcrossQ
  rw [Nat.totient_eq_mul_prod_factors, Nat.totient_eq_mul_prod_factors,
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr ha),
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hb)] at hratio
  have hprimeA : ∀ p ∈ primeSupport a, p.Prime := fun p hp ↦
    Nat.prime_of_mem_primeFactors hp
  have hprimeB : ∀ p ∈ primeSupport b, p.Prime := fun p hp ↦
    Nat.prime_of_mem_primeFactors hp
  rw [prod_eulerFactor_eq_div (primeSupport a) hprimeA,
    prod_eulerFactor_eq_div (primeSupport b) hprimeB] at hratio
  have hdenA : eulerDenominator (primeSupport a) ≠ 0 := by
    rw [eulerDenominator]
    exact (Finset.prod_pos fun p hp ↦ (hprimeA p hp).pos).ne'
  have hdenB : eulerDenominator (primeSupport b) ≠ 0 := by
    rw [eulerDenominator]
    exact (Finset.prod_pos fun p hp ↦ (hprimeB p hp).pos).ne'
  have hcrossQ' :=
    (div_eq_div_iff (Nat.cast_ne_zero.mpr hdenA) (Nat.cast_ne_zero.mpr hdenB)).mp hratio
  exact_mod_cast hcrossQ'

/-- The largest prime occurring in either of two prime sets satisfying the Euler-product cross identity occurs in both sets.
@isnad1 id=other.4h2v.s6.c56a93cc1eb5 from=translated src=- shape=d309dfd5 vocab=f53307ea
-/
theorem max_mem_both_of_euler_products_cross_eq (S T : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime) (hT : ∀ q ∈ T, q.Prime) (hne : (S ∪ T).Nonempty)
    (hcross : eulerNumerator S * eulerDenominator T =
      eulerNumerator T * eulerDenominator S) :
    let P := (S ∪ T).max' hne
    P ∈ S ∧ P ∈ T := by
  classical
  let P := (S ∪ T).max' hne
  have hPmem : P ∈ S ∪ T := by
    exact Finset.max'_mem (S ∪ T) hne
  have hPprime : P.Prime := by
    rcases Finset.mem_union.mp hPmem with hPS | hPT
    · exact hS P hPS
    · exact hT P hPT
  have hSle : ∀ q ∈ S, q ≤ P := by
    intro q hq
    exact (S ∪ T).le_max' q (Finset.mem_union_left T hq)
  have hTle : ∀ q ∈ T, q ≤ P := by
    intro q hq
    exact (S ∪ T).le_max' q (Finset.mem_union_right S hq)
  have one_sided_impossible (A B : Finset ℕ) (hA : ∀ q ∈ A, q.Prime)
      (hB : ∀ q ∈ B, q.Prime) (hAle : ∀ q ∈ A, q ≤ P)
      (heq : eulerNumerator A * eulerDenominator B =
        eulerNumerator B * eulerDenominator A)
      (hPA : P ∈ A) (hPB : P ∉ B) : False := by
    have hPdenA : P ∣ eulerDenominator A := by
      rw [eulerDenominator]
      exact Finset.dvd_prod_of_mem id hPA
    have hPright : P ∣ eulerNumerator B * eulerDenominator A :=
      dvd_mul_of_dvd_right hPdenA _
    have hPleft : P ∣ eulerNumerator A * eulerDenominator B := by
      rw [heq]
      exact hPright
    rcases hPprime.dvd_mul.mp hPleft with hPnumA | hPdenB
    · rw [eulerNumerator] at hPnumA
      obtain ⟨q, hqA, hPpred⟩ :=
        exists_mem_dvd_finset_prod_of_prime hPprime A (fun q ↦ q - 1) hPnumA
      have hqprime := hA q hqA
      have hpredpos : 0 < q - 1 := Nat.sub_pos_of_lt hqprime.one_lt
      have hPle : P ≤ q - 1 := Nat.le_of_dvd hpredpos hPpred
      have hqle := hAle q hqA
      omega
    · rw [eulerDenominator] at hPdenB
      obtain ⟨q, hqB, hPq⟩ :=
        exists_mem_dvd_finset_prod_of_prime hPprime B id hPdenB
      have hqprime := hB q hqB
      have hPeq : P = q := (Nat.prime_dvd_prime_iff_eq hPprime hqprime).mp hPq
      exact hPB (hPeq ▸ hqB)
  rcases Finset.mem_union.mp hPmem with hPS | hPT
  · refine ⟨hPS, ?_⟩
    by_contra hPnotT
    exact one_sided_impossible S T hS hT hSle hcross hPS hPnotT
  · refine ⟨?_, hPT⟩
    by_contra hPnotS
    exact one_sided_impossible T S hT hS hTle hcross.symm hPT hPnotS

/-- Finite sets of primes are determined by the product of their Euler factors.
@isnad1 id=eq.3h2v.s6.f80911ef624e from=translated src=- shape=aed072dd vocab=7d939df8
-/
theorem primeFinset_eq_of_euler_products_cross_eq (S T : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime) (hT : ∀ q ∈ T, q.Prime)
    (hcross : eulerNumerator S * eulerDenominator T =
      eulerNumerator T * eulerDenominator S) :
    S = T := by
  classical
  induction hcard : S.card + T.card using Nat.strong_induction_on generalizing S T with
  | h k ih =>
      by_cases hne : (S ∪ T).Nonempty
      · let P := (S ∪ T).max' hne
        have hPboth : P ∈ S ∧ P ∈ T :=
          max_mem_both_of_euler_products_cross_eq S T hS hT hne hcross
        have hPS := hPboth.1
        have hPT := hPboth.2
        have hnumS : eulerNumerator S = eulerNumerator (S.erase P) * (P - 1) := by
          rw [eulerNumerator, eulerNumerator]
          exact (Finset.prod_erase_mul S (fun q ↦ q - 1) hPS).symm
        have hnumT : eulerNumerator T = eulerNumerator (T.erase P) * (P - 1) := by
          rw [eulerNumerator, eulerNumerator]
          exact (Finset.prod_erase_mul T (fun q ↦ q - 1) hPT).symm
        have hdenS : eulerDenominator S = eulerDenominator (S.erase P) * P := by
          rw [eulerDenominator, eulerDenominator]
          exact (Finset.prod_erase_mul S id hPS).symm
        have hdenT : eulerDenominator T = eulerDenominator (T.erase P) * P := by
          rw [eulerDenominator, eulerDenominator]
          exact (Finset.prod_erase_mul T id hPT).symm
        have hPprime := hS P hPS
        have hfactor : (P - 1) * P ≠ 0 :=
          mul_ne_zero (Nat.sub_ne_zero_of_lt hPprime.one_lt) hPprime.ne_zero
        have hcrossErase :
            eulerNumerator (S.erase P) * eulerDenominator (T.erase P) =
              eulerNumerator (T.erase P) * eulerDenominator (S.erase P) := by
          apply (mul_right_inj' hfactor).mp
          calc
            (P - 1) * P *
                (eulerNumerator (S.erase P) * eulerDenominator (T.erase P)) =
                eulerNumerator S * eulerDenominator T := by
                  rw [hnumS, hdenT]
                  ac_rfl
            _ = eulerNumerator T * eulerDenominator S := hcross
            _ = (P - 1) * P *
                (eulerNumerator (T.erase P) * eulerDenominator (S.erase P)) := by
                  rw [hnumT, hdenS]
                  ac_rfl
        have hSerase : ∀ q ∈ S.erase P, q.Prime := by
          intro q hq
          exact hS q (Finset.mem_of_mem_erase hq)
        have hTerase : ∀ q ∈ T.erase P, q.Prime := by
          intro q hq
          exact hT q (Finset.mem_of_mem_erase hq)
        have hlt : (S.erase P).card + (T.erase P).card < k := by
          have hScard : 0 < S.card := Finset.card_pos.mpr ⟨P, hPS⟩
          have hTcard : 0 < T.card := Finset.card_pos.mpr ⟨P, hPT⟩
          rw [Finset.card_erase_of_mem hPS, Finset.card_erase_of_mem hPT, ← hcard]
          omega
        have herase := ih _ hlt (S.erase P) (T.erase P) hSerase hTerase hcrossErase rfl
        calc
          S = insert P (S.erase P) := (Finset.insert_erase hPS).symm
          _ = insert P (T.erase P) := by rw [herase]
          _ = T := Finset.insert_erase hPT
      · have hempty : S ∪ T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        have hSempty : S = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro q hq
          have : q ∈ S ∪ T := Finset.mem_union_left T hq
          rw [hempty] at this
          exact Finset.notMem_empty q this
        have hTempty : T = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro q hq
          have : q ∈ S ∪ T := Finset.mem_union_right S hq
          rw [hempty] at this
          exact Finset.notMem_empty q this
        exact hSempty.trans hTempty.symm

/-- Equality of the reduced totient ratios forces equality of prime supports.
@isnad1 id=eq.3h2v.s5.6e7b0bb8093e from=translated src=- shape=e3719d49 vocab=42ba4790
-/
theorem primeSupport_eq_of_totient_cross_eq {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcross : a.totient * b = b.totient * a) :
    primeSupport a = primeSupport b := by
  apply primeFinset_eq_of_euler_products_cross_eq
  · intro q hq
    exact Nat.prime_of_mem_primeFactors hq
  · intro q hq
    exact Nat.prime_of_mem_primeFactors hq
  · exact euler_products_cross_eq_of_totient_cross_eq ha hb hcross

/-- The normalized coefficient multiplying the first provider in the fixed-cofactor equation.-/
def normalizedA (m₁ m₂ : ℕ) : ℕ :=
  m₂.totient / Nat.gcd m₁.totient m₂.totient

/-- The normalized coefficient multiplying the second provider in the fixed-cofactor equation.-/
def normalizedB (m₁ m₂ : ℕ) : ℕ :=
  m₁.totient / Nat.gcd m₁.totient m₂.totient

/-- The normalized coefficients are coprime for positive cofactors.
@isnad1 id=coprime.2h2v.s4.0fa71d9b476f from=translated src=- shape=4c218ca2 vocab=258521a3
-/
theorem normalizedA_coprime_normalizedB {m₁ m₂ : ℕ} (hm₁ : 0 < m₁) (_hm₂ : 0 < m₂) :
    (normalizedA m₁ m₂).Coprime (normalizedB m₁ m₂) := by
  have htot₁ : 0 < m₁.totient := Nat.totient_pos.mpr hm₁
  have hg : 0 < Nat.gcd m₁.totient m₂.totient :=
    Nat.gcd_pos_of_pos_left _ htot₁
  exact (Nat.coprime_div_gcd_div_gcd hg).symm

/-- A balance relation has a unique primitive direction: its two multipliers are a common multiple of the normalized coefficients `a` and `b`.
@isnad1 id=ex.3h4v.s6.759a374610ff from=translated src=- shape=3be8f18a vocab=cf3983b3
-/
theorem exists_normalized_common_multiplier {m₁ m₂ k₁ k₂ : ℕ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hbalance : k₁ * m₁.totient = k₂ * m₂.totient) :
    ∃ c, k₁ = normalizedA m₁ m₂ * c ∧
      k₂ = normalizedB m₁ m₂ * c := by
  let g := Nat.gcd m₁.totient m₂.totient
  let a := normalizedA m₁ m₂
  let b := normalizedB m₁ m₂
  have htot₁ : 0 < m₁.totient := Nat.totient_pos.mpr hm₁
  have htot₂ : 0 < m₂.totient := Nat.totient_pos.mpr hm₂
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ htot₁
  have ha : 0 < a := by
    exact Nat.div_pos (Nat.gcd_le_right _ htot₂) hg
  have hb : 0 < b := by
    exact Nat.div_pos (Nat.gcd_le_left _ htot₁) hg
  have htot₁_eq : m₁.totient = b * g := by
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left m₁.totient m₂.totient)).symm
  have htot₂_eq : m₂.totient = a * g := by
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_right m₁.totient m₂.totient)).symm
  have hab : a.Coprime b := normalizedA_coprime_normalizedB hm₁ hm₂
  have hprimitive : k₁ * b = k₂ * a := by
    apply (mul_right_inj' hg.ne').mp
    calc
      g * (k₁ * b) = k₁ * m₁.totient := by rw [htot₁_eq]; ac_rfl
      _ = k₂ * m₂.totient := hbalance
      _ = g * (k₂ * a) := by rw [htot₂_eq]; ac_rfl
  have hak₁ : a ∣ k₁ := by
    apply hab.dvd_of_dvd_mul_right
    exact ⟨k₂, hprimitive.trans (Nat.mul_comm _ _)⟩
  let c := k₁ / a
  have hk₁ : k₁ = a * c := by
    rw [mul_comm]
    exact (Nat.div_mul_cancel hak₁).symm
  have hk₂ : k₂ = b * c := by
    apply (mul_right_inj' ha.ne').mp
    calc
      a * k₂ = k₂ * a := Nat.mul_comm _ _
      _ = k₁ * b := hprimitive.symm
      _ = a * (b * c) := by rw [hk₁]; ac_rfl
  exact ⟨c, hk₁, hk₂⟩

/-- The first cofactor in a large-prime skeleton is positive.
@isnad1 id=lt.0h4v.s4.b036b956f2ac from=translated src=- shape=710851aa vocab=01002611
-/
theorem LargePrimeSkeleton.m1_pos {h n p : ℕ} (s : LargePrimeSkeleton h n p) :
    0 < s.m1 := by
  apply Nat.pos_of_ne_zero
  intro hm
  apply s.q1_not_dvd_m1
  rw [hm]
  exact dvd_zero s.q1

/-- The second cofactor in a large-prime skeleton is positive.
@isnad1 id=lt.0h4v.s4.bb26ab494413 from=translated src=- shape=710851aa vocab=dd8ba735
-/
theorem LargePrimeSkeleton.m2_pos {h n p : ℕ} (s : LargePrimeSkeleton h n p) :
    0 < s.m2 := by
  apply Nat.pos_of_ne_zero
  intro hm
  apply s.q2_not_dvd_m2
  rw [hm]
  exact dvd_zero s.q2

/-- The paper's normalized `a,b,c` decomposition for a large-prime skeleton.
@isnad1 id=ex.0h4v.s6.1d358afd15e0 from=translated src=- shape=6c28373c vocab=9a531895
-/
theorem LargePrimeSkeleton.exists_normalized_common_multiplier {h n p : ℕ}
    (s : LargePrimeSkeleton h n p) :
    ∃ c, s.k1 = normalizedA s.m1 s.m2 * c ∧
      s.k2 = normalizedB s.m1 s.m2 * c :=
  RankAmplification.exists_normalized_common_multiplier s.m1_pos s.m2_pos s.balance

/-- In a skeleton the common multiplier `c` in the normalized decomposition is positive.
@isnad1 id=ex.0h4v.s6.c021179144aa from=translated src=- shape=142a1871 vocab=67ef32f6
-/
theorem LargePrimeSkeleton.exists_pos_normalized_common_multiplier {h n p : ℕ}
    (s : LargePrimeSkeleton h n p) :
    ∃ c, 0 < c ∧ s.k1 = normalizedA s.m1 s.m2 * c ∧
      s.k2 = normalizedB s.m1 s.m2 * c := by
  obtain ⟨c, hk₁, hk₂⟩ := s.exists_normalized_common_multiplier
  have hc : 0 < c := by
    by_contra hc
    have hc₀ : c = 0 := Nat.eq_zero_of_not_pos hc
    rw [hc₀, Nat.mul_zero] at hk₁
    exact s.k1_pos.ne' hk₁
  exact ⟨c, hc, hk₁, hk₂⟩

/-- Substituting the normalized decomposition into the two cofactor factorizations gives the paper's affine equation (3.4), in subtraction-free form.
@isnad1 id=eq.2h5v.s7.930114573a2f from=translated src=- shape=be7444b9 vocab=1404522c
-/
theorem LargePrimeSkeleton.normalized_shift_equation {h n p : ℕ}
    (s : LargePrimeSkeleton h n p) {c : ℕ}
    (hk₁ : s.k1 = normalizedA s.m1 s.m2 * c)
    (hk₂ : s.k2 = normalizedB s.m1 s.m2 * c) :
    s.m1 * (normalizedA s.m1 s.m2 * (c * p) + 1) + h =
      s.m2 * (normalizedB s.m1 s.m2 * (c * p) + 1) := by
  calc
    s.m1 * (normalizedA s.m1 s.m2 * (c * p) + 1) + h =
        s.m1 * s.q1 + h := by rw [s.q1_eq, hk₁]; ring
    _ = n + h := congrArg (fun x : ℕ ↦ x + h) s.n_eq.symm
    _ = s.m2 * s.q2 := s.shifted_eq
    _ = s.m2 * (normalizedB s.m1 s.m2 * (c * p) + 1) := by
      rw [s.q2_eq, hk₂]
      ring

/-- A vanishing normalized slope would force equality of the two reduced totient ratios.
@isnad1 id=eq.1h2v.s5.62a7f6e5aa39 from=translated src=- shape=be382476 vocab=9f996b75
-/
theorem totient_cross_eq_of_normalized_diagonal {m₁ m₂ : ℕ}
    (hdiag : m₁ * normalizedA m₁ m₂ = m₂ * normalizedB m₁ m₂) :
    m₁.totient * m₂ = m₂.totient * m₁ := by
  let g := Nat.gcd m₁.totient m₂.totient
  have htot₁ : m₁.totient = normalizedB m₁ m₂ * g := by
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left m₁.totient m₂.totient)).symm
  have htot₂ : m₂.totient = normalizedA m₁ m₂ * g := by
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_right m₁.totient m₂.totient)).symm
  calc
    m₁.totient * m₂ = (m₂ * normalizedB m₁ m₂) * g := by
      rw [htot₁]
      ac_rfl
    _ = (m₁ * normalizedA m₁ m₂) * g := by rw [hdiag]
    _ = m₂.totient * m₁ := by rw [htot₂]; ac_rfl

/-- For an odd shift, the normalized slope in (3.5) cannot vanish.
@isnad1 id=ne.1h4v.s6.f6cec0044fdb from=translated src=- shape=c4fb6482 vocab=2e6c83ed
-/
theorem LargePrimeSkeleton.normalized_slopes_ne {h n p : ℕ} (hodd : Odd h)
    (s : LargePrimeSkeleton h n p) :
    s.m1 * normalizedA s.m1 s.m2 ≠ s.m2 * normalizedB s.m1 s.m2 := by
  intro hdiag
  obtain ⟨c, _hc, hk₁, hk₂⟩ := s.exists_pos_normalized_common_multiplier
  have hshift := s.normalized_shift_equation hk₁ hk₂
  have hshiftExpanded :
      (s.m1 * normalizedA s.m1 s.m2) * (c * p) + (s.m1 + h) =
        (s.m2 * normalizedB s.m1 s.m2) * (c * p) + s.m2 := by
    calc
      (s.m1 * normalizedA s.m1 s.m2) * (c * p) + (s.m1 + h) =
          s.m1 * (normalizedA s.m1 s.m2 * (c * p) + 1) + h := by ring
      _ = s.m2 * (normalizedB s.m1 s.m2 * (c * p) + 1) := hshift
      _ = (s.m2 * normalizedB s.m1 s.m2) * (c * p) + s.m2 := by ring
  rw [hdiag] at hshiftExpanded
  have hm₂eq : s.m2 = s.m1 + h := (Nat.add_left_cancel hshiftExpanded).symm
  have htotcross := totient_cross_eq_of_normalized_diagonal hdiag
  have hsupport : primeSupport s.m1 = primeSupport s.m2 :=
    primeSupport_eq_of_totient_cross_eq s.m1_pos.ne' s.m2_pos.ne' htotcross
  apply not_isSameSupportIndex_of_odd hodd
  refine ⟨s.m1_pos, ?_⟩
  rw [← hm₂eq]
  exact hsupport

/-- A nonconstant integral affine equation has at most one natural-number parameter.
@isnad1 id=eq.3h6v.s6.d803787c44c3 from=translated src=- shape=f2bb5fb4 vocab=5c386ba3
-/
theorem affine_parameter_unique {A B L R C D : ℕ} (hAB : A ≠ B)
    (hC : A * C + L = B * C + R) (hD : A * D + L = B * D + R) :
    C = D := by
  have hCℤ : (A : ℤ) * C + L = (B : ℤ) * C + R := by exact_mod_cast hC
  have hDℤ : (A : ℤ) * D + L = (B : ℤ) * D + R := by exact_mod_cast hD
  have hproduct : ((A : ℤ) - B) * ((C : ℤ) - D) = 0 := by
    calc
      ((A : ℤ) - B) * ((C : ℤ) - D) =
          ((A : ℤ) * C + L - ((B : ℤ) * C + R)) -
            ((A : ℤ) * D + L - ((B : ℤ) * D + R)) := by ring
      _ = 0 := by rw [hCℤ, hDℤ]; ring
  rcases mul_eq_zero.mp hproduct with hcoeff | hparam
  · have hcast : (A : ℤ) = B := sub_eq_zero.mp hcoeff
    have : A = B := by exact_mod_cast hcast
    exact (hAB this).elim
  · have hcast : (C : ℤ) = D := sub_eq_zero.mp hparam
    exact_mod_cast hcast

/-- **Paper Lemma 3.3.** For an odd shift, two large-prime skeletons carrying the same ordered cofactor pair determine the same integer `n`.
@isnad1 id=eq.3h7v.s5.65695ab1df6a from=translated src=- shape=3054197d vocab=e9dcc2b0
-/
theorem LargePrimeSkeleton.n_eq_of_same_cofactors {h n p n' p' : ℕ} (hodd : Odd h)
    (s : LargePrimeSkeleton h n p) (t : LargePrimeSkeleton h n' p')
    (hm₁ : s.m1 = t.m1) (hm₂ : s.m2 = t.m2) :
    n = n' := by
  obtain ⟨c, _hc, hsk₁, hsk₂⟩ := s.exists_pos_normalized_common_multiplier
  obtain ⟨d, _hd, htk₁, htk₂⟩ := t.exists_pos_normalized_common_multiplier
  let C := c * p
  let D := d * p'
  have hsShift := s.normalized_shift_equation hsk₁ hsk₂
  have htShift := t.normalized_shift_equation htk₁ htk₂
  have hsLinear :
      (s.m1 * normalizedA s.m1 s.m2) * C + (s.m1 + h) =
        (s.m2 * normalizedB s.m1 s.m2) * C + s.m2 := by
    calc
      (s.m1 * normalizedA s.m1 s.m2) * C + (s.m1 + h) =
          s.m1 * (normalizedA s.m1 s.m2 * (c * p) + 1) + h := by
            simp only [C]
            ring
      _ = s.m2 * (normalizedB s.m1 s.m2 * (c * p) + 1) := hsShift
      _ = (s.m2 * normalizedB s.m1 s.m2) * C + s.m2 := by
        simp only [C]
        ring
  have htLinear :
      (t.m1 * normalizedA t.m1 t.m2) * D + (t.m1 + h) =
        (t.m2 * normalizedB t.m1 t.m2) * D + t.m2 := by
    calc
      (t.m1 * normalizedA t.m1 t.m2) * D + (t.m1 + h) =
          t.m1 * (normalizedA t.m1 t.m2 * (d * p') + 1) + h := by
            simp only [D]
            ring
      _ = t.m2 * (normalizedB t.m1 t.m2 * (d * p') + 1) := htShift
      _ = (t.m2 * normalizedB t.m1 t.m2) * D + t.m2 := by
        simp only [D]
        ring
  have htLinear' :
      (s.m1 * normalizedA s.m1 s.m2) * D + (s.m1 + h) =
        (s.m2 * normalizedB s.m1 s.m2) * D + s.m2 := by
    simpa only [hm₁, hm₂] using htLinear
  have hCD : C = D := affine_parameter_unique (s.normalized_slopes_ne hodd) hsLinear htLinear'
  have hnS : n = s.m1 * (normalizedA s.m1 s.m2 * C + 1) := by
    calc
      n = s.m1 * s.q1 := s.n_eq
      _ = s.m1 * (normalizedA s.m1 s.m2 * C + 1) := by
        rw [s.q1_eq, hsk₁]
        simp only [C]
        ring
  have hnT : n' = t.m1 * (normalizedA t.m1 t.m2 * D + 1) := by
    calc
      n' = t.m1 * t.q1 := t.n_eq
      _ = t.m1 * (normalizedA t.m1 t.m2 * D + 1) := by
        rw [t.q1_eq, htk₁]
        simp only [D]
        ring
  calc
    n = s.m1 * (normalizedA s.m1 s.m2 * C + 1) := hnS
    _ = s.m1 * (normalizedA s.m1 s.m2 * D + 1) := by rw [hCD]
    _ = t.m1 * (normalizedA t.m1 t.m2 * D + 1) := by rw [hm₁, hm₂]
    _ = n' := hnT.symm

/-- The natural numbers admitting a skeleton with a prescribed ordered cofactor pair.-/
def fixedCofactorSkeletonNumbers (h m₁ m₂ : ℕ) : Set ℕ :=
  {n | ∃ p, ∃ s : LargePrimeSkeleton h n p, s.m1 = m₁ ∧ s.m2 = m₂}

/-- Set-theoretic fixed-fiber form of Lemma 3.3: every prescribed cofactor fiber has at most one natural number in it.
@isnad1 id=subsingl.1h3v.s4.f392e6820261 from=translated src=- shape=9bab1ada vocab=deadf4a3
-/
theorem fixedCofactorSkeletonNumbers_subsingleton {h : ℕ} (hodd : Odd h) (m₁ m₂ : ℕ) :
    (fixedCofactorSkeletonNumbers h m₁ m₂).Subsingleton := by
  intro n hn n' hn'
  obtain ⟨p, s, hs₁, hs₂⟩ := hn
  obtain ⟨p', t, ht₁, ht₂⟩ := hn'
  apply s.n_eq_of_same_cofactors hodd t
  · exact hs₁.trans ht₁.symm
  · exact hs₂.trans ht₂.symm

/-- Injection foundation for Corollary 3.4.
@isnad1 id=injectiv.1h4v.s7.1b5f0232d47e from=translated src=- shape=78af0160 vocab=1780175e
-/
theorem cofactorPair_injective_on_skeletonNumbers {h : ℕ} (hodd : Odd h) (S : Finset ℕ)
    (provider : (x : {n // n ∈ S}) → ℕ)
    (skeleton : (x : {n // n ∈ S}) → LargePrimeSkeleton h x.1 (provider x)) :
    Function.Injective (fun x ↦ ((skeleton x).m1, (skeleton x).m2)) := by
  intro x y hpair
  apply Subtype.ext
  apply (skeleton x).n_eq_of_same_cofactors hodd (skeleton y)
  · exact congrArg Prod.fst hpair
  · exact congrArg Prod.snd hpair

/-- Finite cardinal form of the cofactor-pair injection: choosing one skeleton for each member of `S` produces exactly `|S|` distinct ordered pairs.
@isnad1 id=eq.1h4v.s7.38578f5c9892 from=translated src=- shape=4f69fe18 vocab=341b72b4
-/
theorem card_cofactorPair_image_eq {h : ℕ} (hodd : Odd h) (S : Finset ℕ)
    (provider : (x : {n // n ∈ S}) → ℕ)
    (skeleton : (x : {n // n ∈ S}) → LargePrimeSkeleton h x.1 (provider x)) :
    (S.attach.image (fun x ↦ ((skeleton x).m1, (skeleton x).m2))).card = S.card := by
  rw [Finset.card_image_of_injective _
    (cofactorPair_injective_on_skeletonNumbers hodd S provider skeleton)]
  exact Finset.card_attach

end RankAmplification

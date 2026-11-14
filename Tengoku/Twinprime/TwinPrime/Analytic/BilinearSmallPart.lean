import Tengoku.Twinprime.TwinPrime.Analytic.BilinearSign
import Tengoku.Twinprime.TwinPrime.Analytic.TruncatedMangoldt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact cancellation from a bounded nontrivial small-prime part

If 1 < a ≤ U and every prime divisor of the positive integer b exceeds U,
the complete signed coefficient (μ_{>U} * β_U)(a*b) vanishes. The factors
need not be squarefree. These are grouped coefficient identities; they do
not discard individual positive or negative divisor contributions.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TwinPrime.Analytic

theorem coprime_small_rough (U a b : ℕ) (ha : 0 < a) (haU : a ≤ U)
    (hrough : ∀ p, Nat.Prime p → p ∣ b → U < p) : a.Coprime b := by
  apply Nat.coprime_of_dvd
  intro p hp hpa hpb
  have hpU := (Nat.le_of_dvd ha hpa).trans haU
  exact (not_lt_of_ge hpU) (hrough p hp hpb)

/-- A divisor below the cutoff cannot acquire any prime factor from the rough part.-/
theorem small_divisor_mul_dvd_left_of_rough (U a b d : ℕ)
    (hd : 0 < d) (hdU : d ≤ U)
    (hrough : ∀ p, Nat.Prime p → p ∣ b → U < p) (hdvd : d ∣ a * b) :
    d ∣ a :=
  (coprime_small_rough U d b hd hdU hrough).dvd_of_dvd_mul_right hdvd

theorem vaughanBeta_eq_sum_primePow (U n : ℕ) :
    vaughanBeta U n =
      ∑ d ∈ n.divisors with IsPrimePow d, if U < d then vonMangoldt d else 0 := by
  rw [vaughanBeta_apply, sum_filter]
  apply sum_congr rfl
  intro d _
  by_cases hd : IsPrimePow d
  · simp [hd]
  · simp [hd, vonMangoldt_eq_zero_iff.mpr hd]

/-- The cutoff divisor weight is additive on coprime products, with no
restriction on prime-power multiplicities.-/
theorem vaughanBeta_mul_of_coprime (U : ℕ) {a b : ℕ} (hab : a.Coprime b) :
    vaughanBeta U (a * b) = vaughanBeta U a + vaughanBeta U b := by
  rw [vaughanBeta_eq_sum_primePow, Nat.mul_divisors_filter_prime_pow hab,
    filter_union, sum_union (Nat.disjoint_divisors_filter_isPrimePow hab),
    ← vaughanBeta_eq_sum_primePow, ← vaughanBeta_eq_sum_primePow]

theorem vaughanBeta_mul_small_rough (U a b : ℕ) (ha : 0 < a) (haU : a ≤ U)
    (hrough : ∀ p, Nat.Prime p → p ∣ b → U < p) :
    vaughanBeta U (a * b) = Real.log b := by
  rw [vaughanBeta_mul_of_coprime U (coprime_small_rough U a b ha haU hrough),
    vaughanBeta_eq_zero_of_le U a haU,
    vaughanBeta_eq_log_of_small_divisors U b
      (small_divisors_eq_one_of_prime_divisors_gt U b hrough), zero_add]

/-- The low Möbius convolution factors through the complete divisor sum of
the bounded small part.-/
theorem moebiusLow_mul_beta_small_rough (U a b : ℕ) (ha : 0 < a)
    (haU : a ≤ U) (hb : 0 < b)
    (hrough : ∀ p, Nat.Prime p → p ∣ b → U < p) :
    (moebiusLow U * vaughanBeta U) (a * b) =
      (∑ d ∈ a.divisors, (μ d : ℝ)) * Real.log b := by
  rw [mul_apply,
    Nat.sum_divisorsAntidiagonal
      (fun d r => moebiusLow U d * vaughanBeta U r)]
  have hsub : a.divisors ⊆ (a * b).divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr
      ⟨dvd_mul_of_dvd_left (Nat.dvd_of_mem_divisors hd) b, Nat.ne_of_gt (Nat.mul_pos ha hb)⟩
  have hrestrict :
      (∑ d ∈ (a * b).divisors, moebiusLow U d * vaughanBeta U (a * b / d)) =
        ∑ d ∈ a.divisors, moebiusLow U d * vaughanBeta U (a * b / d) := by
    symm
    apply sum_subset hsub
    intro d hd hda
    have hnot : ¬d ≤ U := by
      intro hdU
      apply hda
      exact Nat.mem_divisors.mpr
        ⟨small_divisor_mul_dvd_left_of_rough U a b d (Nat.pos_of_mem_divisors hd)
          hdU hrough (Nat.dvd_of_mem_divisors hd), ha.ne'⟩
    simp [moebiusLow, cutoffLow_apply, hnot]
  rw [hrestrict, sum_mul]
  apply sum_congr rfl
  intro d hd
  have hda := Nat.dvd_of_mem_divisors hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have hda_le := Nat.le_of_dvd ha hda
  have hquot : a * b / d = a / d * b := by
    obtain ⟨k, rfl⟩ := hda
    simp [Nat.mul_div_cancel_left _ hdpos, mul_assoc]
  rw [moebiusLow, cutoffLow_apply, ite_eq_left (hda_le.trans haU), hquot,
    vaughanBeta_mul_small_rough U (a / d) b (Nat.div_pos hda_le hdpos)
      ((Nat.div_le_self a d).trans haU) hrough]
  rfl

theorem mangoldtHigh_mul_small_rough (U a b : ℕ) (ha : 1 < a)
    (haU : a ≤ U) (hb : 0 < b)
    (hrough : ∀ p, Nat.Prime p → p ∣ b → U < p) :
    mangoldtHigh U (a * b) = 0 := by
  by_cases hb1 : b = 1
  · simp [hb1, mangoldtHigh, cutoffHigh_apply, Nat.not_lt.mpr haU]
  have hab := coprime_small_rough U a b (lt_trans Nat.zero_lt_one ha) haU hrough
  have hnot : ¬IsPrimePow (a * b) := by
    intro hpow
    rcases (hab.isPrimePow_dvd_mul hpow).mp (dvd_refl (a * b)) with h | h
    · have hle := Nat.le_of_dvd (lt_trans Nat.zero_lt_one ha) h
      have hb2 : 2 ≤ b := by omega
      nlinarith
    · have hle := Nat.le_of_dvd hb h
      nlinarith
  simp [mangoldtHigh, cutoffHigh_apply, vonMangoldt_eq_zero_iff.mpr hnot]

/-- A nontrivial small part of size at most the common cutoff forces exact
grouped cancellation, including repeated prime factors and the case b = 1.-/
theorem vaughanBilinear_eq_zero_of_small_part (U a b : ℕ) (ha : 1 < a)
    (haU : a ≤ U) (hb : 0 < b)
    (hrough : ∀ p, Nat.Prime p → p ∣ b → U < p) :
    (moebiusHigh U * vaughanBeta U) (a * b) = 0 := by
  have hmu : (∑ d ∈ a.divisors, (μ d : ℝ)) = 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℝ => f a)
      (coe_moebius_mul_coe_zeta (R := ℝ))
    simpa only [coe_mul_zeta_apply, one_apply_ne (Nat.ne_of_gt ha), intCoe_apply] using h
  have hlow : (moebiusLow U * vaughanBeta U) (a * b) = 0 := by
    rw [moebiusLow_mul_beta_small_rough U a b (lt_trans Nat.zero_lt_one ha)
      haU hb hrough, hmu, zero_mul]
  have hfull : (μ : ArithmeticFunction ℝ) * vaughanBeta U = mangoldtHigh U := by
    rw [vaughanBeta]
    calc
      _ = mangoldtHigh U * ((μ : ArithmeticFunction ℝ) * ζ) := by ring
      _ = _ := by rw [coe_moebius_mul_coe_zeta, mul_one]
  have hsum := congrArg (fun f : ArithmeticFunction ℝ => (f * vaughanBeta U) (a * b))
    (cutoffLow_add_cutoffHigh (μ : ArithmeticFunction ℝ) U)
  change ((moebiusLow U + moebiusHigh U) * vaughanBeta U) (a * b) = _ at hsum
  rw [add_mul, ArithmeticFunction.add_apply, hlow, zero_add, hfull,
    mangoldtHigh_mul_small_rough U a b ha haU hb hrough] at hsum
  exact hsum

/-- With a rough right factor, every low divisor comes entirely from the
left factor. The test function can retain arbitrary signed coefficients.-/
theorem moebiusLow_mul_apply_mul_rough (U a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hrough : ∀ p, Nat.Prime p → p ∣ b → U < p) (g : ArithmeticFunction ℝ) :
    (moebiusLow U * g) (a * b) =
      ∑ d ∈ a.divisors with d ≤ U, (μ d : ℝ) * g (a / d * b) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun d r => moebiusLow U d * g r)]
  have hsub : a.divisors ⊆ (a * b).divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr
      ⟨dvd_mul_of_dvd_left (Nat.dvd_of_mem_divisors hd) b, (Nat.mul_pos ha hb).ne'⟩
  have hrestrict :
      (∑ d ∈ (a * b).divisors, moebiusLow U d * g (a * b / d)) =
        ∑ d ∈ a.divisors, moebiusLow U d * g (a * b / d) := by
    symm
    apply sum_subset hsub
    intro d hd hda
    have hnot : ¬d ≤ U := by
      intro hdU
      apply hda
      exact Nat.mem_divisors.mpr
        ⟨small_divisor_mul_dvd_left_of_rough U a b d (Nat.pos_of_mem_divisors hd)
          hdU hrough (Nat.dvd_of_mem_divisors hd), ha.ne'⟩
    simp [moebiusLow, cutoffLow_apply, hnot]
  rw [hrestrict, sum_filter]
  apply sum_congr rfl
  intro d hd
  have hquot : a * b / d = a / d * b := by
    obtain ⟨k, rfl⟩ := Nat.dvd_of_mem_divisors hd
    simp [Nat.mul_div_cancel_left _ (Nat.pos_of_mem_divisors hd), mul_assoc]
  by_cases hdU : d ≤ U
  · simp only [moebiusLow, cutoffLow_apply, ite_eq_left hdU, hquot, intCoe_apply]
  · simp [moebiusLow, cutoffLow_apply, hdU]

theorem coprime_smooth_rough (U a b : ℕ)
    (hsmooth : ∀ p, Nat.Prime p → p ∣ a → p ≤ U)
    (hrough : ∀ p, Nat.Prime p → p ∣ b → U < p) : a.Coprime b := by
  apply Nat.coprime_of_dvd
  intro p hp hpa hpb
  exact (not_lt_of_ge (hsmooth p hp hpa)) (hrough p hp hpb)

/-- A squarefree smooth integer has no prime-power divisor above the cutoff.-/
theorem vaughanBeta_eq_zero_of_squarefree_smooth (U a : ℕ) (ha : Squarefree a)
    (hsmooth : ∀ p, Nat.Prime p → p ∣ a → p ≤ U) :
    vaughanBeta U a = 0 := by
  rw [vaughanBeta_eq_sum_primePow]
  apply sum_eq_zero
  intro d hd
  obtain ⟨hd, hpow⟩ := mem_filter.mp hd
  have hda := Nat.dvd_of_mem_divisors hd
  have hp := Nat.squarefree_and_prime_pow_iff_prime.mp
    ⟨ha.squarefree_of_dvd hda, hpow⟩
  simp [Nat.not_lt.mpr (hsmooth d hp hda)]

theorem vaughanBeta_mul_squarefree_smooth_rough (U a b : ℕ) (ha : Squarefree a)
    (hsmooth : ∀ p, Nat.Prime p → p ∣ a → p ≤ U)
    (hrough : ∀ p, Nat.Prime p → p ∣ b → U < p) :
    vaughanBeta U (a * b) = Real.log b := by
  rw [vaughanBeta_mul_of_coprime U (coprime_smooth_rough U a b hsmooth hrough),
    vaughanBeta_eq_zero_of_squarefree_smooth U a ha hsmooth,
    vaughanBeta_eq_log_of_small_divisors U b
      (small_divisors_eq_one_of_prime_divisors_gt U b hrough), zero_add]

theorem moebiusLow_mul_beta_squarefree_smooth_rough (U a b : ℕ) (ha : Squarefree a)
    (hb : 0 < b) (hsmooth : ∀ p, Nat.Prime p → p ∣ a → p ≤ U)
    (hrough : ∀ p, Nat.Prime p → p ∣ b → U < p) :
    (moebiusLow U * vaughanBeta U) (a * b) =
      truncatedMoebiusSum U a * Real.log b := by
  rw [moebiusLow_mul_apply_mul_rough U a b (Nat.pos_of_ne_zero ha.ne_zero) hb hrough,
    truncatedMoebiusSum, sum_mul]
  apply sum_congr rfl
  intro d hd
  have hda := Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)
  rw [vaughanBeta_mul_squarefree_smooth_rough U (a / d) b (ha.squarefree_of_dvd hda)
    (fun p hp hpd => hsmooth p hp (hpd.trans hda)) hrough]

/-- The smooth part may exceed U and the rough part may have repeated factors.
The truncated Möbius sum retains its sign.-/
theorem vaughanBilinear_eq_mangoldtHigh_sub_of_squarefree_smooth_rough
    (U a b : ℕ) (ha : Squarefree a) (hb : 0 < b)
    (hsmooth : ∀ p, Nat.Prime p → p ∣ a → p ≤ U)
    (hrough : ∀ p, Nat.Prime p → p ∣ b → U < p) :
    (moebiusHigh U * vaughanBeta U) (a * b) =
      mangoldtHigh U (a * b) - truncatedMoebiusSum U a * Real.log b := by
  have hfull : (μ : ArithmeticFunction ℝ) * vaughanBeta U = mangoldtHigh U := by
    rw [vaughanBeta]
    calc
      _ = mangoldtHigh U * ((μ : ArithmeticFunction ℝ) * ζ) := by ring
      _ = _ := by rw [coe_moebius_mul_coe_zeta, mul_one]
  have hsum := congrArg (fun f : ArithmeticFunction ℝ => (f * vaughanBeta U) (a * b))
    (cutoffLow_add_cutoffHigh (μ : ArithmeticFunction ℝ) U)
  change ((moebiusLow U + moebiusHigh U) * vaughanBeta U) (a * b) = _ at hsum
  rw [add_mul, ArithmeticFunction.add_apply, hfull,
    moebiusLow_mul_beta_squarefree_smooth_rough U a b ha hb hsmooth hrough] at hsum
  linarith

theorem vaughanBilinear_eq_mangoldt_sub_of_squarefree_smooth_rough
    (U a b : ℕ) (ha : Squarefree a) (hb : 0 < b) (hn : U < a * b)
    (hsmooth : ∀ p, Nat.Prime p → p ∣ a → p ≤ U)
    (hrough : ∀ p, Nat.Prime p → p ∣ b → U < p) :
    (moebiusHigh U * vaughanBeta U) (a * b) =
      vonMangoldt (a * b) - truncatedMoebiusSum U a * Real.log b := by
  rw [vaughanBilinear_eq_mangoldtHigh_sub_of_squarefree_smooth_rough
    U a b ha hb hsmooth hrough, mangoldtHigh, cutoffHigh_apply, ite_eq_left hn]

theorem truncatedMoebiusSum_two_primes (U p q : ℕ) (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hpq : p ≠ q) (hpU : p ≤ U) (hqU : q ≤ U)
    (hU : U < p * q) : truncatedMoebiusSum U (p * q) = -1 := by
  have hfilter : {d ∈ (p * q).divisors | d ≤ U} = {1, p, q} := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨hd, _⟩, hdU⟩
      obtain ⟨e, f, he, hf, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd
      rcases (Nat.dvd_prime hp).mp he with rfl | rfl <;>
        rcases (Nat.dvd_prime hq).mp hf with rfl | rfl <;>
        simp_all [Nat.not_le.mpr hU]
    · intro hd
      rcases hd with rfl | rfl | rfl
      · exact ⟨⟨one_dvd _, Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩, hp.one_le.trans hpU⟩
      · exact ⟨⟨dvd_mul_right _ _, Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩, hpU⟩
      · exact ⟨⟨dvd_mul_left _ _, Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩, hqU⟩
  rw [truncatedMoebiusSum, hfilter]
  simp [hp.ne_one.symm, hq.ne_one.symm, hpq,
    moebius_apply_prime hp, moebius_apply_prime hq]

/-- Two distinct small primes whose product exceeds the cutoff give a
positive logarithmic coefficient when multiplied by any positive rough part.
The rough factor may have repeated primes; at b = 1 the coefficient is zero.-/
theorem vaughanBilinear_eq_log_of_two_small_primes (U p q b : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hpU : p ≤ U) (hqU : q ≤ U) (hU : U < p * q) (hb : 0 < b)
    (hrough : ∀ r, Nat.Prime r → r ∣ b → U < r) :
    (moebiusHigh U * vaughanBeta U) (p * q * b) = Real.log b := by
  have hsf : Squarefree (p * q) :=
    Nat.squarefree_mul_iff.mpr ⟨(Nat.coprime_primes hp hq).mpr hpq, hp.squarefree, hq.squarefree⟩
  have hsmooth : ∀ r, Nat.Prime r → r ∣ p * q → r ≤ U := by
    intro r hr hrd
    rcases hr.dvd_or_dvd hrd with hrp | hrq
    · exact ((Nat.prime_dvd_prime_iff_eq hr hp).mp hrp) ▸ hpU
    · exact ((Nat.prime_dvd_prime_iff_eq hr hq).mp hrq) ▸ hqU
  have hnot : ¬IsPrimePow (p * q * b) := by
    intro hpow
    obtain ⟨r, _, huniq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
    have hpr := huniq p ⟨hp, dvd_mul_of_dvd_left (dvd_mul_right p q) b⟩
    have hqr := huniq q ⟨hq, dvd_mul_of_dvd_left (dvd_mul_left q p) b⟩
    exact hpq (hpr.trans hqr.symm)
  rw [vaughanBilinear_eq_mangoldtHigh_sub_of_squarefree_smooth_rough
      U (p * q) b hsf hb hsmooth hrough,
    truncatedMoebiusSum_two_primes U p q hp hq hpq hpU hqU hU]
  simp [mangoldtHigh, cutoffHigh_apply, vonMangoldt_eq_zero_iff.mpr hnot]

theorem vaughanBilinear_nonneg_of_two_small_primes (U p q b : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hpU : p ≤ U) (hqU : q ≤ U) (hU : U < p * q) (hb : 0 < b)
    (hrough : ∀ r, Nat.Prime r → r ∣ b → U < r) :
    0 ≤ (moebiusHigh U * vaughanBeta U) (p * q * b) := by
  rw [vaughanBilinear_eq_log_of_two_small_primes U p q b hp hq hpq hpU hqU hU hb hrough]
  exact Real.log_nonneg (by exact_mod_cast hb)

end TwinPrime.Analytic

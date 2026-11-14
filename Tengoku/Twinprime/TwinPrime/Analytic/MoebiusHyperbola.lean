import Tengoku.Twinprime.TwinPrime.Analytic.MoebiusSmoothing
import Tengoku.Twinprime.TwinPrime.Analytic.MoebiusAbel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Identifying the ordinary Möbius reciprocal limit by the hyperbola method

The exact identity `μ * ζ = 1` supplies the boundary constant by an elementary
finite argument. No absolute summability of `μ(n)/n` is used or asserted.
-/

noncomputable section

open Finset ArithmeticFunction Filter
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TwinPrime.Analytic

def moebiusSummatory (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, (μ n : ℝ)

theorem moebius_floor_sum (X : ℕ) (hX : 1 ≤ X) :
    (∑ n ∈ Ioc 0 X, (μ n : ℝ) * (X / n : ℕ)) = 1 := by
  have hμ : (μ : ArithmeticFunction ℝ) * ζ = 1 := coe_moebius_mul_coe_zeta
  have h := sum_Ioc_mul_zeta_eq_sum (μ : ArithmeticFunction ℝ) X
  rw [hμ] at h
  simpa [ArithmeticFunction.one_apply, hX] using h.symm

theorem moebiusSummatory_sub (a b : ℕ) (hab : a ≤ b) :
    moebiusSummatory b - moebiusSummatory a = ∑ n ∈ Ioc a b, (μ n : ℝ) := by
  unfold moebiusSummatory
  have h := sum_Ioc_consecutive (fun n => (μ n : ℝ)) (show 0 ≤ a from Nat.zero_le _) hab
  linarith

/-- An exact hyperbola split at the integer rectangle `N × K`.-/
theorem moebius_hyperbola (K N : ℕ) (hK : 1 ≤ K) (hN : 1 ≤ N) :
    (∑ d ∈ Ioc 0 N, (μ d : ℝ) * (K * N / d : ℕ)) +
      (∑ m ∈ Ioc 0 K, moebiusSummatory (K * N / m)) - K * moebiusSummatory N = 1 := by
  let X := K * N
  have hNX : N ≤ X := by dsimp [X]; nlinarith
  have htail : (∑ d ∈ Ioc N X, (μ d : ℝ) * (X / d : ℕ)) =
      ∑ m ∈ Ioc 0 K, (moebiusSummatory (X / m) - moebiusSummatory N) := by
    have he : ∀ d ∈ Ioc N X, (μ d : ℝ) * (X / d : ℕ) =
        ∑ m ∈ Ioc 0 K, if d * m ≤ X then (μ d : ℝ) else 0 := by
      intro d hd
      obtain ⟨hNd, hdX⟩ := mem_Ioc.mp hd
      have hd0 : 0 < d := by omega
      have hdiv : X / d ≤ K := by
        apply Nat.div_le_of_le_mul
        dsimp [X]
        nlinarith
      have hs : (Ioc 0 K).filter (fun m => d * m ≤ X) = Ioc 0 (X / d) := by
        ext m
        simp only [mem_filter, mem_Ioc]
        constructor
        · rintro ⟨⟨hm, _⟩, hdm⟩
          exact ⟨hm, (Nat.le_div_iff_mul_le hd0).mpr (by simpa [mul_comm] using hdm)⟩
        · rintro ⟨hm, hmD⟩
          exact ⟨⟨hm, hmD.trans hdiv⟩,
            by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd0).mp hmD⟩
      rw [← sum_filter, hs]
      simp [mul_comm]
    simp_rw [sum_congr rfl he]
    rw [sum_comm]
    apply sum_congr rfl
    intro m hm
    obtain ⟨hm0, hmK⟩ := mem_Ioc.mp hm
    have hNm : N ≤ X / m := by
      apply (Nat.le_div_iff_mul_le hm0).mpr
      dsimp [X]
      nlinarith
    rw [moebiusSummatory_sub N (X / m) hNm, ← sum_filter]
    congr 1
    ext d
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨hNd, _⟩, hdm⟩
      exact ⟨hNd, (Nat.le_div_iff_mul_le hm0).mpr hdm⟩
    · rintro ⟨hNd, hdM⟩
      exact ⟨⟨hNd, hdM.trans (Nat.div_le_self X m)⟩,
        (Nat.le_div_iff_mul_le hm0).mp hdM⟩
  have hsplit := sum_Ioc_consecutive (fun d => (μ d : ℝ) * (X / d : ℕ))
    (show 0 ≤ N from Nat.zero_le _) hNX
  rw [htail, moebius_floor_sum X (by dsimp [X]; nlinarith)] at hsplit
  simpa only [X, sum_sub_distrib, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul,
    add_sub_assoc] using hsplit

theorem abs_moebius_floor_error_le (K N : ℕ) :
    |(∑ d ∈ Ioc 0 N, (μ d : ℝ) * (K * N / d : ℕ)) -
      ((K : ℝ) * N) * normalizedMoebiusSum N| ≤ N := by
  unfold normalizedMoebiusSum
  rw [mul_sum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ Ioc 0 N, |(μ d : ℝ) * (K * N / d : ℕ) -
        ((K : ℝ) * N) * normalizedMoebius d| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Ioc 0 N, (1 : ℝ) := by
      apply sum_le_sum
      intro d hd
      have hd0 : 0 < d := (mem_Ioc.mp hd).1
      have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
      have hlow : (K * N / d : ℕ) * d ≤ K * N := Nat.div_mul_le_self _ _
      have hhigh : K * N < (K * N / d + 1) * d := by
        have := Nat.mod_lt (K * N) hd0
        have := Nat.mod_add_div (K * N) d
        nlinarith
      have hl : (K * N / d : ℕ) ≤ ((K : ℝ) * N) / d := by
        rw [le_div_iff₀ hdr]
        exact_mod_cast hlow
      have hh : ((K : ℝ) * N) / d < (K * N / d : ℕ) + 1 := by
        rw [div_lt_iff₀ hdr]
        exact_mod_cast hhigh
      have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := d))
      have heq : (μ d : ℝ) * (K * N / d : ℕ) - ((K : ℝ) * N) * normalizedMoebius d =
          (μ d : ℝ) * ((K * N / d : ℕ) - ((K : ℝ) * N) / d) := by
        rw [normalizedMoebius_apply]
        ring
      rw [heq, abs_mul, abs_of_nonpos (sub_nonpos.mpr hl)]
      nlinarith
    _ = _ := by simp

/-- The finite hyperbola estimate needs cancellation only on `[N,KN]`.-/
theorem normalizedMoebiusSum_le_of_mertens_range (K N : ℕ) (hK : 1 ≤ K) (hN : 1 ≤ N)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hM : ∀ t ∈ Icc N (K * N), |moebiusSummatory t| ≤ ε * t) :
    |normalizedMoebiusSum N| ≤ 2 / K + ε * (K + 1) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNX : N ≤ K * N := by nlinarith
  have hMN := hM N (mem_Icc.mpr ⟨le_rfl, hNX⟩)
  have hsum : |∑ m ∈ Ioc 0 K, moebiusSummatory (K * N / m)| ≤ ε * K * K * N := by
    calc
      _ ≤ ∑ m ∈ Ioc 0 K, |moebiusSummatory (K * N / m)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m ∈ Ioc 0 K, ε * (K * N : ℕ) := by
        apply sum_le_sum
        intro m hm
        obtain ⟨hm0, hmK⟩ := mem_Ioc.mp hm
        have hNm : N ≤ K * N / m := (Nat.le_div_iff_mul_le hm0).mpr (by nlinarith)
        exact (hM _ (mem_Icc.mpr ⟨hNm, Nat.div_le_self _ _⟩)).trans
          (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.div_le_self (K * N) m) hε)
      _ = _ := by simp; ring
  have hid := moebius_hyperbola K N hK hN
  let A : ℝ := ∑ d ∈ Ioc 0 N, (μ d : ℝ) * (K * N / d : ℕ)
  have hAb : |A| ≤ 1 + ε * K * K * N + K * (ε * N) := by
    have heq : A = 1 - (∑ m ∈ Ioc 0 K, moebiusSummatory (K * N / m)) +
        K * moebiusSummatory N := by dsimp [A]; linarith
    rw [heq]
    have ht := (abs_add_le (1 - ∑ m ∈ Ioc 0 K, moebiusSummatory (K * N / m))
      (K * moebiusSummatory N)).trans
        (add_le_add (abs_sub 1 (∑ m ∈ Ioc 0 K, moebiusSummatory (K * N / m))) le_rfl)
    rw [abs_one, abs_mul, abs_of_pos hKr] at ht
    exact ht.trans (by nlinarith [mul_le_mul_of_nonneg_left hMN hKr.le])
  have herr := abs_moebius_floor_error_le K N
  change |A - ((K : ℝ) * N) * normalizedMoebiusSum N| ≤ N at herr
  have ht := abs_add_le (((K : ℝ) * N) * normalizedMoebiusSum N - A) A
  rw [sub_add_cancel, abs_sub_comm _ A] at ht
  rw [abs_mul, abs_of_pos (mul_pos hKr hNr)] at ht
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hb : ((K : ℝ) * N) * |normalizedMoebiusSum N| ≤
      2 * N + ε * K * N * (K + 1) := by nlinarith
  apply (mul_le_mul_iff_right₀ (mul_pos hKr hNr)).mp
  calc
    _ ≤ 2 * N + ε * K * N * (K + 1) := hb
    _ = ((K : ℝ) * N) * (2 / K + ε * (K + 1)) := by field_simp

/-- Ordinary sublinear Möbius cancellation identifies the normalized limit as
zero by the exact hyperbola identity, without a Tauberian or absolute-sum assumption.-/
theorem tendsto_normalizedMoebiusSum_of_mertens_sublinear
    (hM : Tendsto (fun N : ℕ => moebiusSummatory N / N) atTop (nhds 0)) :
    Tendsto normalizedMoebiusSum atTop (nhds 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (4 / ε)
  have hKp : (0 : ℝ) < K := (div_pos (by norm_num) hε).trans hK
  have hK1 : 1 ≤ K := by exact_mod_cast hKp
  have hsmall : 2 / (K : ℝ) < ε / 2 := by
    have hh := (div_lt_iff₀ hε).mp hK
    rw [div_lt_iff₀ hKp]
    nlinarith
  let δ := ε / (4 * ((K : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hmabs : Tendsto (fun N : ℕ => |moebiusSummatory N / N|) atTop (nhds 0) := by
    simpa using hM.abs
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((hmabs.eventually (gt_mem_nhds hδ)).and (eventually_ge_atTop 1))
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hN1 := (hN₀ N hN).2
  have hr := normalizedMoebiusSum_le_of_mertens_range K N hK1 hN1 δ hδ.le
    (fun t ht => by
      have htt := hN₀ t (hN.trans (mem_Icc.mp ht).1)
      have htp : (0 : ℝ) < t := by exact_mod_cast htt.2
      have hh := htt.1
      rw [abs_div, abs_of_pos htp] at hh
      exact ((div_lt_iff₀ htp).mp hh).le)
  rw [Real.dist_eq, sub_zero]
  have heq : δ * ((K : ℝ) + 1) = ε / 4 := by dsimp [δ]; field_simp
  rw [heq] at hr
  linarith

theorem tendsto_mertens_div_of_log_six (K : ℝ) (_hK : 0 ≤ K)
    (hM : ∀ᶠ t : ℕ in atTop, |mertensSum t| ≤ K * t / (Real.log t) ^ 6) :
    Tendsto (fun t : ℕ => mertensSum t / t) atTop (nhds 0) := by
  have hl : Tendsto (fun t : ℕ => Real.log (t : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun t : ℕ => K / (Real.log t) ^ 6) atTop (nhds 0) := by
    simpa [div_eq_mul_inv, inv_pow] using
      (hl.inv_tendsto_atTop.pow 6).const_mul K
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards with t
    exact abs_nonneg _
  · filter_upwards [hM, eventually_ge_atTop 1] with t ht ht1
    have htp : (0 : ℝ) < t := by exact_mod_cast ht1
    dsimp only [Function.comp_def]
    rw [abs_div, abs_of_pos htp]
    apply (div_le_div_of_nonneg_right ht htp.le).trans
    have heq : (K * (t : ℝ) / (Real.log t) ^ 6) / t = K / (Real.log t) ^ 6 := by field_simp
    exact heq.le

/-- The zero constant is now derived from the ordinary Mertens hypothesis.-/
theorem tendsto_normalizedMoebiusSum_of_mertens_log_six (K : ℝ) (hK : 0 ≤ K)
    (hM : ∀ᶠ t : ℕ in atTop, |mertensSum t| ≤ K * t / (Real.log t) ^ 6) :
    Tendsto normalizedMoebiusSum atTop (nhds 0) :=
  tendsto_normalizedMoebiusSum_of_mertens_sublinear (tendsto_mertens_div_of_log_six K hK hM)

theorem normalizedMoebiusSum_abs_le_log_five_of_mertens (K : ℝ) (hK : 0 ≤ K)
    (hM : ∀ᶠ t : ℕ in atTop, |mertensSum t| ≤ K * t / (Real.log t) ^ 6) :
    ∀ᶠ t : ℕ in atTop,
      |normalizedMoebiusSum t| ≤ (32 + 2 / Real.log 2) * K / (Real.log t) ^ 5 := by
  simpa only [reciprocalCoefficientSum_moebius, sub_zero] using
    reciprocalCoefficientSum_sub_limit_le_log_five (fun n => (μ n : ℝ)) K hK hM 0
      (tendsto_normalizedMoebiusSum_of_mertens_log_six K hK hM)

theorem tendsto_normalizedMoebiusSum_log_sq_of_mertens (K : ℝ) (hK : 0 ≤ K)
    (hM : ∀ᶠ t : ℕ in atTop, |mertensSum t| ≤ K * t / (Real.log t) ^ 6) :
    Tendsto (fun t : ℕ => normalizedMoebiusSum t * (Real.log (t + 1)) ^ 2)
      atTop (nhds 0) :=
  tendsto_normalizedMoebiusSum_mul_log_sq_of_mertens_log_six K hK hM
    (tendsto_normalizedMoebiusSum_of_mertens_log_six K hK hM)

end TwinPrime.Analytic

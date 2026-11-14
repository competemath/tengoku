import Tengoku.Twinprime.TwinPrime.Sieve.TwinBound
import Tengoku.Seed.NumberTheory.Chebyshev

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The dyadic fixed-shift endpoint

All sums in this file use the integer interval `X < n ≤ 2 * X`.
`N2` counts genuine twin pairs, while `W2` is the von Mangoldt correlation.
The explicitly subtracted term `Epp` contains every contribution with a nonprime
member. Cofinal positivity of `W2 - Epp` is equivalent to the twin prime
conjecture; no positivity hypothesis is proved or incorporated into a definition.
-/

noncomputable section

open Finset Filter
open scoped ArithmeticFunction.vonMangoldt

namespace TwinPrime

/-- Number of twin pairs whose lower member is in `(X, 2X]`.-/
def N2 (X : ℕ) : ℕ := ((Ioc X (2 * X)).filter (· ∈ twinPrimes)).card

/-- The von Mangoldt correlation on `(X, 2X]`, including proper prime powers.-/
def W2 (X : ℕ) : ℝ := ∑ n ∈ Ioc X (2 * X), Λ n * Λ (n + 2)

/-- Contribution to `W2` from terms with at least one nonprime member.-/
def Epp (X : ℕ) : ℝ :=
  ∑ n ∈ (Ioc X (2 * X)).filter (· ∉ twinPrimes), Λ n * Λ (n + 2)

theorem twinCount_mono : Monotone twinCount := by
  intro x y hxy
  apply Finset.card_le_card
  intro n hn
  simp only [mem_filter, mem_range] at hn ⊢
  exact ⟨by omega, hn.2⟩

/-- Natural subtraction is valid because the earlier counting set is a subset.-/
theorem N2_eq_twinCount_sub (X : ℕ) : N2 X = twinCount (2 * X) - twinCount X := by
  have hsub : (range (X + 1)).filter (· ∈ twinPrimes) ⊆
      (range (2 * X + 1)).filter (· ∈ twinPrimes) := by
    intro n hn
    simp only [mem_filter, mem_range] at hn ⊢
    exact ⟨by omega, hn.2⟩
  have heq : (Ioc X (2 * X)).filter (· ∈ twinPrimes) =
      (range (2 * X + 1)).filter (· ∈ twinPrimes) \
      (range (X + 1)).filter (· ∈ twinPrimes) := by
    apply Finset.ext
    intro n
    simp only [Finset.mem_sdiff, mem_filter, mem_Ioc, mem_range, mem_twinPrimes]
    constructor
    · rintro ⟨⟨hXn, hnX⟩, hp⟩
      refine ⟨⟨by omega, hp⟩, ?_⟩
      rintro ⟨hn, _⟩
      omega
    · rintro ⟨⟨hnX, hp⟩, hn⟩
      refine ⟨⟨?_, by omega⟩, hp⟩
      by_contra hXn
      exact hn ⟨by omega, hp⟩
  unfold N2 twinCount
  rw [heq, card_sdiff_of_subset hsub]

theorem N2_pos_iff (X : ℕ) :
    0 < N2 X ↔ ∃ n, X < n ∧ n ≤ 2 * X ∧ n ∈ twinPrimes := by
  simp only [N2, card_pos, nonempty_def, mem_filter, mem_Ioc]
  aesop

/-- Good dyadic intervals need only occur cofinally, rather than eventually.-/
theorem twinPrimeConjecture_iff_cofinal_N2_pos :
    TwinPrimeConjecture ↔ ∀ Y : ℕ, ∃ X ≥ Y, 0 < N2 X := by
  rw [twinPrimeConjecture_iff_forall_exists_gt]
  constructor
  · intro h Y
    obtain ⟨p, hp, hYp⟩ := h (Y + 1)
    refine ⟨p - 1, by omega, (N2_pos_iff _).mpr ⟨p, by omega, by omega, hp⟩⟩
  · intro h Y
    obtain ⟨X, hYX, hX⟩ := h Y
    obtain ⟨p, hXp, _, hp⟩ := (N2_pos_iff X).mp hX
    exact ⟨p, hp, lt_of_le_of_lt hYX hXp⟩

theorem Epp_nonneg (X : ℕ) : 0 ≤ Epp X := by
  exact sum_nonneg fun _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    ArithmeticFunction.vonMangoldt_nonneg

/-- Exact removal of all nonprime contributions from the correlation.-/
theorem W2_sub_Epp_eq_prime_sum (X : ℕ) :
    W2 X - Epp X =
      ∑ n ∈ (Ioc X (2 * X)).filter (· ∈ twinPrimes),
        Real.log n * Real.log (n + 2) := by
  have hsplit := sum_filter_add_sum_filter_not (Ioc X (2 * X))
    (fun n => n ∈ twinPrimes) (fun n => Λ n * Λ (n + 2))
  have hprime :
      (∑ n ∈ (Ioc X (2 * X)).filter (· ∈ twinPrimes), Λ n * Λ (n + 2)) =
      ∑ n ∈ (Ioc X (2 * X)).filter (· ∈ twinPrimes),
        Real.log n * Real.log (n + 2) := by
    apply sum_congr rfl
    intro n hn
    obtain ⟨hp, hq⟩ := (mem_filter.mp hn).2
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp,
      ArithmeticFunction.vonMangoldt_apply_prime hq]
    norm_cast
  unfold W2 Epp
  rw [← hsplit, add_sub_cancel_right, hprime]

/-- The prime-power subtraction inequality (PP) from the proof plan.-/
theorem W2_sub_Epp_le_log_sq_mul_N2 (X : ℕ) :
    W2 X - Epp X ≤ (Real.log (2 * X + 2)) ^ 2 * N2 X := by
  rw [W2_sub_Epp_eq_prime_sum]
  calc
    _ ≤ ∑ _n ∈ (Ioc X (2 * X)).filter (· ∈ twinPrimes),
        (Real.log (2 * X + 2)) ^ 2 := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hnI, hp, hq⟩ := mem_filter.mp hn
      have hnle : (n : ℝ) ≤ 2 * X + 2 := by
        have := (mem_Ioc.mp hnI).2
        exact_mod_cast (show n ≤ 2 * X + 2 by omega)
      have hqle : (n : ℝ) + 2 ≤ 2 * X + 2 := by
        exact_mod_cast Nat.add_le_add_right (mem_Ioc.mp hnI).2 2
      have hp0 : (0 : ℝ) < n := by exact_mod_cast hp.pos
      have hq0 : (0 : ℝ) < n + 2 := by positivity
      have hlog : 0 ≤ Real.log (2 * X + 2) :=
        Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith)
      exact (mul_le_mul (Real.log_le_log hp0 hnle) (Real.log_le_log hq0 hqle)
        (Real.log_nonneg (by exact_mod_cast hq.one_le)) hlog).trans_eq (sq _).symm
    _ = _ := by simp [N2, mul_comm]

theorem W2_gt_Epp_iff_N2_pos (X : ℕ) : Epp X < W2 X ↔ 0 < N2 X := by
  rw [← sub_pos, W2_sub_Epp_eq_prime_sum]
  constructor
  · intro h
    by_contra hN
    have hempty : (Ioc X (2 * X)).filter (· ∈ twinPrimes) = ∅ :=
      card_eq_zero.mp (Nat.eq_zero_of_not_pos hN)
    rw [hempty, sum_empty] at h
    exact (lt_irrefl 0) h
  · intro h
    obtain ⟨p, hXp, hpX, hp, hq⟩ := (N2_pos_iff X).mp h
    apply sum_pos'
    · intro n hn
      obtain ⟨_, hn, hn2⟩ := mem_filter.mp hn
      apply mul_nonneg <;> apply Real.log_nonneg
      · exact_mod_cast hn.one_le
      · exact_mod_cast hn2.one_le
    · refine ⟨p, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hXp, hpX⟩, hp, hq⟩, ?_⟩
      apply mul_pos <;> apply Real.log_pos
      · exact_mod_cast hp.one_lt
      · exact_mod_cast hq.one_lt

theorem twinPrimeConjecture_iff_cofinal_W2_gt_Epp :
    TwinPrimeConjecture ↔ ∀ Y : ℕ, ∃ X ≥ Y, Epp X < W2 X := by
  simp_rw [W2_gt_Epp_iff_N2_pos]
  exact twinPrimeConjecture_iff_cofinal_N2_pos

theorem twinPrimeConjecture_of_cofinal_W2_gt_Epp
    (h : ∀ Y : ℕ, ∃ X ≥ Y, Epp X < W2 X) : TwinPrimeConjecture :=
  twinPrimeConjecture_iff_cofinal_W2_gt_Epp.mpr h

/-- A direct bound for the excluded contribution using the classical elementary
Chebyshev bound for `ψ - θ`. It is sufficient for the required `o(X)` error.-/
theorem Epp_le_sqrt_mul_log_sq (X : ℕ) :
    Epp X ≤ 4 * Real.sqrt (2 * X + 2) * (Real.log (2 * X + 2)) ^ 2 := by
  let Y : ℕ := 2 * X + 2
  let L : ℝ := Real.log Y
  let f : ℕ → ℝ := fun n => if ¬n.Prime then Λ n else 0
  have hf : ∀ n, 0 ≤ f n := by
    intro n
    dsimp [f]
    split_ifs <;> positivity
  have hY : (1 : ℝ) ≤ Y := by
    exact_mod_cast (show 1 ≤ Y by dsimp [Y]; omega)
  have hL : 0 ≤ L := Real.log_nonneg hY
  have htotal : (∑ n ∈ Ioc 0 Y, f n) = Chebyshev.psi Y - Chebyshev.theta Y := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
    simp [f, sum_filter]
  have hfirst : (∑ n ∈ Ioc X (2 * X), f n) ≤ ∑ n ∈ Ioc 0 Y, f n := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [mem_Ioc] at hn ⊢
      dsimp [Y]
      omega
    · exact fun n _ _ => hf n
  have hsecond : (∑ n ∈ Ioc X (2 * X), f (n + 2)) ≤ ∑ n ∈ Ioc 0 Y, f n := by
    rw [← sum_image (fun a _ b _ h => Nat.add_right_cancel h)]
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
      simp only [mem_Ioc] at hm ⊢
      dsimp [Y]
      omega
    · exact fun n _ _ => hf n
  have hpoint : Epp X ≤ L *
      ((∑ n ∈ Ioc X (2 * X), f n) + ∑ n ∈ Ioc X (2 * X), f (n + 2)) := by
    unfold Epp
    rw [sum_filter, mul_add, mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1.trans_le' (Nat.zero_le X)
    have hnY : (n : ℝ) ≤ Y := by
      exact_mod_cast (show n ≤ Y by dsimp [Y]; have := (mem_Ioc.mp hn).2; omega)
    have hq0 : (0 : ℝ) < (n + 2 : ℕ) := by positivity
    have hqY : ((n + 2 : ℕ) : ℝ) ≤ Y := by
      exact_mod_cast (show n + 2 ≤ Y by dsimp [Y]; have := (mem_Ioc.mp hn).2; omega)
    have hnL : Λ n ≤ L := ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log hn0 hnY)
    have hqL : Λ (n + 2) ≤ L := ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log hq0 hqY)
    have hnΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hqΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n + 2)
    by_cases hp : n.Prime <;> by_cases hq : (n + 2).Prime <;>
      simp only [mem_twinPrimes, hp, hq, and_self, not_true_eq_false, not_false_eq_true,
        and_false, and_true, ite_true, ite_false, f, mul_zero,
        zero_add, add_zero]
    · exact le_rfl
    · exact mul_le_mul_of_nonneg_right hnL hqΛ
    · nlinarith [mul_le_mul_of_nonneg_left hqL hnΛ]
    · nlinarith [mul_le_mul_of_nonneg_right hnL hqΛ, mul_nonneg hL hnΛ]
  have hmain : Epp X ≤ 4 * Real.sqrt (Y : ℝ) * L ^ 2 := by
    calc
      Epp X ≤ L *
          ((∑ n ∈ Ioc X (2 * X), f n) + ∑ n ∈ Ioc X (2 * X), f (n + 2)) := hpoint
      _ ≤ L * ((∑ n ∈ Ioc 0 Y, f n) + ∑ n ∈ Ioc 0 Y, f n) :=
        mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hL
      _ = L * (2 * (Chebyshev.psi Y - Chebyshev.theta Y)) := by rw [htotal]; ring
      _ ≤ L * (2 * (2 * Real.sqrt (Y : ℝ) * L)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Chebyshev.psi_sub_theta_le hY) (by norm_num)) hL
      _ = _ := by ring
  simpa [Y, L] using hmain

/-- The elementary prime-power error bound is sublinear.-/
theorem tendsto_primePowerError_div :
    Tendsto (fun X : ℕ =>
      (4 * Real.sqrt (2 * X + 2) * (Real.log (2 * X + 2)) ^ 2) / X)
      atTop (nhds 0) := by
  have hlog : Tendsto (fun t : ℝ => (Real.log t) ^ 2 / Real.sqrt t) atTop (nhds 0) := by
    simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 1 / 2)
        (by norm_num)).tendsto_div_nhds_zero
  have harg : Tendsto (fun X : ℕ => (2 : ℝ) * X + 2) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_natCast_atTop_atTop
    filter_upwards with X
    have := Nat.cast_nonneg (α := ℝ) X
    linarith
  have hinv : Tendsto (fun X : ℕ => (X : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun X : ℕ => (2 : ℝ) + 2 * (X : ℝ)⁻¹)
      atTop (nhds 2) := by
    convert (tendsto_const_nhds.add (hinv.const_mul 2)) using 1
    norm_num
  have h := ((hlog.comp harg).mul hratio).const_mul 4
  simp only [mul_zero, zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with X hX
  have hx : (X : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hX)
  have hy : (0 : ℝ) < 2 * X + 2 := by positivity
  have hs : Real.sqrt (2 * X + 2) ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have heq := Real.sq_sqrt hy.le
  dsimp only [Function.comp_def]
  field_simp
  have heq' : Real.sqrt (2 * ((X : ℝ) + 1)) ^ 2 = 2 * ((X : ℝ) + 1) := by
    exact Real.sq_sqrt (by positivity)
  rw [heq']
  ring

/-- Removing proper prime powers has zero relative cost on dyadic intervals.-/
theorem tendsto_Epp_div :
    Tendsto (fun X : ℕ => Epp X / X) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds tendsto_primePowerError_div
  · filter_upwards with X
    exact div_nonneg (Epp_nonneg X) (Nat.cast_nonneg X)
  · filter_upwards with X
    exact div_le_div_of_nonneg_right (Epp_le_sqrt_mul_log_sq X) (Nat.cast_nonneg X)

/-- Any fixed positive linear lower bound on cofinally many `W2` values suffices.
The needed prime-power estimate is proved above rather than assumed here.-/
theorem twinPrimeConjecture_of_cofinal_W2_linear {c : ℝ} (hc : 0 < c)
    (h : ∀ Y : ℕ, ∃ X ≥ Y, c * X ≤ W2 X) : TwinPrimeConjecture := by
  have hsmall : ∀ᶠ X : ℕ in atTop, Epp X / X < c :=
    tendsto_Epp_div.eventually (gt_mem_nhds hc)
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp hsmall
  apply twinPrimeConjecture_of_cofinal_W2_gt_Epp
  intro Y
  obtain ⟨X, hX, hW⟩ := h (max Y (max Y₀ 1))
  have hXY : Y ≤ X := (le_max_left _ _).trans hX
  have hXY₀ : Y₀ ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have hX1 : 1 ≤ X := (le_max_right _ _).trans ((le_max_right _ _).trans hX)
  refine ⟨X, hXY, lt_of_lt_of_le ?_ hW⟩
  exact (div_lt_iff₀ (by exact_mod_cast (show 0 < X by omega))).mp (hY₀ X hXY₀)

end TwinPrime

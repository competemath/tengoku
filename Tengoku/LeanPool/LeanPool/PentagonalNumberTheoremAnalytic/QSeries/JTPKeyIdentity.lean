/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.PentagonalNumberTheoremAnalytic.QSeries.EulerIdentities

/-!
# Key identity for the Jacobi triple product

We prove that for ‖q‖ < 1 and all k ≥ 0:

$$S_k(q) := \sum_{m=0}^{\infty} \frac{q^{m(m+k)}}{(q;q)_m (q;q)_{m+k}} = \frac{1}{(q;q)_\infty}$$

The proof uses a recurrence:
  S_k - S_{k+1} = q^{k+1} (S_{k+2} - S_{k+1})

This forces all differences to be zero (since S_k → 1/(q;q)_∞),
so all S_k are equal to 1/(q;q)_∞.
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace QSeries

noncomputable section

/-- The key sum S_k(q) = Σ_{m≥0} q^{m(m+k)} / ((q;q)_m (q;q)_{m+k}). -/
def keySum (q : ℂ) (k : ℕ) : ℂ :=
  ∑' m : ℕ, q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k))

/-- The summand of S_k. -/
def keySummand (q : ℂ) (k : ℕ) (m : ℕ) : ℂ :=
  q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k))

/-- Unfolds `keySum` as the tsum of `keySummand`.
@isnad1 id=eq.0h2v.s5.69e01b36346a from=translated src=- shape=3e0437c8 vocab=fe649c53
-/
theorem keySum_eq_tsum (q : ℂ) (k : ℕ) :
    keySum q k = ∑' m, keySummand q k m := rfl

/-- A sequence of positive reals converging to a positive limit is bounded below by a
positive constant. -/
private theorem exists_pos_le_of_tendsto {f : ℕ → ℝ} {L : ℝ} (hL : 0 < L)
    (hf : Tendsto f atTop (𝓝 L)) (hpos : ∀ n, 0 < f n) : ∃ C > 0, ∀ n, C ≤ f n := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hf.eventually (lt_mem_nhds (half_lt_self hL)))
  have hne : (Finset.range (N + 1)).Nonempty := ⟨0, by simp⟩
  refine ⟨min (L / 2) ((Finset.range (N + 1)).inf' hne f), ?_, fun n => ?_⟩
  · exact lt_min (by linarith) ((Finset.lt_inf'_iff hne).2 fun i _ => hpos i)
  · rcases le_or_gt n N with h | h
    · exact (min_le_right _ _).trans (Finset.inf'_le f (Finset.mem_range.2 (by omega)))
    · exact (min_le_left _ _).trans (hN n h.le).le

/-- The finite q-Pochhammer symbols `(q;q)_n` are bounded away from `0` uniformly in `n`,
since they converge to the nonzero limit `(q;q)_∞`.
@isnad1 id=ex.1h1v.s5.9caf869ca067 from=translated src=- shape=4ac0e167 vocab=61fbbbce
-/
theorem exists_pos_le_norm_qPochhammer_self {q : ℂ} (hq : ‖q‖ < 1) :
    ∃ C > 0, ∀ n : ℕ, C ≤ ‖qPochhammer q q n‖ :=
  exists_pos_le_of_tendsto (norm_pos_iff.mpr (qPochhammerInf_ne_zero hq hq))
    (tendsto_qPochhammer hq).norm fun n => norm_pos_iff.mpr (qPochhammer_self_ne_zero hq n)

/-- The series defining $S_k(q)$ is summable for $\|q\| < 1$.
@isnad1 id=summable.1h2v.s5.12370668570b from=translated src=- shape=571a36be vocab=81b2523b
-/
theorem summable_keySummand {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    Summable (keySummand q k) := by
  obtain ⟨C, hC₀, hC⟩ := exists_pos_le_norm_qPochhammer_self hq
  have hsq : Summable fun m : ℕ => ‖q‖ ^ (m ^ 2) :=
    Summable.comp_injective (summable_geometric_of_lt_one (norm_nonneg q) hq)
      fun a b h => by simpa using h
  refine Summable.of_norm <| (hsq.mul_right (C * C)⁻¹).of_nonneg_of_le
    (fun m => norm_nonneg _) fun m => ?_
  have h1 : ‖q‖ ^ (m * (m + k)) ≤ ‖q‖ ^ (m ^ 2) :=
    pow_le_pow_of_le_one (norm_nonneg q) hq.le (by nlinarith)
  have h2 : C * C ≤ ‖qPochhammer q q m‖ * ‖qPochhammer q q (m + k)‖ :=
    mul_le_mul (hC m) (hC (m + k)) hC₀.le (hC₀.le.trans (hC m))
  rw [keySummand, norm_div, norm_pow, norm_mul, ← div_eq_mul_inv]
  exact div_le_div₀ (by positivity) h1 (by positivity) h2

/-- As $k \to \infty$, $S_k(q)$ converges to $1/(q;q)_\infty$.
@isnad1 id=tendsto.1h1v.s5.1ba8360f5a34 from=translated src=- shape=313dc6c4 vocab=988767fd
-/
theorem tendsto_keySum {q : ℂ} (hq : ‖q‖ < 1) :
    Tendsto (keySum q) atTop (𝓝 (1 / qPochhammerInf q q)) := by
  obtain ⟨C, hC₀, hC⟩ := exists_pos_le_norm_qPochhammer_self hq
  have hCC : ∀ m k : ℕ, C * C ≤ ‖qPochhammer q q m * qPochhammer q q (m + k)‖ := fun m k => by
    rw [norm_mul]
    exact mul_le_mul (hC m) (hC (m + k)) hC₀.le (hC₀.le.trans (hC m))
  have hCC₀ : (0 : ℝ) < C * C := mul_pos hC₀ hC₀
  have h_m_zero : Tendsto (fun k => 1 / qPochhammer q q k) atTop (𝓝 (1 / qPochhammerInf q q)) :=
    tendsto_const_nhds.div (tendsto_qPochhammer hq) (qPochhammerInf_ne_zero hq hq)
  have h_sum_zero : Tendsto (fun k => ∑' m : ℕ, (if m = 0 then 0 else
      q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k)))) atTop (𝓝 0) := by
    have h_dominated : ∀ m, m ≠ 0 → Tendsto (fun k : ℕ =>
        q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k))) atTop (𝓝 0) := by
      intro m hm
      have h_lim : Tendsto (fun k : ℕ => q ^ (m * (m + k))) atTop (𝓝 0) :=
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).comp <|
          tendsto_atTop_mono (fun k => by nlinarith [Nat.one_le_iff_ne_zero.mpr hm])
            tendsto_natCast_atTop_atTop
      have h_bnd : Tendsto (fun k : ℕ => ‖q ^ (m * (m + k))‖ / (C * C)) atTop (𝓝 0) := by
        simpa using h_lim.norm.div_const (C * C)
      refine squeeze_zero_norm (fun k => ?_) h_bnd
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hCC₀ (hCC m k)
    have h_dom_conv : Tendsto (fun k => ∑' m : ℕ, (if m = 0 then 0 else
        q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k)))) atTop
        (𝓝 (∑' _ : ℕ, (0 : ℂ))) := by
      refine tendsto_tsum_of_dominated_convergence
        (bound := fun m : ℕ => if m = 0 then 0 else ‖q‖ ^ (m * m) / (C * C)) ?_ ?_ ?_
      · rw [← summable_nat_add_iff 1]
        refine Summable.mul_right _ <| Summable.of_nonneg_of_le (fun n => by positivity)
          (fun n => ?_) <| summable_geometric_of_lt_one (norm_nonneg q) hq
        simpa using pow_le_pow_of_le_one (norm_nonneg q) hq.le (by nlinarith)
      · intro m
        by_cases hm : m = 0
        · simp only [hm]
          exact tendsto_const_nhds
        · simpa only [ite_eq_right hm] using h_dominated m hm
      · refine Filter.Eventually.of_forall fun k m => ?_
        by_cases hm : m = 0
        · simp [hm]
        · simp only [ite_eq_right hm, norm_div]
          refine div_le_div₀ (by positivity) ?_ hCC₀ (hCC m k)
          rw [norm_pow]
          exact pow_le_pow_of_le_one (norm_nonneg q) hq.le (by nlinarith)
    simpa using h_dom_conv
  convert h_m_zero.add h_sum_zero using 2 <;> norm_num [keySum]
  rw [Summable.tsum_eq_add_tsum_ite]
  any_goals exact Nat.zero
  · norm_num [qPochhammer]
  · exact summable_keySummand hq _

/-- For `‖q‖ < 1` and `n ≥ 1` the tail factor `1 - qⁿ` is bounded away from zero,
uniformly in `n`, by the constant `1 - ‖q‖`.
@isnad1 id=le.2h2v.s6.0c4894736c5c from=translated src=- shape=7ef6a77a vocab=53fdcbe5
-/
theorem one_sub_norm_le_norm_one_sub_pow {q : ℂ} (hq : ‖q‖ < 1) {n : ℕ} (hn : 1 ≤ n) :
    1 - ‖q‖ ≤ ‖1 - q ^ n‖ := by
  refine le_trans ?_ (norm_sub_norm_le (1 : ℂ) (q ^ n))
  have h : ‖q‖ ^ n ≤ ‖q‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg q) hq.le hn
  simp only [norm_one, norm_pow, pow_one] at h ⊢
  linarith

/-- The shifted family `q ^ (m * (m + k)) / ((q;q)_m (q;q)_{m+k+1})` is summable:
it is `keySummand q k` scaled by the uniformly bounded factor `(1 - q ^ (m+k+1))⁻¹`.
@isnad1 id=summable.1h2v.s6.701f040ae9e4 from=translated src=- shape=df96429d vocab=4482d65a
-/
theorem summable_pow_div_qPochhammer_succ {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    Summable fun m : ℕ =>
      q ^ (m * (m + k)) / (qPochhammer q q m * qPochhammer q q (m + k + 1)) := by
  have hpos : (0 : ℝ) < 1 - ‖q‖ := by linarith
  refine Summable.of_norm <|
    ((summable_keySummand hq k).norm.mul_right (1 - ‖q‖)⁻¹).of_nonneg_of_le
      (fun m => norm_nonneg _) fun m => ?_
  rw [qPochhammer_succ, ← mul_assoc, ← pow_succ', div_mul_eq_div_div, norm_div, div_eq_mul_inv,
    keySummand]
  gcongr
  exact one_sub_norm_le_norm_one_sub_pow hq (by omega)

/-- Multiplying the shifted family by the bounded factor `1 - q ^ m` preserves summability.
@isnad1 id=summable.1h2v.s7.432144dfd394 from=translated src=- shape=5c69c49c vocab=0e1cce10
-/
theorem summable_pow_mul_one_sub_pow_div_qPochhammer {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    Summable fun m : ℕ =>
      q ^ (m * (m + k)) * (1 - q ^ m) / (qPochhammer q q m * qPochhammer q q (m + k + 1)) := by
  refine Summable.of_norm <|
    ((summable_pow_div_qPochhammer_succ hq k).norm.mul_right 2).of_nonneg_of_le
      (fun m => norm_nonneg _) fun m => ?_
  rw [← div_mul_eq_mul_div, norm_mul]
  gcongr
  refine le_trans (norm_sub_le _ _) ?_
  have : ‖q‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg q) hq.le
  simp only [norm_one, norm_pow]
  linarith

/-- Telescoping: `(q;q)_∞ = (q;q)_n * (q^{n+1};q)_∞`. -/
private lemma qPochhammerInf_eq_qPochhammer_mul {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    qPochhammerInf q q = qPochhammer q q n * qPochhammerInf (q * q ^ n) q := by
  induction n with
  | zero => simp [qPochhammer]
  | succ n ih =>
    rw [ih, qPochhammer_succ, mul_assoc]
    congr 1
    rw [qPochhammerInf_eq_one_sub_mul hq]
    ring_nf

/-- `qPochhammerInf (q * q^n) q = (q;q)_∞ / (q;q)_n`.
@isnad1 id=eq.1h2v.s6.bd1ea20f3762 from=translated src=- shape=9de53da5 vocab=dfc3d790
-/
theorem qPochhammerInf_mul_pow_eq_div {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    qPochhammerInf (q * q ^ n) q = qPochhammerInf q q / qPochhammer q q n := by
  rw [eq_div_iff (qPochhammer_self_ne_zero hq n), mul_comm]
  exact (qPochhammerInf_eq_qPochhammer_mul hq n).symm

end

end QSeries

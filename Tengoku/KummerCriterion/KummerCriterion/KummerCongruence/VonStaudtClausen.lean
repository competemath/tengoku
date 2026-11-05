module

public import Tengoku.Seed.NumberTheory.Bernoulli
public import Tengoku.Seed.NumberTheory.Padics.PadicIntegers
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.NNReal
import Tengoku.Seed.CategoryTheory.Category.Init

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Kummer congruences - Von Staudt–Clausen + Step 2 (power-sum mod `p²`)

This module proves the `p`-adic integrality ingredients for the Kummer
congruence chain:

- **Adams' integrality** (restricted to `k < p - 1`):
 `bernoulli_div_mem_padicInt`.
- **Von Staudt–Clausen (generic case, restricted)**:
 `bernoulli_mem_padicInt_of_not_pSubOne_dvd`.
- **Faulhaber term bound** (helper): `faulhaber_term_mem_p_sq`.
- **Pre-division Step 2**: `sum_range_pow_sub_p_mul_bernoulli_weighted`.
- **Step 2** (power-sum mod `p²`): `sum_range_pow_sModEq_p_mul_bernoulli`.
- **Von Staudt–Clausen (unified, restricted)**:
 `p_mul_bernoulli_mem_padicInt_restricted`.

See the umbrella `KummerCriterion.KummerCongruence` for the full
statements derived from these ingredients.
-/

@[expose] public section

noncomputable section

namespace KummerCriterion

/-- **Pointwise Faulhaber term bound** (helper for Step 2): for `i < t`
with `t` even and `t ≥ 2`, each Faulhaber summand `B_i · C(t+1, i) · p^{t+1-i}`
is in `p² · ℤ_p`, assuming the lower even Bernoulli terms satisfy the
unified `p · B_j` integrality bound.-/
lemma faulhaber_term_mem_p_sq
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {t : ℕ} (ht_two : 2 ≤ t) (ht_even : Even t)
    (ih_pB : ∀ j, j < t -> 2 ≤ j -> Even j ->
      ∃ z : ℤ_[p], (p : ℚ_[p]) * ((bernoulli j : ℚ) : ℚ_[p]) = (z : ℚ_[p]))
    {i : ℕ} (hi : i < t) :
    ∃ z : ℤ_[p],
      ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (t + 1 - i)) =
        ((p : ℚ_[p]) ^ 2) * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  rcases Nat.eq_zero_or_pos i with rfl | hi_pos
  · refine ⟨(p : ℤ_[p]) ^ (t - 1), ?_⟩
    simp only [_root_.bernoulli_zero, Rat.cast_one, one_mul,
      Nat.choose_zero_right, Nat.cast_one]
    rw [show (t + 1 - 0 : ℕ) = 2 + (t - 1) by omega, pow_add]; push_cast; ring
  rcases eq_or_ne i 1 with rfl | hi_ne_one
  · have h2_unit : IsUnit ((2 : ℕ) : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact hp.coprime_iff_not_dvd.mpr fun h =>
        absurd (Nat.le_of_dvd (by omega) h) (by omega)
    set w : ℤ_[p] := (h2_unit.unit⁻¹ : (ℤ_[p])ˣ).val with hw_def
    have hw_mul : ((2 : ℕ) : ℤ_[p]) * w = 1 := by
      change ((h2_unit.unit * h2_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1; simp
    have hw_mul_Qp : (2 : ℚ_[p]) * ((w : ℤ_[p]) : ℚ_[p]) = 1 := by
      simpa using! congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hw_mul
    refine ⟨-((Nat.choose (t + 1) 1 : ℤ_[p]) * w * (p : ℤ_[p]) ^ (t - 2)), ?_⟩
    rw [_root_.bernoulli_one,
      show (t + 1 - 1 : ℕ) = 2 + (t - 2) by omega, pow_add]
    have h2Q_ne : (2 : ℚ_[p]) ≠ 0 := by norm_num
    have h_half : ((-1 / 2 : ℚ) : ℚ_[p]) = -((w : ℤ_[p]) : ℚ_[p]) :=
      mul_left_cancel₀ h2Q_ne (by push_cast; linear_combination hw_mul_Qp)
    rw [h_half]; push_cast; ring
  have hi_ge : 2 ≤ i := by omega
  rcases Nat.even_or_odd i with hi_even | hi_odd
  · have hi_le : i ≤ t - 2 := by
      rcases hi_even with ⟨k, hk⟩; rcases ht_even with ⟨m, hm⟩; omega
    obtain ⟨c, hc⟩ := ih_pB i hi hi_ge hi_even
    refine ⟨c * (Nat.choose (t + 1) i : ℤ_[p]) * (p : ℤ_[p]) ^ (t - i - 2), ?_⟩
    rw [show t + 1 - i = 1 + (t - i - 2) + 2 from by omega,
      show (p : ℚ_[p]) ^ (1 + (t - i - 2) + 2) =
        (p : ℚ_[p]) * (p : ℚ_[p]) ^ (t - i - 2) * (p : ℚ_[p]) ^ 2 from by
        rw [pow_add, pow_add]; ring]
    have hbc : ((bernoulli i : ℚ) : ℚ_[p]) * ((p : ℚ_[p])) = ((c : ℤ_[p]) : ℚ_[p]) := by
      rw [← hc]; ring
    push_cast
    linear_combination
      (((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) * ((p : ℚ_[p]) ^ (t - i - 2)) *
        ((p : ℚ_[p]) ^ 2)) * hbc
  · refine ⟨0, ?_⟩
    have hi_gt : 1 < i := by omega
    rw [bernoulli_eq_zero_of_odd hi_odd hi_gt]; push_cast; ring

/-- **Pre-division Step 2**: the `(t+1)`-weighted Faulhaber identity
`∑ a^t − p · B_t`, assuming the lower even `p · B_j` integrality bounds.-/
theorem sum_range_pow_sub_p_mul_bernoulli_weighted
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {t : ℕ} (ht_two : 2 ≤ t) (ht_even : Even t)
    (ih_pB : ∀ j, j < t -> 2 ≤ j -> Even j ->
      ∃ z : ℤ_[p], (p : ℚ_[p]) * ((bernoulli j : ℚ) : ℚ_[p]) = (z : ℚ_[p])) :
    ∃ W : ℤ_[p],
      ((t + 1 : ℕ) : ℚ_[p]) *
          ((∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t) -
            (p : ℚ_[p]) * ((bernoulli t : ℚ) : ℚ_[p])) =
        ((p : ℚ_[p]) ^ 2) * ((W : ℤ_[p]) : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  choose w hw using (fun (i : ℕ) (hi : i < t) =>
    faulhaber_term_mem_p_sq hp_odd ht_two ht_even ih_pB hi)
  set W : ℤ_[p] :=
    ∑ i ∈ Finset.attach (Finset.range t), w i.1 (Finset.mem_range.mp i.2) with hW_def
  refine ⟨W, ?_⟩
  have h_faulhaber_Q : ((t + 1 : ℚ)) * (∑ k ∈ Finset.range p, (k : ℚ) ^ t) =
      ∑ i ∈ Finset.range (t + 1),
        bernoulli i * (Nat.choose (t + 1) i : ℚ) * (p : ℚ) ^ (t + 1 - i) := by
    rw [sum_range_pow p t, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have htp1Q_ne : (((t + 1 : ℕ)) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  have h_faulhaber_Qp : ((t + 1 : ℕ) : ℚ_[p]) * (∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t) =
      ∑ i ∈ Finset.range (t + 1),
        ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p])) ^ (t + 1 - i) := by
    have := congrArg (fun q : ℚ => (q : ℚ_[p])) h_faulhaber_Q
    push_cast at this; push_cast; exact this
  have h_split_sum : ((t + 1 : ℕ) : ℚ_[p]) * (∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t) -
        ((t + 1 : ℕ) : ℚ_[p]) * ((p : ℚ_[p])) * ((bernoulli t : ℚ) : ℚ_[p]) =
      ∑ i ∈ Finset.range t,
        ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p])) ^ (t + 1 - i) := by
    rw [h_faulhaber_Qp, Finset.sum_range_succ, Nat.choose_succ_self_right t,
      show (t + 1 - t : ℕ) = 1 from by omega]
    push_cast; ring
  have h_rhs_eq : (∑ i ∈ Finset.range t,
        ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p])) ^ (t + 1 - i)) =
      ((p : ℚ_[p])) ^ 2 * ((W : ℤ_[p]) : ℚ_[p]) := by
    rw [← Finset.sum_attach]
    rw [show (((p : ℚ_[p])) ^ 2 * ((W : ℤ_[p]) : ℚ_[p])) =
        ∑ i ∈ Finset.attach (Finset.range t),
          ((p : ℚ_[p])) ^ 2 * ((w i.1 (Finset.mem_range.mp i.2) : ℤ_[p]) : ℚ_[p]) from ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      exact hw i.1 (Finset.mem_range.mp i.2)
    · rw [hW_def]
      simp [PadicInt.coe_sum, Finset.mul_sum]
  rw [mul_sub, ← h_rhs_eq, ← h_split_sum]; push_cast; ring

/-- For an odd prime `p` and even `t ≥ 2`
with `p ∤ (t+1)`, the power sum `∑_{a=0}^{p-1} a^t` is congruent to
`p · B_t` modulo `p²` (viewed in `ℚ_[p]`, with the difference a `p`-adic
integer times `p²`).-/
theorem sum_range_pow_sModEq_p_mul_bernoulli
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {t : ℕ} (ht_two : 2 ≤ t) (ht_even : Even t)
    (h_p_not_dvd_t_plus_one : ¬ (p : ℕ) ∣ (t + 1))
    (ih_pB : ∀ j, j < t -> 2 ≤ j -> Even j ->
      ∃ z : ℤ_[p], (p : ℚ_[p]) * ((bernoulli j : ℚ) : ℚ_[p]) = (z : ℚ_[p])) :
    ∃ z : ℤ_[p],
      ((∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t)) -
          (p : ℚ_[p]) * ((bernoulli t : ℚ) : ℚ_[p]) =
        ((p : ℚ_[p]) ^ 2) * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have htp1_unit : IsUnit ((t + 1 : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr h_p_not_dvd_t_plus_one
  set u : ℤ_[p] := (htp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val with hu_def
  have hu_mul : ((t + 1 : ℕ) : ℤ_[p]) * u = 1 := by
    change ((htp1_unit.unit * htp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1; simp
  have hu_mul_Qp : ((t + 1 : ℕ) : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hu_mul
  obtain ⟨W, hW⟩ := sum_range_pow_sub_p_mul_bernoulli_weighted hp_odd ht_two ht_even ih_pB
  refine ⟨u * W, ?_⟩
  have : ((u : ℤ_[p]) : ℚ_[p]) *
      (((t + 1 : ℕ) : ℚ_[p]) *
        ((∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t) -
          (p : ℚ_[p]) * ((bernoulli t : ℚ) : ℚ_[p]))) =
      ((u : ℤ_[p]) : ℚ_[p]) * ((p : ℚ_[p]) ^ 2 * ((W : ℤ_[p]) : ℚ_[p])) := by
    rw [hW]
  push_cast
  linear_combination this - ((∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t) -
    (p : ℚ_[p]) * ((bernoulli t : ℚ) : ℚ_[p])) * hu_mul_Qp

/-- **Von Staudt–Clausen (unified, restricted to `v_p(k+1) ≤ 2`)**:
every even `k ≥ 2` with `¬ p^3 ∣ (k+1)` we have `p · B_k ∈ ℤ_[p]`. This
subsumes both the classical boundary case `(p-1) ∣ k` (where the naive
statement `B_k ∈ ℤ_[p]` fails) and the generic case `(p-1) ∤ k` (where
the stronger `B_k ∈ ℤ_[p]` is known; multiplying by `p` still holds).
The extra factor of `p` absorbs the potential pole in `B_k`.-/
theorem p_mul_bernoulli_mem_padicInt_restricted
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {k : ℕ} (hk_two : 2 ≤ k) (hk_even : Even k)
    (h_below : ∀ j, j ≤ k -> ¬ (p : ℕ) ^ 3 ∣ (j + 1)) :
    ∃ z : ℤ_[p], (p : ℚ_[p]) * (((bernoulli k : ℚ)) : ℚ_[p]) = (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  have hpQ_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.ne_zero
  revert hk_two hk_even h_below
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk_two hk_even h_below
    have ih_pB : ∀ j, j < k -> 2 ≤ j -> Even j ->
        ∃ z : ℤ_[p], (p : ℚ_[p]) * ((bernoulli j : ℚ) : ℚ_[p]) = (z : ℚ_[p]) := by
      intro j hj hj_two hj_even
      exact ih j hj hj_two hj_even (fun j' hj' => h_below j' (Nat.le_trans hj' hj.le))
    have h_not_pCube : ¬ (p : ℕ) ^ 3 ∣ (k + 1) := h_below k (le_refl k)
    set S_nat : ℕ := ∑ j ∈ Finset.range p, j ^ k with hS_def
    have hS_cast : (∑ j ∈ Finset.range p, (j : ℚ_[p]) ^ k) = ((S_nat : ℕ) : ℚ_[p]) := by
      simp only [hS_def]; push_cast; rfl
    by_cases h_p_dvd : (p : ℕ) ∣ (k + 1)
    · by_cases h_p_sq : (p : ℕ) ^ 2 ∣ (k + 1)
      · obtain ⟨q, hq⟩ := h_p_sq
        have hq_coprime : ¬ (p : ℕ) ∣ q := by
          intro hdvd
          apply h_not_pCube
          rw [hq, pow_succ]
          exact mul_dvd_mul_left (p ^ 2) hdvd
        have hq_unit : IsUnit ((q : ℕ) : ℤ_[p]) := by
          rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
          exact hp.coprime_iff_not_dvd.mpr hq_coprime
        set qInv : ℤ_[p] := (hq_unit.unit⁻¹ : (ℤ_[p])ˣ).val
        have hqInv_mul : ((q : ℕ) : ℤ_[p]) * qInv = 1 := by
          change ((hq_unit.unit * hq_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1; simp
        have hqInv_mul_Qp : ((q : ℕ) : ℚ_[p]) * ((qInv : ℤ_[p]) : ℚ_[p]) = 1 := by
          simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hqInv_mul
        obtain ⟨W, hW⟩ := sum_range_pow_sub_p_mul_bernoulli_weighted hp_odd hk_two hk_even ih_pB
        have h_kp1_eq : ((k + 1 : ℕ) : ℚ_[p]) = (p : ℚ_[p])^2 * ((q : ℕ) : ℚ_[p]) := by
          have : (k + 1 : ℕ) = p^2 * q := hq
          push_cast [this]; ring
        rw [h_kp1_eq] at hW
        have hp_sq_ne : (p : ℚ_[p])^2 ≠ 0 := pow_ne_zero 2 hpQ_ne
        have hW'' : ((q : ℕ) : ℚ_[p]) *
            ((∑ k' ∈ Finset.range p, (k' : ℚ_[p]) ^ k) -
              (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p])) =
            ((W : ℤ_[p]) : ℚ_[p]) :=
          mul_left_cancel₀ hp_sq_ne (by linear_combination hW)
        have h_sub : ((∑ k' ∈ Finset.range p, (k' : ℚ_[p]) ^ k) -
              (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p])) =
            ((qInv : ℤ_[p]) : ℚ_[p]) * ((W : ℤ_[p]) : ℚ_[p]) := by
          linear_combination ((qInv : ℤ_[p]) : ℚ_[p]) * hW'' -
            (((∑ k' ∈ Finset.range p, (k' : ℚ_[p]) ^ k) -
              (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p]))) * hqInv_mul_Qp
        rw [hS_cast] at h_sub
        refine ⟨(S_nat : ℤ_[p]) - qInv * W, ?_⟩
        have h_rearr : (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p]) =
            ((S_nat : ℕ) : ℚ_[p]) -
              ((qInv : ℤ_[p]) : ℚ_[p]) * ((W : ℤ_[p]) : ℚ_[p]) := by
          linear_combination -h_sub
        rw [h_rearr]; push_cast; ring
      · obtain ⟨m', hm'⟩ := h_p_dvd
        have hm'_coprime : ¬ (p : ℕ) ∣ m' := by
          intro hdvd
          apply h_p_sq
          rw [hm', pow_two]
          exact mul_dvd_mul_left p hdvd
        have hm'_unit : IsUnit ((m' : ℕ) : ℤ_[p]) := by
          rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
          exact hp.coprime_iff_not_dvd.mpr hm'_coprime
        set mInv : ℤ_[p] := (hm'_unit.unit⁻¹ : (ℤ_[p])ˣ).val
        have hmInv_mul : ((m' : ℕ) : ℤ_[p]) * mInv = 1 := by
          change ((hm'_unit.unit * hm'_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1; simp
        have hmInv_mul_Qp : ((m' : ℕ) : ℚ_[p]) * ((mInv : ℤ_[p]) : ℚ_[p]) = 1 := by
          simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hmInv_mul
        obtain ⟨W, hW⟩ := sum_range_pow_sub_p_mul_bernoulli_weighted hp_odd hk_two hk_even ih_pB
        have h_kp1_eq : ((k + 1 : ℕ) : ℚ_[p]) = (p : ℚ_[p]) * ((m' : ℕ) : ℚ_[p]) := by
          have : (k + 1 : ℕ) = p * m' := hm'
          push_cast [this]; ring
        rw [h_kp1_eq] at hW
        have hW'' : ((m' : ℕ) : ℚ_[p]) *
            ((∑ k' ∈ Finset.range p, (k' : ℚ_[p]) ^ k) -
              (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p])) =
            (p : ℚ_[p]) * ((W : ℤ_[p]) : ℚ_[p]) :=
          mul_left_cancel₀ hpQ_ne (by linear_combination hW)
        have h_sub : ((∑ k' ∈ Finset.range p, (k' : ℚ_[p]) ^ k) -
              (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p])) =
            ((mInv : ℤ_[p]) : ℚ_[p]) * ((p : ℚ_[p]) * ((W : ℤ_[p]) : ℚ_[p])) := by
          linear_combination ((mInv : ℤ_[p]) : ℚ_[p]) * hW'' -
            (((∑ k' ∈ Finset.range p, (k' : ℚ_[p]) ^ k) -
              (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p]))) * hmInv_mul_Qp
        rw [hS_cast] at h_sub
        refine ⟨(S_nat : ℤ_[p]) - mInv * (p : ℤ_[p]) * W, ?_⟩
        have h_rearr : (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p]) =
            ((S_nat : ℕ) : ℚ_[p]) - ((mInv : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) *
              ((W : ℤ_[p]) : ℚ_[p]) := by
          linear_combination -h_sub
        rw [h_rearr]; push_cast; ring
    · obtain ⟨w, hw⟩ :=
        sum_range_pow_sModEq_p_mul_bernoulli hp_odd hk_two hk_even h_p_dvd ih_pB
      rw [hS_cast] at hw
      refine ⟨(S_nat : ℤ_[p]) - (p : ℤ_[p]) ^ 2 * w, ?_⟩
      have h_rearr : (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p]) =
          ((S_nat : ℕ) : ℚ_[p]) - (p : ℚ_[p]) ^ 2 * ((w : ℤ_[p]) : ℚ_[p]) := by
        linear_combination -hw
      rw [h_rearr]; push_cast; ring

end KummerCriterion

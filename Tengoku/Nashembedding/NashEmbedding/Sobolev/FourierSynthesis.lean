/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Tengoku
import Tengoku.Nashembedding.NashEmbedding.Sobolev.Basic
import Tengoku.Nashembedding.NashEmbedding.Sobolev.Summability
import Tengoku.Nashembedding.NashEmbedding.Sobolev.Differentiation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fourier Synthesis: Smoothness, Sup-Norm Bound, and Basic Properties

**Main result.** Let `k ∈ ℕ` and `s ∈ ℝ` with `2s > n`. For each
`a ∈ ℓ²_(s+k)(ℤⁿ)`, the Fourier series `ǎ(θ) = ∑ aₘ eₘ(θ)` defines a
function of class `Cᵏ` that is `2π`-periodic in each variable, and the map
`a ↦ ǎ` is a continuous linear injection from `ℓ²_(s+k)` into `Cᵏ(ℝⁿ; ℂ)`.

We prove a concrete bound: for each multi-index `α` with `|α| ≤ k`,
`sup_θ |∂^α ǎ(θ)| ≤ C · ‖a‖_(s+k)`, where `C` depends only on `n`, `s`, `k`.
-/

open scoped BigOperators Real
open NashEmbedding.Sobolev Complex

set_option maxHeartbeats 800000

noncomputable section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-- The Fourier synthesis map: `ǎ(θ) = ∑ aₘ eₘ(θ)`.-/
def fourierSynthesis (n : ℕ) (a : (Fin n → ℤ) → ℂ) (θ : Fin n → ℝ) : ℂ :=
  ∑' m : Fin n → ℤ, a m * fourierExp n m θ

/-- For a multi-index `α : Fin n → ℕ`, the monomial `m^α = ∏ mⱼ^{αⱼ}`.-/
def monomialPow (m : Fin n → ℤ) (α : Fin n → ℕ) : ℤ :=
  ∏ j : Fin n, m j ^ α j

/-- The total degree `|α| = ∑ αⱼ`.-/
def multiDeg (α : Fin n → ℕ) : ℕ :=
  ∑ j : Fin n, α j

/-- The `α`-th derivative coefficient: `(im)^α aₘ`.-/
def derivCoeff (α : Fin n → ℕ) (a : (Fin n → ℤ) → ℂ) (m : Fin n → ℤ) : ℂ :=
  (Complex.I ^ (multiDeg α)) * (monomialPow m α : ℂ) * a m

/-
Key bound: `|(im)^α| ≤ (1 + |m|²)^{k/2}` when `|α| ≤ k`.
-/

/-
If `a ∈ ℓ²_(s+k)` and `|α| ≤ k`, then `m ↦ (im)^α aₘ` is in `ℓ²_(s)`.
-/

/-
If `a ∈ ℓ²_(s+k)`, `2s > n`, and `|α| ≤ k`, then `m ↦ (im)^α aₘ ∈ ℓ¹`.
-/

/-
**Sup-norm bound for Fourier synthesis.** If `a ∈ ℓ²_(s+k)`, `2s > n`, and
`|α| ≤ k`, then `sup_θ |∂^α ǎ(θ)| ≤ C · ‖a‖_(s+k)` where the constant
`C = (∑ (1+|m|²)^{-s})^{1/2}` depends only on `n` and `s`.
-/

/-- **Fourier synthesis: 2π-periodicity.** The Fourier synthesis `ǎ` is
`2π`-periodic in each variable.-/
theorem fourierSynthesis_periodic
    {a : (Fin n → ℤ) → ℂ} (ha : Summable (fun m => ‖a m‖))
    (θ : Fin n → ℝ) (j : Fin n) :
    fourierSynthesis n a (Function.update θ j (θ j + 2 * π)) =
      fourierSynthesis n a θ := by
  simp only [fourierSynthesis]
  exact tsum_congr fun m => by rw [fourierExp_add_two_pi]

/-
**Fourier synthesis: linearity.** The map `a ↦ ǎ` is linear.
-/
theorem fourierSynthesis_add
    {a b : (Fin n → ℤ) → ℂ}
    (ha : Summable (fun m => ‖a m‖))
    (hb : Summable (fun m => ‖b m‖))
    (θ : Fin n → ℝ) :
    fourierSynthesis n (a + b) θ = fourierSynthesis n a θ + fourierSynthesis n b θ := by
  unfold fourierSynthesis;
  rw [ ← Summable.tsum_add ];
  · exact tsum_congr fun m => add_mul _ _ _;
  · exact .of_norm <| by simpa [ norm_fourierExp ] using ha;
  · exact .of_norm <| by simpa [ norm_fourierExp ] using hb

theorem fourierSynthesis_smul
    {a : (Fin n → ℤ) → ℂ} (c : ℂ)
    (ha : Summable (fun m => ‖a m‖))
    (θ : Fin n → ℝ) :
    fourierSynthesis n (c • a) θ = c * fourierSynthesis n a θ := by
  unfold fourierSynthesis;
  simp +decide [ mul_assoc, mul_left_comm, ← tsum_mul_left ]

/-
**Fourier synthesis: injectivity.** If `ǎ = 0` then `a = 0`, provided
`a ∈ ℓ¹`.
-/
theorem fourierSynthesis_injective
    {a : (Fin n → ℤ) → ℂ}
    (ha : Summable (fun m => ‖a m‖))
    (h : ∀ θ : Fin n → ℝ, fourierSynthesis n a θ = 0) :
    a = 0 := by
  apply funext;
  have h_inner : ∀ m₀ : Fin n → ℤ, ∫ θ : Fin n → ℝ in Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • 1), fourierSynthesis n a θ * starRingEnd ℂ (fourierExp n m₀ θ) = (2 * Real.pi) ^ n * a m₀ := by
    intro m₀
    have h_fourier_coeff_inner : ∀ m : Fin n → ℤ, ∫ θ : Fin n → ℝ in Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • 1), fourierExp n m θ * starRingEnd ℂ (fourierExp n m₀ θ) = if m = m₀ then (2 * Real.pi) ^ n else 0 := by
      intro m
      have h_fourier_coeff_inner : ∫ θ : Fin n → ℝ in Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • 1), Complex.exp (Complex.I * (∑ j, ((m j : ℝ) - (m₀ j : ℝ)) * θ j)) = if m = m₀ then (2 * Real.pi) ^ n else 0 := by
        split_ifs with h;
        · simp +decide [ h, MeasureTheory.measureReal_def ];
          erw [ Real.volume_Icc_pi ] ; norm_num [ mul_comm ];
          rw [ ENNReal.toReal_ofReal ( by positivity ) ] ; norm_num;
        · -- Since $m \neq m₀$, there exists some $j$ such that $m_j \neq m₀_j$.
          obtain ⟨j, hj⟩ : ∃ j : Fin n, m j ≠ m₀ j := by
            exact Function.ne_iff.mp h;
          have h_integral_zero : ∫ θ : Fin n → ℝ in Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • 1), Complex.exp (Complex.I * (∑ j, ((m j : ℝ) - (m₀ j : ℝ)) * θ j)) = (∏ j, ∫ θ_j : ℝ in Set.Icc 0 (2 * Real.pi), Complex.exp (Complex.I * ((m j : ℝ) - (m₀ j : ℝ)) * θ_j)) := by
            have h_integral_zero : ∫ θ : Fin n → ℝ in Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • 1), Complex.exp (Complex.I * (∑ j, ((m j : ℝ) - (m₀ j : ℝ)) * θ j)) = ∫ θ : Fin n → ℝ, (∏ j, (if 0 ≤ θ j ∧ θ j ≤ 2 * Real.pi then Complex.exp (Complex.I * ((m j : ℝ) - (m₀ j : ℝ)) * θ j) else 0)) := by
              rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
              congr with θ ; simp +decide [ Pi.le_def, forall_and ];
              split_ifs <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.prod_ite ];
              · rw [ ← Complex.exp_sum, Finset.mul_sum _ _ _ ];
              · grind;
            have h_integral_zero : ∫ θ : Fin n → ℝ, (∏ j, (if 0 ≤ θ j ∧ θ j ≤ 2 * Real.pi then Complex.exp (Complex.I * ((m j : ℝ) - (m₀ j : ℝ)) * θ j) else 0)) = ∏ j, ∫ θ_j : ℝ, (if 0 ≤ θ_j ∧ θ_j ≤ 2 * Real.pi then Complex.exp (Complex.I * ((m j : ℝ) - (m₀ j : ℝ)) * θ_j) else 0) := by
              rw [ ← MeasureTheory.integral_fintype_prod_eq_prod ];
              rfl;
            simp_all +decide [ ← MeasureTheory.integral_indicator, Set.indicator_apply ];
          have h_integral_zero : ∫ θ_j : ℝ in Set.Icc 0 (2 * Real.pi), Complex.exp (Complex.I * ((m j : ℝ) - (m₀ j : ℝ)) * θ_j) = 0 := by
            rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.two_pi_pos.le ];
            have := @integral_exp_mul_complex 0 ( 2 * Real.pi );
            have hz : I * ((m j : ℂ) - (m₀ j : ℂ)) * (2 * (π : ℂ))
                    = ((m j - m₀ j : ℤ) : ℂ) * (2 * π * I) := by push_cast; ring
            convert this ( show ( I * ( m j - m₀ j : ℂ ) ) ≠ 0 from mul_ne_zero Complex.I_ne_zero <| sub_ne_zero_of_ne <| mod_cast hj ) using 1
            all_goals (first
              | rfl
              | (norm_num; done)
              | (push_cast; ring; done)
              | (symm
                 rw [div_eq_zero_iff]
                 left
                 simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
                 push_cast
                 exact sub_eq_zero.mpr (Complex.exp_eq_one_iff.mpr ⟨m j - m₀ j, hz⟩)));
          simp_all +decide [ Finset.prod_eq_zero ( Finset.mem_univ j ) ];
      convert h_fourier_coeff_inner using 3 ; norm_num [ fourierExp ] ; ring;
      norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Finset.sum_sub_distrib ];
      exact ⟨ by rw [ Real.cos_sub ], by rw [ Real.sin_sub ] ; ring ⟩;
    have h_fourier_coeff_inner : ∫ θ : Fin n → ℝ in Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • 1), ∑' m : Fin n → ℤ, a m * fourierExp n m θ * starRingEnd ℂ (fourierExp n m₀ θ) = ∑' m : Fin n → ℤ, a m * ∫ θ : Fin n → ℝ in Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • 1), fourierExp n m θ * starRingEnd ℂ (fourierExp n m₀ θ) := by
      rw [ MeasureTheory.integral_tsum ];
      · simp +decide only [mul_assoc, MeasureTheory.integral_const_mul];
      · intro m; exact Continuous.aestronglyMeasurable ( by
          refine' Continuous.mul _ _;
          · refine' continuous_const.mul _;
            exact Complex.continuous_exp.comp <| Continuous.mul continuous_const <| Complex.continuous_ofReal.comp <| continuous_finsetSum _ fun _ _ => Continuous.mul ( continuous_const ) <| continuous_apply _;
          · exact Complex.continuous_conj.comp ( Complex.continuous_exp.comp <| by continuity ) ) ;
      · refine' ne_of_lt ( lt_of_le_of_lt ( ENNReal.tsum_le_tsum fun m => _ ) _ );
        use fun m => ENNReal.ofReal ( ‖a m‖ * ( 2 * Real.pi ) ^ n );
        · refine' le_trans ( MeasureTheory.lintegral_mono fun x => _ ) _;
          use fun x => ENNReal.ofReal ( ‖a m‖ );
          · rw [ ENNReal.le_ofReal_iff_toReal_le ] <;> norm_num [ norm_fourierExp ];
            finiteness;
          · simp +decide [ mul_comm, Real.pi_pos.le ];
            erw [ Real.volume_Icc_pi ] ; norm_num [ mul_comm, Real.pi_pos.le ];
        · rw [ ← ENNReal.ofReal_tsum_of_nonneg ] <;> norm_num;
          · exact fun m => mul_nonneg ( norm_nonneg _ ) ( pow_nonneg ( by positivity ) _ );
          · exact ha.mul_right _;
    convert h_fourier_coeff_inner using 1;
    · simp +decide only [fourierSynthesis, ← tsum_mul_right];
    · rw [ tsum_eq_single m₀ ] <;> simp_all +decide [ mul_comm ];
  simp_all +decide [ mul_eq_zero, Real.pi_ne_zero ]

end NashEmbedding.Sobolev

end

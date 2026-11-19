/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Tengoku
import Tengoku.Nashembedding.NashEmbedding.Sobolev.Basic
import Tengoku.Nashembedding.NashEmbedding.Sobolev.Distribution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sobolev Multiplication on the Torus

This file proves Peetre's inequality and the first Sobolev multiplication
theorem: H^s_{2πℤⁿ}(ℝⁿ) is invariant under multiplication by smooth
periodic functions (represented by their rapidly decaying Fourier
coefficient sequences).

## Main results

* `peetre_weight` — Peetre's inequality for the Sobolev weight function
* `sobolev_mul_seq` — First multiplication theorem (sequence side)
* `smoothMulDistrib` — Distribution-side product definition
* `sobolev_mul_dist` — First multiplication theorem (distribution side)
-/

open scoped BigOperators ComplexConjugate
open Complex Real NashEmbedding.Sobolev

set_option maxHeartbeats 800000

noncomputable section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-! ## Additional weight lemmas -/

/-
The weight is invariant under negation of the index:
`w_t(-m) = w_t(m)`, since `(-m_i)² = m_i²`.
-/

/-! ## Peetre's inequality -/

/-
The base of the weight satisfies a submultiplicative triangle inequality:
`1 + |m|² ≤ 2(1 + |m - j|²)(1 + |j|²)`.

*Proof.* Each coordinate satisfies `m_i² ≤ 2(m_i - j_i)² + 2j_i²`
(expand `((m_i - j_i) + j_i)²` and use AM–QM). Summing gives
`|m|² ≤ 2|m-j|² + 2|j|²`. Then
`1 + 2a + 2b ≤ 2(1 + a)(1 + b)` for `a, b ≥ 0`
(since `2(1+a)(1+b) = 2 + 2a + 2b + 2ab ≥ 1 + 2a + 2b`).
-/

/-
**Peetre's inequality.** For all `s ∈ ℝ` and `m, j ∈ ℤⁿ`:
`weight n s m ≤ 2^|s| · weight n |s| (m - j) · weight n s j`.
-/

/-! ## Translation invariance of tsum -/

/-
Translation invariance: `∑' m, f(m - i) = ∑' m, f(m)`.
-/
lemma tsum_sub_shift
    {f : (Fin n → ℤ) → ℝ} (hf : Summable f) (i : Fin n → ℤ) :
    ∑' m, f (m - i) = ∑' m, f m := by
  conv_rhs => rw [ ← Equiv.tsum_eq ( Equiv.subRight i ) ] ;
  rfl

/-! ## Young's convolution inequality (ℓ¹ ⊛ ℓ²) -/

/-
Summability of the convolution at each point (for non-negative real sequences).
-/
lemma conv_abs_summable
    {f g : (Fin n → ℤ) → ℝ}
    (hf_nn : ∀ m, 0 ≤ f m) (hg_nn : ∀ m, 0 ≤ g m)
    (hf : Summable f) (hg_sq : Summable (fun m => g m ^ 2))
    (m : Fin n → ℤ) :
    Summable (fun i => f i * g (m - i)) := by
  refine' .of_nonneg_of_le ( fun i => mul_nonneg ( hf_nn i ) ( hg_nn _ ) ) ( fun i => _ ) ( hf.mul_right ( Real.sqrt ( ∑' m, g m ^ 2 ) ) );
  exact mul_le_mul_of_nonneg_left ( Real.le_sqrt_of_sq_le ( Summable.le_tsum ( hg_sq ) ( m - i ) ( fun _ _ => sq_nonneg _ ) ) ) ( hf_nn i )

/-
**Young's convolution inequality** for ℓ¹ ⊛ ℓ² on `ℤⁿ`.
If `f ∈ ℓ¹` and `g ∈ ℓ²` are non-negative, then `f ⊛ g ∈ ℓ²` with
`‖f ⊛ g‖_{ℓ²}² ≤ ‖f‖_{ℓ¹}² · ‖g‖_{ℓ²}²`.
-/
theorem young_conv_sq_bound
    {f g : (Fin n → ℤ) → ℝ}
    (hf_nn : ∀ m, 0 ≤ f m) (hg_nn : ∀ m, 0 ≤ g m)
    (hf : Summable f) (hg_sq : Summable (fun m => g m ^ 2)) :
    Summable (fun m => (∑' i, f i * g (m - i)) ^ 2) ∧
    ∑' m, (∑' i, f i * g (m - i)) ^ 2 ≤
      (∑' i, f i) ^ 2 * ∑' m, g m ^ 2 := by
  have h_conv_abs_summable : ∀ m, Summable (fun i => f i * g (m - i)) := by
    intro m
    apply conv_abs_summable hf_nn hg_nn hf hg_sq m;
  have h_cauchy_schwarz : ∀ m, (∑' i, f i * g (m - i)) ^ 2 ≤ (∑' i, f i) * (∑' i, f i * g (m - i) ^ 2) := by
    intro m;
    have h_cauchy_schwarz : ∀ (u v : (Fin n → ℤ) → ℝ), (∀ i, 0 ≤ u i) → (∀ i, 0 ≤ v i) → Summable (fun i => u i) → Summable (fun i => u i * v i ^ 2) → (∑' i, u i * v i) ^ 2 ≤ (∑' i, u i) * (∑' i, u i * v i ^ 2) := by
      intros u v hu hv hu_sum hv_sum
      have h_cauchy_schwarz : ∀ (N : Finset (Fin n → ℤ)), (∑ i ∈ N, u i * v i) ^ 2 ≤ (∑ i ∈ N, u i) * (∑ i ∈ N, u i * v i ^ 2) := by
        intro N;
        have h_cauchy_schwarz : ∀ (u v : (Fin n → ℤ) → ℝ), (∀ i, 0 ≤ u i) → (∀ i, 0 ≤ v i) → (∑ i ∈ N, u i * v i) ^ 2 ≤ (∑ i ∈ N, u i) * (∑ i ∈ N, u i * v i ^ 2) := by
          intros u v hu hv
          have h_cauchy_schwarz : ∀ (i j : Fin n → ℤ), u i * v i * u j * v j ≤ (u i * u j * v i ^ 2 + u i * u j * v j ^ 2) / 2 := by
            exact fun i j => by nlinarith only [ sq_nonneg ( v i - v j ), mul_nonneg ( hu i ) ( hu j ), mul_nonneg ( hu i ) ( hv j ), mul_nonneg ( hv i ) ( hu j ), mul_nonneg ( hv i ) ( hv j ) ] ;
          have h_cauchy_schwarz : ∑ i ∈ N, ∑ j ∈ N, u i * v i * u j * v j ≤ ∑ i ∈ N, ∑ j ∈ N, (u i * u j * v i ^ 2 + u i * u j * v j ^ 2) / 2 := by
            exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => h_cauchy_schwarz i j;
          convert h_cauchy_schwarz using 1 <;> norm_num [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ← Finset.sum_div ] ; ring;
          · simp +decide only [sq, Finset.mul_sum _ _ _, mul_comm, mul_left_comm];
          · simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, Finset.sum_add_distrib ] ; ring;
            simp +decide [ mul_assoc, Finset.mul_sum _ _ _ ] ; ring;
        exact h_cauchy_schwarz u v hu hv;
      have h_cauchy_schwarz : Filter.Tendsto (fun N : Finset (Fin n → ℤ) => (∑ i ∈ N, u i * v i) ^ 2) Filter.atTop (nhds ((∑' i, u i * v i) ^ 2)) := by
        refine' Filter.Tendsto.pow _ _;
        refine' Summable.hasSum _;
        have h_cauchy_schwarz : Summable (fun i => u i * v i) := by
          have h_cauchy_schwarz : ∀ i, u i * v i ≤ u i + u i * v i ^ 2 := by
            exact fun i => by nlinarith only [ hu i, hv i, sq_nonneg ( v i - 1 ) ] ;
          exact Summable.of_nonneg_of_le ( fun i => mul_nonneg ( hu i ) ( hv i ) ) h_cauchy_schwarz ( hu_sum.add hv_sum );
        exact h_cauchy_schwarz;
      exact le_of_tendsto_of_tendsto' h_cauchy_schwarz ( Filter.Tendsto.mul ( hu_sum.hasSum ) ( hv_sum.hasSum ) ) fun N => by aesop;
    apply h_cauchy_schwarz f (fun i => g (m - i)) hf_nn (fun i => hg_nn (m - i)) hf;
    refine' .of_nonneg_of_le ( fun i => mul_nonneg ( hf_nn i ) ( sq_nonneg _ ) ) ( fun i => mul_le_mul_of_nonneg_left ( show g ( m - i ) ^ 2 ≤ ∑' j, g j ^ 2 from _ ) ( hf_nn i ) ) ( hf.mul_right _ );
    exact Summable.le_tsum ( hg_sq ) ( m - i ) ( fun _ _ => sq_nonneg _ );
  have h_fubini : ∑' m, ∑' i, f i * g (m - i) ^ 2 = ∑' i, f i * ∑' m, g (m - i) ^ 2 := by
    rw [ Summable.tsum_comm ];
    · simp +decide only [← tsum_mul_left];
    · have h_fubini : Summable (fun p : (Fin n → ℤ) × (Fin n → ℤ) => f p.1 * g p.2 ^ 2) := by
        exact .of_norm <| by simpa using Summable.mul_norm ( hf.norm ) ( hg_sq.norm ) ;
      convert h_fubini.comp_injective ( show Function.Injective ( fun p : ( Fin n → ℤ ) × ( Fin n → ℤ ) => ( p.1, p.2 - p.1 ) ) from fun p q h => by aesop ) using 1
      funext p; simp [Function.uncurry, Function.comp]
  have h_translation_invariance : ∀ i, ∑' m, g (m - i) ^ 2 = ∑' m, g m ^ 2 := by
    exact fun i => Equiv.tsum_eq ( Equiv.subRight i ) fun m => g m ^ 2;
  simp_all +decide [ tsum_mul_right, tsum_mul_left ];
  refine' ⟨ _, _ ⟩;
  · refine' Summable.of_nonneg_of_le ( fun m => sq_nonneg _ ) ( fun m => h_cauchy_schwarz m ) _;
    refine' Summable.mul_left _ _;
    contrapose! h_fubini;
    rw [ tsum_eq_zero_of_not_summable h_fubini ] ; norm_num;
    constructor;
    · intro H;
      have h_zero : ∀ m, f m = 0 := by
        exact fun m => le_antisymm ( le_trans ( Summable.le_tsum ( hf ) m ( fun _ _ => hf_nn _ ) ) H.le ) ( hf_nn m );
      exact h_fubini <| by simpa [ h_zero ] using summable_zero;
    · intro H; simp_all +decide [ tsum_eq_zero_of_not_summable ] ;
      -- Since $\sum' m, g m ^ 2 = 0$, we have $g m = 0$ for all $m$.
      have h_g_zero : ∀ m, g m = 0 := by
        exact fun m => sq_eq_zero_iff.mp ( le_antisymm ( le_trans ( Summable.le_tsum ( hg_sq ) m ( fun _ _ => sq_nonneg _ ) ) H.le ) ( sq_nonneg _ ) );
      exact h_fubini <| by simpa [ h_g_zero ] using summable_zero;
  · refine' le_trans ( Summable.tsum_le_tsum h_cauchy_schwarz _ _ ) _;
    · refine' Summable.of_nonneg_of_le ( fun m => sq_nonneg _ ) ( fun m => h_cauchy_schwarz m ) _;
      refine' Summable.mul_left _ _;
      contrapose! h_fubini;
      rw [ tsum_eq_zero_of_not_summable h_fubini ] ; norm_num;
      constructor;
      · intro H;
        have h_zero : ∀ m, f m = 0 := by
          exact fun m => le_antisymm ( le_trans ( Summable.le_tsum ( hf ) m ( fun _ _ => hf_nn _ ) ) H.le ) ( hf_nn m );
        exact h_fubini <| by simpa [ h_zero ] using summable_zero;
      · intro H; simp_all +decide [ tsum_eq_zero_of_not_summable ] ;
        -- Since $\sum' m, g m ^ 2 = 0$, we have $g m = 0$ for all $m$.
        have h_g_zero : ∀ m, g m = 0 := by
          exact fun m => sq_eq_zero_iff.mp ( le_antisymm ( le_trans ( Summable.le_tsum ( hg_sq ) m ( fun _ _ => sq_nonneg _ ) ) H.le ) ( sq_nonneg _ ) );
        exact h_fubini <| by simpa [ h_g_zero ] using summable_zero;
    · refine' Summable.mul_left _ _;
      contrapose! h_fubini;
      rw [ tsum_eq_zero_of_not_summable h_fubini ] ; norm_num;
      constructor <;> intro h <;> simp_all +decide [ tsum_eq_zero_of_not_summable ];
      · -- Since $f$ is non-negative and its sum is zero, $f$ must be zero everywhere.
        have h_f_zero : ∀ m, f m = 0 := by
          exact fun m => le_antisymm ( le_trans ( Summable.le_tsum ( hf ) m ( fun _ _ => hf_nn _ ) ) h.le ) ( hf_nn m );
        exact h_fubini <| by simpa [ h_f_zero ] using summable_zero;
      · -- Since $\sum' m, g m ^ 2 = 0$, we have $g m = 0$ for all $m$.
        have h_g_zero : ∀ m, g m = 0 := by
          exact fun m => sq_eq_zero_iff.mp ( le_antisymm ( le_trans ( Summable.le_tsum ( hg_sq ) m ( fun _ _ => sq_nonneg _ ) ) h.le ) ( sq_nonneg _ ) );
        exact h_fubini <| by simpa [ h_g_zero ] using summable_zero;
    · rw [ tsum_mul_left, h_fubini, sq, mul_assoc ]

/-! ## First Sobolev multiplication theorem (sequence side) -/

/-
**First Sobolev multiplication theorem (sequence side).**
If `a ∈ ℓ²_{(s)}(ℤⁿ)` and the sequence `b` satisfies the weighted ℓ¹ condition
`∑ ‖b_i‖ · (1 + |i|²)^{|s|/2} < ∞`, then the convolution `b ⊛ a` belongs to
`ℓ²_{(s)}(ℤⁿ)` and satisfies the norm bound
`‖b ⊛ a‖_{(s)} ≤ 2^{|s|/2} · (∑ ‖b_i‖ · (1 + |i|²)^{|s|/2}) · ‖a‖_{(s)}`.
-/

/-! ## Distribution-side multiplication -/

/-- Multiplication of a distribution `φ ∈ X_n^*` by a sequence `b : ℤⁿ → ℂ`
of Fourier coefficients (representing a smooth periodic function).
The product is defined via convolution on the Fourier side:
`(b · φ)^_m = ∑_i b_i · φ̂_{m-i}`.-/
def smoothMulDistrib (n : ℕ) (b : (Fin n → ℤ) → ℂ) (φ : TrigPolyDual n) :
    TrigPolyDual n :=
  seqToDual n (fun m => ∑' i, b i * fourierCoeffDistrib φ (m - i))

/-- The Fourier coefficients of the product distribution are the convolution
of `b` with the Fourier coefficients of `φ`.-/
lemma fourierCoeffDistrib_smoothMulDistrib (b : (Fin n → ℤ) → ℂ) (φ : TrigPolyDual n) :
    fourierCoeffDistrib (smoothMulDistrib n b φ) =
      fun m => ∑' i, b i * fourierCoeffDistrib φ (m - i) :=
  fourierCoeffDistrib_seqToDual _

end NashEmbedding.Sobolev

end

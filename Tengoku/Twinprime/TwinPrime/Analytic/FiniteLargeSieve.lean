import Tengoku.Twinprime.TwinPrime.Analytic.AdditiveKernel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A finite large-sieve inequality from Gram row sums

A nonnegative symmetric kernel satisfies the elementary Schur bound. Applied
to the absolute values of a Gram matrix, this bounds synthesis of a finite
family of vectors. Cauchy--Schwarz duality then gives the corresponding
large-sieve estimate for the sum of squared correlations.

The row condition is an explicit finite inequality. This file does not assert
that a family of separated frequencies satisfies any particular row bound.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

/-- The finite Schur bound, using only symmetry, positivity and row sums.
@isnad1 id=le.3h5v.s7.173762596d57 from=translated src=- shape=c0db1296 vocab=261e16a0
-/
theorem finite_schur_bound {ι : Type*} (s : Finset ι) (K : ι → ι → ℝ)
    (w : ι → ℝ) (B : ℝ)
    (hK : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ K i j)
    (hsym : ∀ i ∈ s, ∀ j ∈ s, K i j = K j i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, K i j ≤ B) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * K i j) ≤ B * ∑ i ∈ s, (w i) ^ 2 := by
  have hswap : (∑ i ∈ s, ∑ j ∈ s, (w j) ^ 2 * K j i) =
      ∑ i ∈ s, ∑ j ∈ s, (w i) ^ 2 * K i j := by rw [sum_comm]
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s,
        ((w i) ^ 2 * K i j + (w j) ^ 2 * K j i) / 2 := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      rw [← hsym i hi j hj]
      nlinarith [mul_nonneg (hK i hi j hj) (sq_nonneg (w i - w j))]
    _ = ((∑ i ∈ s, ∑ j ∈ s, (w i) ^ 2 * K i j) +
        ∑ i ∈ s, ∑ j ∈ s, (w j) ^ 2 * K j i) / 2 := by
      simp only [div_eq_mul_inv, add_mul, sum_add_distrib, ← sum_mul]
    _ = ∑ i ∈ s, ∑ j ∈ s, (w i) ^ 2 * K i j := by rw [hswap]; ring
    _ = ∑ i ∈ s, (w i) ^ 2 * ∑ j ∈ s, K i j := by simp only [mul_sum]
    _ ≤ ∑ i ∈ s, (w i) ^ 2 * B :=
      sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
    _ = _ := by rw [← sum_mul]; ring

section InnerProduct

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The synthesis estimate associated with a finite absolute Gram row bound.
@isnad1 id=le.1h6v.s8.989219c6035e from=translated src=- shape=03725bda vocab=5c8c4a2a
-/
theorem norm_sum_smul_sq_le_gram_row (s : Finset ι) (v : ι → H)
    (b : ι → ℂ) (B : ℝ)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, ‖inner ℂ (v i) (v j)‖ ≤ B) :
    ‖∑ i ∈ s, b i • v i‖ ^ 2 ≤ B * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  calc
    _ = ‖inner ℂ (∑ i ∈ s, b i • v i) (∑ j ∈ s, b j • v j)‖ := by
      simp [inner_self_eq_norm_sq_to_K]
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖inner ℂ (b i • v i) (b j • v j)‖ := by
      rw [sum_inner]
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro i _
      rw [inner_sum]
      exact norm_sum_le _ _
    _ = ∑ i ∈ s, ∑ j ∈ s, ‖b i‖ * ‖b j‖ * ‖inner ℂ (v i) (v j)‖ := by
      simp [mul_assoc, mul_comm, mul_left_comm]
    _ ≤ _ := finite_schur_bound s (fun i j => ‖inner ℂ (v i) (v j)‖)
      (fun i => ‖b i‖) B (fun _ _ _ _ => norm_nonneg _)
      (fun i _ j _ => norm_inner_symm _ _) hrow

/-- A finite large-sieve inequality; the family need not be orthogonal.
@isnad1 id=le.2h6v.s8.89750b1cd710 from=translated src=- shape=6a2076f0 vocab=f5dc72b4
-/
theorem sum_norm_inner_sq_le_gram_row (s : Finset ι) (v : ι → H)
    (x : H) (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, ‖inner ℂ (v i) (v j)‖ ≤ B) :
    (∑ i ∈ s, ‖inner ℂ (v i) x‖ ^ 2) ≤ B * ‖x‖ ^ 2 := by
  let S : ℝ := ∑ i ∈ s, ‖inner ℂ (v i) x‖ ^ 2
  let u : H := ∑ i ∈ s, inner ℂ (v i) x • v i
  have hS : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hu : ‖u‖ ^ 2 ≤ B * S := norm_sum_smul_sq_le_gram_row s v
    (fun i => inner ℂ (v i) x) B hrow
  have heq : inner ℂ u x = (S : ℂ) := by
    simp only [u, S, sum_inner, inner_smul_left, Complex.conj_mul', Complex.ofReal_sum,
      Complex.ofReal_pow]
  have hnorm : ‖inner ℂ u x‖ = S := by
    rw [heq, Complex.norm_real, Real.norm_of_nonneg hS]
  have hcs : S ^ 2 ≤ ‖u‖ ^ 2 * ‖x‖ ^ 2 := by
    have h := norm_inner_le_norm u x (𝕜 := ℂ)
    rw [hnorm] at h
    exact (pow_le_pow_left₀ hS h 2).trans_eq (mul_pow _ _ _)
  have hsquare : S ^ 2 ≤ (B * S) * ‖x‖ ^ 2 :=
    hcs.trans (mul_le_mul_of_nonneg_right hu (sq_nonneg _))
  change S ≤ B * ‖x‖ ^ 2
  rcases eq_or_lt_of_le hS with hzero | hpos
  · rw [← hzero]
    positivity
  · apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith [hsquare]

end InnerProduct

/-- The complex-matrix form, with a finite sample type and arbitrary finite
frequency set. The orientation agrees with `Σ a(n) E(i,n)`.
@isnad1 id=le.2h6v.s7.1832094aad43 from=translated src=- shape=25be0e12 vocab=933662c5
-/
theorem finite_large_sieve {ι κ : Type*} [Fintype κ] (s : Finset ι)
    (E : ι → κ → ℂ) (a : κ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i ∈ s, ∑ j ∈ s,
      ‖∑ n : κ, E i n * starRingEnd ℂ (E j n)‖ ≤ B) :
    (∑ i ∈ s, ‖∑ n : κ, a n * E i n‖ ^ 2) ≤ B * ∑ n : κ, ‖a n‖ ^ 2 := by
  let v : ι → EuclideanSpace ℂ κ := fun i => WithLp.toLp 2
    (fun n => starRingEnd ℂ (E i n))
  let x : EuclideanSpace ℂ κ := WithLp.toLp 2 a
  have hv : ∀ i j, inner ℂ (v i) (v j) =
      ∑ n : κ, E i n * starRingEnd ℂ (E j n) := by
    intro i j
    simp [v, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hx : ∀ i, inner ℂ (v i) x = ∑ n : κ, a n * E i n := by
    intro i
    simp [v, x, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hnorm : ‖x‖ ^ 2 = ∑ n : κ, ‖a n‖ ^ 2 := by
    simp [x, EuclideanSpace.norm_sq_eq]
  have h := sum_norm_inner_sq_le_gram_row s v x B hB (by simpa only [hv] using hrow)
  simpa only [hx, hnorm] using h

/-- Both the frequency set and the sample set may be arbitrary finsets.
@isnad1 id=le.2h7v.s7.5030616e7a98 from=translated src=- shape=1119a489 vocab=0db9294a
-/
theorem finite_large_sieve_finset {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (E : ι → κ → ℂ) (a : κ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i ∈ s, ∑ j ∈ s,
      ‖∑ n ∈ t, E i n * starRingEnd ℂ (E j n)‖ ≤ B) :
    (∑ i ∈ s, ‖∑ n ∈ t, a n * E i n‖ ^ 2) ≤ B * ∑ n ∈ t, ‖a n‖ ^ 2 := by
  have hrow' : ∀ i ∈ s, ∑ j ∈ s,
      ‖∑ n : t, E i n * starRingEnd ℂ (E j n)‖ ≤ B := by
    intro i hi
    convert hrow i hi using 1
    congr 1
    ext j
    rw [Finset.sum_coe_sort t (fun n => E i n * starRingEnd ℂ (E j n))]
  have h := finite_large_sieve (κ := t) s (fun i n => E i n) (fun n => a n) B hB hrow'
  convert h using 1
  · congr 1
    ext i
    rw [Finset.sum_coe_sort t (fun n => a n * E i n)]
  · rw [Finset.sum_coe_sort t (fun n => ‖a n‖ ^ 2)]

/-- The additive-phase specialization, ready for a geometric row estimate.
@isnad1 id=le.2h7v.s7.ae349365443a from=translated src=- shape=d5e0d9d4 vocab=6241d872
-/
theorem finite_additive_large_sieve_of_kernel_rows {ι : Type*} (s : Finset ι)
    (θ : ι → ℝ) (a : ℕ → ℂ) (M N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i ∈ s, ∑ j ∈ s,
      ‖∑ n ∈ Ico M N, additivePhase (n * (θ i - θ j))‖ ≤ B) :
    (∑ i ∈ s, ‖∑ n ∈ Ico M N, a n * additivePhase (n * θ i)‖ ^ 2) ≤
      B * ∑ n ∈ Ico M N, ‖a n‖ ^ 2 := by
  apply finite_large_sieve_finset s (Ico M N) (fun i n => additivePhase (n * θ i)) a B hB
  simpa only [sum_Ico_phase_mul_conj_eq] using hrow

end TwinPrime.Analytic

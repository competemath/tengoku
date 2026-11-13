import Tengoku.Nlalib.NLAlib.RandomMatrix.Gaussian.Wishart.SoftMin.GramSoftMin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Growth bounds for inverse-power Gram derivatives

Trace/Frobenius estimates bound the explicit inverse-power Hessian and provide
fixed-regularization polynomial dominators for Gaussian integration by parts.
Source: operator hard-edge derivation, atlas wishart-lambda-min-tail.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A trace power-product with two copies of the same direction is bounded by
spectral powers times the squared Frobenius direction size. Source: Frobenius
Cauchy--Schwarz; atlas wishart-lambda-min-tail (Hessian growth helper).
@isnad1 id=le.0h5v.s7.11f599990766 from=translated src=- shape=a31bf931 vocab=c5ab3bec
-/
theorem abs_trace_pow_mul_mul_pow_mul_le (R B : Matrix ι ι ℝ) (p q : ℕ) :
    |Matrix.trace (R ^ p * B * R ^ q * B)| ≤
      specNorm R ^ (p + q) * frobSq B := by
  cases isEmpty_or_nonempty ι with
  | inl hι => simp [Matrix.trace, Matrix.diag, frobSq, frobInner]
  | inr hι =>
    have htrace : Matrix.trace (R ^ p * B * R ^ q * B) =
        frobInner (R ^ p * B)ᵀ (R ^ q * B) := by
      rw [frobInner_eq_trace, RCLike.re_to_real,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
      simp only [Matrix.mul_assoc]
    have hp : specNorm (R ^ p) ≤ specNorm R ^ p := by
      simp only [specNorm_eq_norm]
      exact norm_pow_le R p
    have hq : specNorm (R ^ q) ≤ specNorm R ^ q := by
      simp only [specNorm_eq_norm]
      exact norm_pow_le R q
    have hfp : frobNorm (R ^ p * B) ≤ specNorm R ^ p * frobNorm B :=
      (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans
        (mul_le_mul_of_nonneg_right hp (frobNorm_nonneg B))
    have hfq : frobNorm (R ^ q * B) ≤ specNorm R ^ q * frobNorm B :=
      (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans
        (mul_le_mul_of_nonneg_right hq (frobNorm_nonneg B))
    rw [htrace]
    calc
      _ ≤ frobNorm (R ^ p * B) * frobNorm (R ^ q * B) := by
        simpa only [frobNorm_transpose] using
          abs_frobInner_le_frobNorm_mul_frobNorm (R ^ p * B)ᵀ (R ^ q * B)
      _ ≤ (specNorm R ^ p * frobNorm B) * (specNorm R ^ q * frobNorm B) :=
        mul_le_mul hfp hfq (frobNorm_nonneg _) (mul_nonneg
          (pow_nonneg (specNorm_nonneg R) _) (frobNorm_nonneg B))
      _ = _ := by rw [pow_add, ← frobNorm_sq B]; ring

/-- The inverse-power Hessian kernel has an explicit spectral/Frobenius norm bound.
Source: summing the trace product bound; atlas wishart-lambda-min-tail
(Hessian growth helper).
@isnad1 id=le.0h4v.s6.3f2d5b961935 from=translated src=- shape=3804edba vocab=865f320d
-/
theorem abs_inversePowerHessianKernel_le (R B : Matrix ι ι ℝ) (n : ℕ) :
    |inversePowerHessianKernel R B n| ≤
      ((n : ℝ) + 1) * specNorm R ^ (n + 2) * frobSq B := by
  unfold inversePowerHessianKernel
  calc
    _ ≤ ∑ a ∈ Finset.range (n + 1),
        |Matrix.trace (R ^ (n - a + 1) * B * R ^ (a + 1) * B)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ Finset.range (n + 1), specNorm R ^ (n + 2) * frobSq B := by
      apply Finset.sum_le_sum
      intro a ha
      have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      simpa only [show n - a + 1 + (a + 1) = n + 2 by omega] using
        abs_trace_pow_mul_mul_pow_mul_le R B (n - a + 1) (a + 1)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one]; ring

omit [DecidableEq κ] in
/-- Positive Gram regularization bounds the inverse spectral norm by its scalar
regularization reciprocal. Source: a top inverse eigenvector and the regularized
Gram quadratic form; atlas wishart-lambda-min-tail (growth helper).
@isnad1 id=le.1h4v.s6.cc829121b224 from=translated src=- shape=d85c08c6 vocab=67a81810
-/
theorem specNorm_inv_regularizedGram_le [Nonempty ι] (ε : ℝ) (hε : 0 < ε)
    (G : Matrix ι κ ℝ) :
    specNorm (regularizedGram ε G)⁻¹ ≤ ε⁻¹ := by
  let A := regularizedGram ε G
  have hA : A.PosDef := regularizedGram_posDef hε G
  obtain ⟨v, hv, heig⟩ := exists_unit_mulVec_eq_specNorm_smul hA.inv.posSemidef
  have hmul : A * A⁻¹ = 1 :=
    Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  have heq : specNorm A⁻¹ * (v ⬝ᵥ (A *ᵥ v)) = 1 := by
    have hh : A *ᵥ (A⁻¹ *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
    rw [heig, Matrix.mulVec_smul] at hh
    have h := congrArg (fun w => v ⬝ᵥ w) hh
    simpa only [dotProduct_smul, smul_eq_mul, hv] using h
  have hG : (G * Gᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose G
  have hpos := hG.dotProduct_mulVec_nonneg v
  simp only [star_trivial] at hpos
  have hquad : ε ≤ v ⬝ᵥ (A *ᵥ v) := by
    dsimp [A, regularizedGram]
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul, hv, mul_one]
    linarith
  have hεs : ε * specNorm A⁻¹ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hquad (specNorm_nonneg A⁻¹)
    rw [heq] at hh
    simpa only [mul_comm] using hh
  rw [← one_div ε]
  exact (le_div_iff₀ hε).mpr (by simpa only [mul_comm] using hεs)

/-- A coordinate Gram direction has squared Frobenius size at most four times the
input size. Source: the Frobenius triangle and product inequalities;
atlas wishart-lambda-min-tail (growth helper).
@isnad1 id=other.0h5v.s7.6fb62d59c098 from=translated src=- shape=931194ad vocab=dad6bc5d
-/
theorem frobSq_single_gram_direction_le (G : Matrix ι κ ℝ) (i : ι) (j : κ) :
    let E : Matrix ι κ ℝ := Matrix.single i j 1
    frobSq (E * Gᵀ + G * Eᵀ) ≤ 4 * frobSq G := by
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  have hEsq : frobSq E = 1 := by
    simp [E, frobSq, frobInner, Matrix.single, ite_and]
  have hE : frobNorm E = 1 := by
    rw [frobNorm, hEsq]
    norm_num
  have h1 : frobNorm (E * Gᵀ) ≤ frobNorm G := by
    simpa only [frobNorm_transpose, hE, one_mul] using frobNorm_mul_le E Gᵀ
  have h2 : frobNorm (G * Eᵀ) ≤ frobNorm G := by
    simpa only [frobNorm_transpose, hE, mul_one] using frobNorm_mul_le G Eᵀ
  have hnorm := (frobNorm_add_le (E * Gᵀ) (G * Eᵀ)).trans (add_le_add h1 h2)
  change frobSq (E * Gᵀ + G * Eᵀ) ≤ _
  nlinarith [frobNorm_nonneg (E * Gᵀ + G * Eᵀ), frobNorm_nonneg G,
    frobNorm_sq (E * Gᵀ + G * Eᵀ), frobNorm_sq G]

omit [DecidableEq κ] in
/-- The trace of a regularized Gram matrix is its squared Frobenius size plus
the scalar regularization times the row dimension. Source: trace cyclicity;
atlas wishart-lambda-min-tail (growth helper).
@isnad1 id=eq.0h4v.s5.ec3e3892ca0e from=translated src=- shape=81fffb74 vocab=3401bf4b
-/
theorem trace_regularizedGram_eq (ε : ℝ) (G : Matrix ι κ ℝ) :
    Matrix.trace (regularizedGram ε G) = frobSq G + ε * Fintype.card ι := by
  unfold regularizedGram
  rw [Matrix.trace_add, Matrix.trace_smul]
  simp only [smul_eq_mul, Matrix.trace_one]
  have hh : Matrix.trace (G * Gᵀ) = frobSq G := by
    rw [frobSq, frobInner_eq_trace, RCLike.re_to_real,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.trace_mul_comm]
  rw [hh]

end NLAlib

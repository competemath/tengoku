import Tengoku.Seed.Analysis.CStarAlgebra.Matrix
import Tengoku.Seed.LinearAlgebra.Matrix.DotProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Frobenius inner product and norm

* `NLAlib.frobInner`, `NLAlib.frobSq`, `NLAlib.frobNorm`: the Frobenius inner product, its
 squared norm and the norm, over any `RCLike` field `𝕜`. The inner product is the real part
 `⟨A, B⟩_F = Re ∑ᵢⱼ conj(Aᵢⱼ) Bᵢⱼ = Re tr(AᴴB)`, the inner product of the underlying real
 Hilbert space (Mathlib's `real_inner`); the `𝕜`-valued pairing is `(Aᴴ * B).trace`. Over `ℝ`
 every definition is the old explicit sum by `rfl` (`frobInner_eq_sum_mul`).

## Contents

* Algebra of `frobInner` (bilinearity over real scalars, symmetry, trace forms
 `Re tr(AᴴB) = Re tr(ABᴴ)`, transpose and conjugate transpose).
* `frobSq` / `frobNorm`: `‖A‖_F² = ∑ᵢⱼ |Aᵢⱼ|²`, nonnegativity, definiteness, expansion of
 `frobSq (A ± B)`, Pythagoras, Cauchy–Schwarz, triangle inequality, transpose, `‖I‖_F² = n`.
* Rows: `‖A‖_F² = ∑ᵢ ‖Aᵢ‖²`, `‖Av‖² = ∑ᵢ (Aᵢ ⬝ v)²`, `‖Av‖² = v*(AᴴA)v`, `v ⬝ v ≥ 0`,
 `‖Bx‖² ≤ ‖B‖_F² ‖x‖²`.
* Products: `⟨PX, QY⟩_F = ⟨X, PᴴQY⟩_F` and invariance under multiplication by matrices with
 orthonormal columns (stated with the raw hypothesis `Qᴴ * Q = 1`, which is
 `NLAlib.HasOrthonormalCols Q` by definition).

Statements are written with `ᴴ` and `star`; real users get `ᵀ` from the simp lemma
`Matrix.conjTranspose_eq_transpose_of_trivial` (foundation change F1; the real `ᵀ` corollaries of
the RCLike round are removed, see `docs/renames/2026-10-F1.json`). Mathlib's Frobenius norm
(`Matrix.frobeniusNormedAddCommGroup`, scope `Matrix.Norms.Frobenius`) is `frobNorm` by
`frobNorm_eq_norm`. The spectral norm and the mixed inequalities are in
`NLAlib.Matrix.Norms.Core`, which imports this file.

The Frobenius algebra is ported from the LRA project (`LRA/Basic.lean`,
`LRA/Deterministic/RangeFinder.lean`, Chen–Persson formalization), namespace renamed.

Atlas: `matrix-norms-def`, `norms-frob-spec`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

/-! ### Definitions -/

/-- Frobenius inner product `⟨A, B⟩_F = Re ∑ᵢⱼ conj(Aᵢⱼ) Bᵢⱼ = Re tr(AᴴB)`; over `ℝ` it is
`∑ᵢⱼ Aᵢⱼ Bᵢⱼ` (`frobInner_eq_sum_mul`).
atlas: matrix-norms-def-/
def frobInner (A B : Matrix m n 𝕜) : ℝ := RCLike.re (∑ i, ∑ j, star (A i j) * B i j)

/-- Squared Frobenius norm `‖A‖_F²`.
atlas: matrix-norms-def-/
def frobSq (A : Matrix m n 𝕜) : ℝ := frobInner A A

/-- Frobenius norm `‖A‖_F`.
atlas: matrix-norms-def-/
def frobNorm (A : Matrix m n 𝕜) : ℝ := Real.sqrt (frobSq A)

/-- Over `ℝ` the Frobenius inner product is the plain entrywise sum (definitional).
@isnad1 id=eq.0h4v.s6.6d95e17c02d8 from=translated src=- shape=3ab6e358 vocab=0d3bae3a
-/
theorem frobInner_eq_sum_mul (A B : Matrix m n ℝ) : frobInner A B = ∑ i, ∑ j, A i j * B i j :=
  rfl

/-- `⟨A, B⟩_F = ∑ᵢⱼ Re(conj(Aᵢⱼ) Bᵢⱼ)`.
@isnad1 id=eq.0h5v.s7.6ede1c9634ff from=translated src=- shape=008d5a1d vocab=3556f3fd
-/
theorem frobInner_eq_sum_re (A B : Matrix m n 𝕜) :
    frobInner A B = ∑ i, ∑ j, RCLike.re (star (A i j) * B i j) := by
  simp only [frobInner, map_sum]

/-! ### Algebra of the Frobenius inner product -/

/-- Symmetry of `⟨·,·⟩_F`. Standard; atlas `norms-frob-spec`.
@isnad1 id=eq.0h5v.s5.2a5163780b9a from=translated src=- shape=f304a0e5 vocab=997d772c
-/
theorem frobInner_comm (A B : Matrix m n 𝕜) : frobInner A B = frobInner B A := by
  unfold frobInner
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← RCLike.conj_re (star (B i j) * A i j), ← RCLike.star_def, star_mul, star_star]

/-- Trace form `⟨A, B⟩_F = Re tr(AᴴB)` (over `ℝ`, `tr(AᵀB)` after `simp`). Standard; atlas
`norms-frob-spec`.
@isnad1 id=eq.0h5v.s8.5c16cbd9834b from=translated src=- shape=8acd22c3 vocab=f3e77bec
-/
theorem frobInner_eq_trace (A B : Matrix m n 𝕜) :
    frobInner A B = RCLike.re (Aᴴ * B).trace := by
  unfold frobInner Matrix.trace
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

/-- The Frobenius pairing is also the real part of the trace of the row cross-product,
`⟨A, B⟩_F = Re tr(ABᴴ)`. Horn–Johnson §7.4.
@isnad1 id=eq.0h5v.s8.743aa384c089 from=translated src=- shape=36828239 vocab=f3e77bec
-/
theorem frobInner_eq_re_trace_mul_conjTranspose (A B : Matrix m n 𝕜) :
    frobInner A B = RCLike.re (A * Bᴴ).trace := by
  rw [frobInner_comm, frobInner_eq_trace, Matrix.trace_mul_comm]

/-- Additivity in the first argument. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h6v.s6.2b2c8ca11069 from=translated src=- shape=61aa74a0 vocab=0ab66b83
-/
theorem frobInner_add_left (A B C : Matrix m n 𝕜) :
    frobInner (A + B) C = frobInner A C + frobInner B C := by
  unfold frobInner
  simp [add_mul, Finset.sum_add_distrib]

/-- Additivity in the second argument. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h6v.s6.26468d1e5d62 from=translated src=- shape=2d9f1f1b vocab=0ab66b83
-/
theorem frobInner_add_right (A B C : Matrix m n 𝕜) :
    frobInner A (B + C) = frobInner A B + frobInner A C := by
  rw [frobInner_comm, frobInner_add_left, frobInner_comm B, frobInner_comm C]

/-- Subtraction in the first argument. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h6v.s6.19d469af3e17 from=translated src=- shape=61aa74a0 vocab=09565940
-/
theorem frobInner_sub_left (A B C : Matrix m n 𝕜) :
    frobInner (A - B) C = frobInner A C - frobInner B C := by
  unfold frobInner
  simp [sub_mul, Finset.sum_sub_distrib]

/-- Subtraction in the second argument. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h6v.s6.425afbf22b26 from=translated src=- shape=2d9f1f1b vocab=09565940
-/
theorem frobInner_sub_right (A B C : Matrix m n 𝕜) :
    frobInner A (B - C) = frobInner A B - frobInner A C := by
  rw [frobInner_comm, frobInner_sub_left, frobInner_comm B, frobInner_comm C]

/-- Homogeneity in the first argument for a real scalar. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h6v.s6.90a4a2f0898c from=translated src=- shape=a86ec544 vocab=fce3f0fe
-/
theorem frobInner_smul_left (c : ℝ) (A B : Matrix m n 𝕜) :
    frobInner (c • A) B = c * frobInner A B := by
  unfold frobInner
  rw [← RCLike.re_ofReal_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, RCLike.real_smul_eq_coe_mul, star_mul', RCLike.star_def,
    RCLike.conj_ofReal, mul_assoc]

/-- Homogeneity in the second argument for a real scalar. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h6v.s6.429de525b274 from=translated src=- shape=fb49148e vocab=fce3f0fe
-/
theorem frobInner_smul_right (c : ℝ) (A B : Matrix m n 𝕜) :
    frobInner A (c • B) = c * frobInner A B := by
  rw [frobInner_comm, frobInner_smul_left, frobInner_comm]

/-- Negation in the first argument. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h5v.s6.702cdda715bd from=translated src=- shape=477f5cc0 vocab=039163e3
-/
theorem frobInner_neg_left (A B : Matrix m n 𝕜) : frobInner (-A) B = -frobInner A B := by
  unfold frobInner; simp [Finset.sum_neg_distrib]

/-- Negation in the second argument. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h5v.s6.b31f4f80b183 from=translated src=- shape=df160d59 vocab=039163e3
-/
theorem frobInner_neg_right (A B : Matrix m n 𝕜) : frobInner A (-B) = -frobInner A B := by
  rw [frobInner_comm, frobInner_neg_left, frobInner_comm]

/-- `⟨0, B⟩_F = 0`. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h4v.s6.0493891261a0 from=translated src=- shape=4752f0e4 vocab=997d772c
-/
@[simp] theorem frobInner_zero_left (B : Matrix m n 𝕜) :
    frobInner (0 : Matrix m n 𝕜) B = 0 := by
  unfold frobInner; simp

/-- `⟨A, 0⟩_F = 0`. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h4v.s6.80e0515960d8 from=translated src=- shape=1c6ade77 vocab=997d772c
-/
@[simp] theorem frobInner_zero_right (A : Matrix m n 𝕜) :
    frobInner A (0 : Matrix m n 𝕜) = 0 := by
  unfold frobInner; simp

/-- `⟨Aᵀ, Bᵀ⟩_F = ⟨A, B⟩_F`. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h5v.s5.f057bc7f268f from=translated src=- shape=67da2f1c vocab=fef57bb1
-/
theorem frobInner_transpose (A B : Matrix m n 𝕜) : frobInner Aᵀ Bᵀ = frobInner A B := by
  unfold frobInner
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- `⟨Aᴴ, Bᴴ⟩_F = ⟨A, B⟩_F`. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h5v.s7.ccaa8861a774 from=translated src=- shape=67da2f1c vocab=78198c27
-/
theorem frobInner_conjTranspose (A B : Matrix m n 𝕜) : frobInner Aᴴ Bᴴ = frobInner A B := by
  rw [frobInner_eq_trace, Matrix.conjTranspose_conjTranspose,
    frobInner_eq_re_trace_mul_conjTranspose]

/-! ### Squared Frobenius norm and Frobenius norm -/

/-- `‖A‖_F² = ∑ᵢⱼ |Aᵢⱼ|²`. Atlas `norms-frob-spec`.
atlas: norms-frob-spec
@isnad1 id=eq.0h4v.s6.53aff7a97fc7 from=translated src=- shape=9ea34ef2 vocab=2839e40c
-/
theorem frobSq_eq_sum_norm_sq (A : Matrix m n 𝕜) : frobSq A = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  unfold frobSq frobInner
  simp only [map_sum, RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- `‖A‖_F² = ∑ᵢⱼ Aᵢⱼ²` over `ℝ`. Atlas `norms-frob-spec`.
atlas: norms-frob-spec
@isnad1 id=eq.0h3v.s6.44172b4fce84 from=translated src=- shape=acd70df9 vocab=00cba50c
-/
theorem frobSq_eq_sum_sq (A : Matrix m n ℝ) : frobSq A = ∑ i, ∑ j, A i j ^ 2 := by
  simp [frobSq_eq_sum_norm_sq]

/-- `‖A‖_F² ≥ 0`. Atlas `norms-frob-spec`.
@isnad1 id=le.0h4v.s5.7622e501d4ec from=translated src=- shape=7c34dae1 vocab=56878ec1
-/
theorem frobSq_nonneg (A : Matrix m n 𝕜) : 0 ≤ frobSq A := by
  rw [frobSq_eq_sum_norm_sq]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/-- `‖0‖_F² = 0`. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h3v.s5.629018bd3425 from=translated src=- shape=1c268922 vocab=a15e1003
-/
@[simp] theorem frobSq_zero : frobSq (0 : Matrix m n 𝕜) = 0 := by
  unfold frobSq; simp

/-- Definiteness: `‖A‖_F² = 0 ↔ A = 0`. Atlas `norms-frob-spec`.
@isnad1 id=iff.0h4v.s6.51ffc6ac496a from=translated src=- shape=eb134ea1 vocab=a15e1003
-/
theorem frobSq_eq_zero_iff (A : Matrix m n 𝕜) : frobSq A = 0 ↔ A = 0 := by
  rw [frobSq_eq_sum_norm_sq, Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg ‖A i j‖)]
  simp only [Finset.mem_univ, true_implies]
  constructor
  · intro h; ext i j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖A i j‖)).1 (h i) j
      (Finset.mem_univ _)
    simpa using this
  · rintro rfl; simp

/-- `‖-A‖_F² = ‖A‖_F²`. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h4v.s6.a89b495a0cce from=translated src=- shape=ea7e6113 vocab=c57c80a3
-/
theorem frobSq_neg (A : Matrix m n 𝕜) : frobSq (-A) = frobSq A := by
  unfold frobSq; rw [frobInner_neg_left, frobInner_neg_right, neg_neg]

/-- `‖A - B‖_F² = ‖B - A‖_F²`. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h5v.s6.bf04c1c75467 from=translated src=- shape=c8b64a76 vocab=063155bd
-/
theorem frobSq_sub_comm (A B : Matrix m n 𝕜) : frobSq (A - B) = frobSq (B - A) := by
  rw [← frobSq_neg, neg_sub]

/-- `‖cA‖_F² = c² ‖A‖_F²` for a real scalar `c`. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h5v.s7.a701a65317bb from=translated src=- shape=902fb9ac vocab=34a19d86
-/
theorem frobSq_smul (c : ℝ) (A : Matrix m n 𝕜) : frobSq (c • A) = c ^ 2 * frobSq A := by
  unfold frobSq; rw [frobInner_smul_left, frobInner_smul_right]; ring

/-- `‖cA‖_F² = |c|² ‖A‖_F²` for a scalar `c : 𝕜`. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h5v.s6.392196ef326d from=translated src=- shape=47bad01c vocab=e3d84fac
-/
theorem frobSq_smul_eq_norm_sq_mul (c : 𝕜) (A : Matrix m n 𝕜) :
    frobSq (c • A) = ‖c‖ ^ 2 * frobSq A := by
  simp only [frobSq_eq_sum_norm_sq, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow,
    Finset.mul_sum]

/-- `‖A + B‖_F² = ‖A‖_F² + 2⟨A, B⟩_F + ‖B‖_F²`. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h5v.s7.c6d033b25d40 from=translated src=- shape=f037b995 vocab=604973b2
-/
theorem frobSq_add (A B : Matrix m n 𝕜) :
    frobSq (A + B) = frobSq A + 2 * frobInner A B + frobSq B := by
  unfold frobSq
  rw [frobInner_add_left, frobInner_add_right, frobInner_add_right, frobInner_comm B A]
  ring

/-- `‖A - B‖_F² = ‖A‖_F² - 2⟨A, B⟩_F + ‖B‖_F²`. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h5v.s7.cdf00339009d from=translated src=- shape=bf9a9f16 vocab=a878d8d3
-/
theorem frobSq_sub (A B : Matrix m n 𝕜) :
    frobSq (A - B) = frobSq A - 2 * frobInner A B + frobSq B := by
  unfold frobSq
  rw [frobInner_sub_left, frobInner_sub_right, frobInner_sub_right, frobInner_comm B A]
  ring

/-- Pythagoras: orthogonal summands have additive squared norms. Atlas `norms-frob-spec`.
@isnad1 id=eq.1h5v.s6.8cf085fb78f4 from=translated src=- shape=952ad2d8 vocab=eab450c6
-/
theorem frobSq_add_of_frobInner_eq_zero (A B : Matrix m n 𝕜) (h : frobInner A B = 0) :
    frobSq (A + B) = frobSq A + frobSq B := by
  rw [frobSq_add, h]; ring

/-- Pythagoras for a difference of orthogonal matrices. Atlas `norms-frob-spec`.
@isnad1 id=eq.1h5v.s6.64251d74bd28 from=translated src=- shape=952ad2d8 vocab=863b7210
-/
theorem frobSq_sub_of_frobInner_eq_zero (A B : Matrix m n 𝕜) (h : frobInner A B = 0) :
    frobSq (A - B) = frobSq A + frobSq B := by
  rw [frobSq_sub, h]; ring

/-- `‖Aᵀ‖_F² = ‖A‖_F²`. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h4v.s5.3c7d20a6a85f from=translated src=- shape=103aacbf vocab=a4fc60bd
-/
theorem frobSq_transpose (A : Matrix m n 𝕜) : frobSq Aᵀ = frobSq A :=
  frobInner_transpose A A

/-- `‖Aᴴ‖_F² = ‖A‖_F²`. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h4v.s6.18d3ae8a5797 from=translated src=- shape=103aacbf vocab=f387e174
-/
theorem frobSq_conjTranspose (A : Matrix m n 𝕜) : frobSq Aᴴ = frobSq A :=
  frobInner_conjTranspose A A

/-- `‖A‖_F ≥ 0`. Atlas `norms-frob-spec`.
@isnad1 id=le.0h4v.s5.cff919c767e2 from=translated src=- shape=7c34dae1 vocab=045c914d
-/
theorem frobNorm_nonneg (A : Matrix m n 𝕜) : 0 ≤ frobNorm A := Real.sqrt_nonneg _

/-- `‖A‖_F² = frobSq A`. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h4v.s5.699b42cd8164 from=translated src=- shape=6be453de vocab=69f5bee9
-/
theorem frobNorm_sq (A : Matrix m n 𝕜) : frobNorm A ^ 2 = frobSq A :=
  Real.sq_sqrt (frobSq_nonneg A)

/-- Definiteness of `‖·‖_F`. Atlas `norms-frob-spec`.
@isnad1 id=iff.0h4v.s6.ba2bf254ffe0 from=translated src=- shape=eb134ea1 vocab=f7988b51
-/
theorem frobNorm_eq_zero_iff (A : Matrix m n 𝕜) : frobNorm A = 0 ↔ A = 0 := by
  rw [frobNorm, Real.sqrt_eq_zero (frobSq_nonneg A), frobSq_eq_zero_iff]

/-- `‖0‖_F = 0`. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h3v.s5.b33e730e2294 from=translated src=- shape=1c268922 vocab=f7988b51
-/
@[simp] theorem frobNorm_zero : frobNorm (0 : Matrix m n 𝕜) = 0 := by
  simp [frobNorm]

/-- `‖Aᵀ‖_F = ‖A‖_F`. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h4v.s5.ca5160b33799 from=translated src=- shape=103aacbf vocab=469143fb
-/
theorem frobNorm_transpose (A : Matrix m n 𝕜) : frobNorm Aᵀ = frobNorm A := by
  rw [frobNorm, frobSq_transpose, frobNorm]

/-- `‖Aᴴ‖_F = ‖A‖_F`. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h4v.s6.3e1a9dcba02a from=translated src=- shape=103aacbf vocab=56019c9a
-/
theorem frobNorm_conjTranspose (A : Matrix m n 𝕜) : frobNorm Aᴴ = frobNorm A := by
  rw [frobNorm, frobSq_conjTranspose, frobNorm]

/-- `‖-A‖_F = ‖A‖_F`. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h4v.s6.976e2ba2effd from=translated src=- shape=ea7e6113 vocab=d1d9e9dc
-/
theorem frobNorm_neg (A : Matrix m n 𝕜) : frobNorm (-A) = frobNorm A := by
  rw [frobNorm, frobSq_neg, frobNorm]

/-- `‖cA‖_F = |c| ‖A‖_F` for a real scalar `c`. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h5v.s6.179307cc3537 from=translated src=- shape=17ce055c vocab=042aa3ab
-/
theorem frobNorm_smul (c : ℝ) (A : Matrix m n 𝕜) : frobNorm (c • A) = |c| * frobNorm A := by
  rw [frobNorm, frobSq_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, frobNorm]

/-- `‖cA‖_F = |c| ‖A‖_F` for a scalar `c : 𝕜`. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h5v.s6.5d6dbb523616 from=translated src=- shape=774290a4 vocab=b0cf6c6a
-/
theorem frobNorm_smul_eq_norm_mul (c : 𝕜) (A : Matrix m n 𝕜) :
    frobNorm (c • A) = ‖c‖ * frobNorm A := by
  rw [frobNorm, frobSq_smul_eq_norm_sq_mul, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg c), frobNorm]

/-- `‖I‖_F² = n`. Atlas: `slq-error` (helper).
@isnad1 id=eq.0h2v.s6.3b1a4f90a0c7 from=translated src=- shape=342382f9 vocab=c053e6bc
-/
theorem frobNorm_one_sq [DecidableEq n] : frobNorm (1 : Matrix n n 𝕜) ^ 2 = Fintype.card n := by
  rw [frobNorm_sq, frobSq_eq_sum_norm_sq]
  simp [Matrix.one_apply, apply_ite (fun x : 𝕜 => ‖x‖ ^ 2)]

/-- The diagonal carries at most the whole Frobenius mass: `∑ᵢ |Aᵢᵢ|² ≤ ‖A‖_F²`.
@isnad1 id=le.0h3v.s6.6e2b76dd8e88 from=translated src=- shape=3a47054b vocab=712ada23
-/
theorem sum_norm_diag_sq_le_frobSq (A : Matrix n n 𝕜) :
    (∑ i, ‖A i i‖ ^ 2) ≤ frobSq A := by
  rw [frobSq_eq_sum_norm_sq]
  exact Finset.sum_le_sum fun i _ =>
    Finset.single_le_sum (f := fun j => ‖A i j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-- The diagonal carries at most the whole Frobenius mass: `∑ᵢ Aᵢᵢ² ≤ ‖A‖_F²` over `ℝ`.
Moved from the Hanson–Wright chain (HighDimProb commit c0cb8d9); atlas `hanson-wright` (helper).
@isnad1 id=le.0h2v.s5.4ab36c023fff from=translated src=- shape=7052c545 vocab=f9dcf08d
-/
theorem sum_diag_sq_le_frobSq (A : Matrix n n ℝ) :
    (∑ i, A i i ^ 2) ≤ frobSq A := by
  simpa using sum_norm_diag_sq_le_frobSq A

/-- `∑ᵢ Aᵢᵢ² ≤ ‖A‖_F²`, stated with `frobNorm A ^ 2`.
Moved from the Hanson–Wright chain (HighDimProb commit c0cb8d9); atlas `hanson-wright` (helper).
@isnad1 id=le.0h2v.s6.f1fc1e57c204 from=translated src=- shape=98ded955 vocab=4abf911d
-/
theorem sum_diag_sq_le_frobNorm_sq (A : Matrix n n ℝ) :
    (∑ i, A i i ^ 2) ≤ frobNorm A ^ 2 := by
  rw [frobNorm_sq]
  exact sum_diag_sq_le_frobSq A

/-! ### Rows and dot products -/

/-- `v ⬝ᵥ v ≥ 0` for real vectors (Mathlib has only the `star` forms
`dotProduct_star_self_nonneg`). Atlas `norms-frob-spec`.
@isnad1 id=le.0h2v.s4.6e6563b835bf from=translated src=- shape=88b7ad43 vocab=fbc09bd2
-/
theorem dotProduct_self_nonneg (v : n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- `‖A‖_F² = ∑ᵢ Re(Aᵢ* Aᵢ)`, the sum of the squared norms of the rows.
@isnad1 id=eq.0h4v.s7.7fa6790cd8ac from=translated src=- shape=c41b3d20 vocab=41d6d174
-/
theorem frobSq_eq_sum_re_star_dotProduct_self (A : Matrix m n 𝕜) :
    frobSq A = ∑ i, RCLike.re (star (A i) ⬝ᵥ A i) := by
  simp [frobSq, frobInner, dotProduct]

omit [Fintype m] in
/-- `‖Av‖² = ∑ᵢ (Aᵢ ⬝ v)²`, written with dot products. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h4v.s6.cb2b7a41ad23 from=translated src=- shape=ffa91289 vocab=5b2b7a5d
-/
theorem mulVec_dotProduct_mulVec_eq_sum_sq [Fintype m] (A : Matrix m n ℝ) (v : n → ℝ) :
    (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = ∑ i, (A i ⬝ᵥ v) ^ 2 := by
  simp only [dotProduct, sq]
  rfl

/-- `‖Ax‖² = x* (AᴴA) x`, written with dot products (over `ℝ`, `(Ax) ⬝ (Ax) = x ⬝ (AᵀA) x`
after `simp`). Atlas `norms-frob-spec`.
@isnad1 id=eq.0h5v.s8.1615f2acf4f4 from=translated src=- shape=abe90b02 vocab=ebed3d08
-/
theorem star_mulVec_dotProduct_mulVec_self (A : Matrix m n 𝕜) (x : n → 𝕜) :
    star (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = star x ⬝ᵥ ((Aᴴ * A) *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (star x) Aᴴ, Matrix.star_mulVec]

/-- The squared Frobenius norm is the real part of the Gram trace: `‖A‖_F² = Re tr(AᴴA)`.
Horn–Johnson 2013, §5.6; supports `volume-sampling`.
@isnad1 id=eq.0h4v.s8.89a24f112868 from=translated src=- shape=ce621987 vocab=38f0f2d1
-/
theorem frobSq_eq_re_trace_conjTranspose_mul_self (A : Matrix m n 𝕜) :
    frobSq A = RCLike.re (Aᴴ * A).trace := by
  simp only [frobSq, frobInner, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

/-- The squared Frobenius norm is the sum of the squared Frobenius norms of the columns
(as `m × Fin 1` matrices). Supports `volume-sampling`.
@isnad1 id=eq.0h4v.s6.04a5b76fdd03 from=translated src=- shape=73e024bf vocab=8be377d2
-/
theorem frobSq_eq_sum_frobSq_col (A : Matrix m n 𝕜) :
    frobSq A = ∑ j, frobSq (A.submatrix id (fun _ : Fin 1 => j)) := by
  simp only [frobSq_eq_sum_norm_sq, Matrix.submatrix_apply, id_eq, Fin.sum_univ_one]
  rw [Finset.sum_comm]

/-- The squared Frobenius norm of a diagonal matrix is the sum of the squared moduli of its
entries.
@isnad1 id=eq.0h3v.s6.8e098c921d4b from=translated src=- shape=0442071b vocab=51e0da84
-/
theorem frobSq_diagonal [DecidableEq n] (d : n → 𝕜) :
    frobSq (Matrix.diagonal d) = ∑ i, ‖d i‖ ^ 2 := by
  simp only [frobSq_eq_sum_norm_sq, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (fun h => (h (Finset.mem_univ i)).elim)]
  simp

/-- Row-wise Cauchy–Schwarz: `‖Ax‖₂² ≤ ‖A‖_F² ‖x‖₂²`, written with explicit sums.
Atlas `norms-frob-spec`.
@isnad1 id=le.0h5v.s7.093ddb4eebd8 from=translated src=- shape=ef900c9d vocab=5b863d71
-/
theorem sum_norm_sq_mulVec_le_frobSq (A : Matrix m n 𝕜) (x : n → 𝕜) :
    ∑ i, ‖(A *ᵥ x) i‖ ^ 2 ≤ frobSq A * ∑ j, ‖x j‖ ^ 2 := by
  rw [frobSq_eq_sum_norm_sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖(A *ᵥ x) i‖ ≤ ∑ j, ‖A i j‖ * ‖x j‖ := by
    simp only [Matrix.mulVec, dotProduct]
    exact (norm_sum_le _ _).trans (le_of_eq (by simp only [norm_mul]))
  calc ‖(A *ᵥ x) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖x j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- Row-wise Cauchy–Schwarz over `ℝ`: `‖Ax‖₂² ≤ ‖A‖_F² ‖x‖₂²`, written with explicit sums.
Atlas `norms-frob-spec`.
@isnad1 id=le.0h4v.s6.5f839eabdeb1 from=translated src=- shape=641617d8 vocab=d0b83b9e
-/
theorem sum_sq_mulVec_le_frobSq (A : Matrix m n ℝ) (x : n → ℝ) :
    ∑ i, (A *ᵥ x) i ^ 2 ≤ frobSq A * ∑ j, x j ^ 2 := by
  simpa using sum_norm_sq_mulVec_le_frobSq A x

/-- Row-wise Cauchy–Schwarz, dot-product form: `‖Bx‖₂² ≤ ‖B‖_F² ‖x‖₂²`.
Atlas `norm-lipschitz`.
@isnad1 id=le.0h4v.s6.cfaad82c49dc from=translated src=- shape=bcd03272 vocab=ba8467f4
-/
theorem mulVec_dotProduct_mulVec_le_frobSq_mul (B : Matrix m n ℝ) (x : n → ℝ) :
    (B *ᵥ x) ⬝ᵥ (B *ᵥ x) ≤ frobSq B * (x ⬝ᵥ x) := by
  have h := sum_sq_mulVec_le_frobSq B x
  simpa [dotProduct, sq] using h

/-! ### Cauchy–Schwarz and the triangle inequality -/

/-- Cauchy–Schwarz for the Frobenius inner product: `⟨A, B⟩_F ≤ ‖A‖_F ‖B‖_F`.
Standard; atlas `norms-frob-spec`.
atlas: norms-frob-spec
@isnad1 id=le.0h5v.s5.77d90bf5cfd6 from=translated src=- shape=fc39736a vocab=6398e898
-/
theorem frobInner_le_frobNorm_mul_frobNorm (A B : Matrix m n 𝕜) :
    frobInner A B ≤ frobNorm A * frobNorm B := by
  -- Discriminant argument: `0 ≤ ‖tA - B‖_F²` for `t = ⟨A, B⟩_F / ‖A‖_F²`.
  by_cases hA : frobSq A = 0
  · have : A = 0 := (frobSq_eq_zero_iff A).1 hA
    subst this; simp
  · have hApos : 0 < frobSq A := lt_of_le_of_ne (frobSq_nonneg A) (Ne.symm hA)
    set t := frobInner A B / frobSq A with ht
    have h0 : 0 ≤ frobSq (t • A - B) := frobSq_nonneg _
    rw [frobSq_sub, frobInner_smul_left, frobSq_smul] at h0
    have key : frobInner A B ^ 2 ≤ frobSq A * frobSq B := by
      have : t ^ 2 * frobSq A - 2 * (t * frobInner A B) + frobSq B =
          frobSq B - frobInner A B ^ 2 / frobSq A := by
        rw [ht]; field_simp; ring
      rw [this] at h0
      have := (sub_nonneg.1 h0)
      rwa [div_le_iff₀ hApos, mul_comm] at this
    have hprod : frobNorm A * frobNorm B = Real.sqrt (frobSq A * frobSq B) := by
      unfold frobNorm; rw [Real.sqrt_mul (frobSq_nonneg A)]
    rw [hprod]
    calc frobInner A B ≤ |frobInner A B| := le_abs_self _
      _ = Real.sqrt (frobInner A B ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (frobSq A * frobSq B) := Real.sqrt_le_sqrt key

/-- Cauchy–Schwarz, absolute-value form: `|⟨A, B⟩_F| ≤ ‖A‖_F ‖B‖_F`. Atlas `norms-frob-spec`.
@isnad1 id=le.0h5v.s6.a06ebebcc816 from=translated src=- shape=ac3896b5 vocab=f03f352c
-/
theorem abs_frobInner_le_frobNorm_mul_frobNorm (A B : Matrix m n 𝕜) :
    |frobInner A B| ≤ frobNorm A * frobNorm B := by
  rw [abs_le]
  constructor
  · have := frobInner_le_frobNorm_mul_frobNorm (-A) B
    rw [frobInner_neg_left, frobNorm_neg] at this
    linarith
  · exact frobInner_le_frobNorm_mul_frobNorm A B

/-- Triangle inequality `‖A + B‖_F ≤ ‖A‖_F + ‖B‖_F`. Atlas `norms-frob-spec`.
@isnad1 id=le.0h5v.s6.8733e5d6cc83 from=translated src=- shape=83b71d17 vocab=104ed960
-/
theorem frobNorm_add_le (A B : Matrix m n 𝕜) : frobNorm (A + B) ≤ frobNorm A + frobNorm B := by
  have hs : 0 ≤ frobNorm A + frobNorm B := add_nonneg (frobNorm_nonneg A) (frobNorm_nonneg B)
  rw [frobNorm, Real.sqrt_le_left hs, frobSq_add, add_sq, frobNorm_sq, frobNorm_sq]
  have := frobInner_le_frobNorm_mul_frobNorm A B
  nlinarith

/-- Triangle inequality for a difference. Atlas `norms-frob-spec`.
@isnad1 id=le.0h5v.s6.46594e341f72 from=translated src=- shape=83b71d17 vocab=2284c400
-/
theorem frobNorm_sub_le (A B : Matrix m n 𝕜) : frobNorm (A - B) ≤ frobNorm A + frobNorm B := by
  rw [sub_eq_add_neg, ← frobNorm_neg B]; exact frobNorm_add_le A (-B)

/-! ### Interaction with matrix products -/

/-- `⟨P X, Q Y⟩_F = ⟨X, (Pᴴ Q) Y⟩_F`. Atlas `norms-frob-spec`.
@isnad1 id=eq.0h8v.s8.8d167d6cca39 from=translated src=- shape=4b3fecb4 vocab=9855c8cb
-/
theorem frobInner_mul_mul (P : Matrix m p 𝕜) (X : Matrix p n 𝕜)
    (Q : Matrix m p 𝕜) (Y : Matrix p n 𝕜) :
    frobInner (P * X) (Q * Y) = frobInner X (Pᴴ * Q * Y) := by
  rw [frobInner_eq_trace, frobInner_eq_trace, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- Matrices with orthogonal column spaces (`Pᴴ Q = 0`) are Frobenius-orthogonal.
Atlas `norms-frob-spec`.
@isnad1 id=eq.1h9v.s8.44221a2cd712 from=translated src=- shape=492fd913 vocab=9855c8cb
-/
theorem frobInner_mul_mul_eq_zero {p' : Type*} [Fintype p']
    (P : Matrix m p 𝕜) (X : Matrix p n 𝕜) (Q : Matrix m p' 𝕜) (Y : Matrix p' n 𝕜)
    (h : Pᴴ * Q = 0) : frobInner (P * X) (Q * Y) = 0 := by
  rw [frobInner_eq_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Pᴴ, h]
  simp

/-- Left multiplication by `Q` with orthonormal columns (`QᴴQ = I`, i.e.
`NLAlib.HasOrthonormalCols Q` unfolded) preserves `⟨·,·⟩_F`. Atlas `norms-frob-spec`.
@isnad1 id=eq.1h7v.s8.e9ab78b038f7 from=translated src=- shape=74ec10e6 vocab=3f1dce08
-/
theorem frobInner_mul_left_of_orthonormal [DecidableEq p] {Q : Matrix m p 𝕜}
    (hQ : Qᴴ * Q = 1) (X Y : Matrix p n 𝕜) :
    frobInner (Q * X) (Q * Y) = frobInner X Y := by
  rw [frobInner_mul_mul, hQ, Matrix.one_mul]

/-- Unitary invariance, left: `‖Q X‖_F² = ‖X‖_F²` when `QᴴQ = I`. Atlas `norms-frob-spec`.
atlas: norms-frob-spec
@isnad1 id=eq.1h6v.s8.faa6e30fa083 from=translated src=- shape=d8473131 vocab=156066c2
-/
theorem frobSq_mul_left_of_orthonormal [DecidableEq p] {Q : Matrix m p 𝕜}
    (hQ : Qᴴ * Q = 1) (X : Matrix p n 𝕜) : frobSq (Q * X) = frobSq X :=
  frobInner_mul_left_of_orthonormal hQ X X

/-- Unitary invariance, right: `‖X Vᴴ‖_F² = ‖X‖_F²` when `VᴴV = I`. Atlas `norms-frob-spec`.
@isnad1 id=eq.1h6v.s8.1e4c5914dc53 from=translated src=- shape=8cc9ce49 vocab=156066c2
-/
theorem frobSq_mul_right_of_orthonormal [DecidableEq p] {V : Matrix n p 𝕜}
    (hV : Vᴴ * V = 1) (X : Matrix m p 𝕜) : frobSq (X * Vᴴ) = frobSq X := by
  rw [← frobSq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    frobSq_mul_left_of_orthonormal hV, frobSq_conjTranspose]

/-! ### Mathlib's Frobenius norm -/

section MathlibFrobenius

open scoped Matrix.Norms.Frobenius

/-- The squared Frobenius norm (Mathlib's scoped `Matrix.frobeniusNormedAddCommGroup`) is the sum
of the squared norms of the entries. Source: the Frobenius definition, supporting.
@isnad1 id=eq.0h4v.s6.66d00e64dd27 from=translated src=- shape=4d02a2b2 vocab=432e5654
-/
theorem frobenius_norm_sq_eq_sum_norm_sq {m n 𝕜 : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup 𝕜] (A : Matrix m n 𝕜) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def]
  simp_rw [Real.rpow_two, ← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- `frobNorm` is Mathlib's Frobenius norm `‖A‖` (`Matrix.frobeniusNormedAddCommGroup`, under
`open scoped Matrix.Norms.Frobenius`). Atlas `norms-frob-spec`.
@isnad1 id=eq.0h4v.s5.84c215f78f36 from=translated src=- shape=a6e67169 vocab=37f19b3a
-/
theorem frobNorm_eq_norm (A : Matrix m n 𝕜) : frobNorm A = ‖A‖ := by
  rw [frobNorm, frobSq_eq_sum_norm_sq, ← frobenius_norm_sq_eq_sum_norm_sq,
    Real.sqrt_sq (norm_nonneg A)]

end MathlibFrobenius

end NLAlib

/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import Tengoku.Nlalib.NLAlib.Matrix.Spectral.SVD
import Tengoku.Nlalib.NLAlib.Matrix.Functions.RealCalculus

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Singular-value transforms through the Gram functional calculus

The finite real spectrum permits arbitrary scalar functions. The Gram formula makes
SVD independence, including repeated and zero singular values, an equality theorem.
Source: Cai–Candès–Shen (2010), §2.1; Fessler–Nadakuditi (2024), §7.5.
Atlas: `singular-value-shrinkage-def`.
-/

noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The rectangular singular-value transform `A h(AᴴA)`, where
`h(t) = φ(√t)/√t` uses total division at zero. For `φ(0)=0` this equals the
usual SVD formula; no continuity assumption on `φ` is needed on a finite spectrum.
Cai–Candès–Shen (2010), §2.1; Fessler–Nadakuditi (2024), §7.5.
atlas: singular-value-shrinkage-def (partial)-/
def singularValueTransform (φ : ℝ → ℝ) (A : Matrix m n 𝕜) : Matrix m n 𝕜 :=
  A * cfc (fun t => φ (Real.sqrt t) / Real.sqrt t) (Aᴴ * A)

/-- Singular-value transforms commute with left and right unitary multiplication.
The Gram definition proves this independently of singular-vector choices.
Cai–Candès–Shen (2010), §2.1.
atlas: singular-value-shrinkage-def (partial)-/
theorem singularValueTransform_unitary_mul (φ : ℝ → ℝ) (A : Matrix m n 𝕜)
    (U : Matrix m m 𝕜) (V : Matrix n n 𝕜)
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) :
    singularValueTransform φ (U * A * Vᴴ) = U * singularValueTransform φ A * Vᴴ := by
  have hGram : (U * A * Vᴴ)ᴴ * (U * A * Vᴴ) = V * (Aᴴ * A) * Vᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hU.conjTranspose_mul_self, Matrix.one_mul]
  rw [singularValueTransform, hGram,
    cfc_isometric_conj V hV (mul_eq_one_comm.mp hV.conjTranspose_mul_self) _ _
      (Matrix.isHermitian_conjTranspose_mul_self A), singularValueTransform]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Vᴴ V, hV.conjTranspose_mul_self, Matrix.one_mul]

/-- Singular-value soft thresholding, with the scalar rule `(s-τ)₊`.
Cai–Candès–Shen (2010), equations (2.1)–(2.2).
atlas: singular-value-shrinkage-def (partial)-/
def singularValueSoftThreshold (τ : ℝ) (A : Matrix m n 𝕜) : Matrix m n 𝕜 :=
  singularValueTransform (fun s => max (s - τ) 0) A

end NLAlib

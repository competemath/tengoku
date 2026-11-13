import Tengoku.Nlalib.NLAlib.Matrix.Spectral.CStarRectangularDilation
import Tengoku.Seed.Analysis.SpecialFunctions.Sqrt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Positive spectral branch of the actual rectangular dilation

The true sign symmetry and square mapping identify positive dilation
spectrum with positive row-Gram spectrum over arbitrary C*-algebras.
Source: arXiv:2406.11453v2, Section 5.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace CStarMatrix
variable {m n A : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Negating the native rectangular dilation leaves its actual spectrum unchanged.-/
theorem spectrum_real_neg_rectangularDilation (Y : Matrix m n A) :
    spectrum ℝ (-rectangularDilation Y) = spectrum ℝ (rectangularDilation Y) := by
  let S : CStarMatrix (m ⊕ n) (m ⊕ n) A := blockDiagonalStarAlgHom (1, -1)
  have hSS : S * S = 1 := by
    change blockDiagonalStarAlgHom (1, -1) * blockDiagonalStarAlgHom (1, -1) = 1
    rw [← map_mul]
    norm_num
    change blockDiagonalStarAlgHom (1 : CStarMatrix m m A × CStarMatrix n n A) = 1
    exact map_one _
  let u : (CStarMatrix (m ⊕ n) (m ⊕ n) A)ˣ := ⟨S, S, hSS, hSS⟩
  have hconj : (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) * rectangularDilation Y *
      (↑u⁻¹ : CStarMatrix (m ⊕ n) (m ⊕ n) A) = -rectangularDilation Y := by
    change (Matrix.fromBlocks 1 0 0 (-1) : Matrix (m ⊕ n) (m ⊕ n) A) * Matrix.fromBlocks 0 Y Yᴴ 0 *
      Matrix.fromBlocks 1 0 0 (-1) = -Matrix.fromBlocks 0 Y Yᴴ 0
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, zero_add, add_zero,
      neg_zero, Matrix.fromBlocks_neg]
  rw [← hconj]
  exact spectrum.units_conjugate

omit [PartialOrder A] [StarOrderedRing A] in
/-- The actual dilation spectrum has the genuine sign symmetry, without
assuming discrete eigenvalues.-/
theorem mem_spectrum_real_rectangularDilation_neg_iff (Y : Matrix m n A) (r : ℝ) :
    -r ∈ spectrum ℝ (rectangularDilation Y) ↔ r ∈ spectrum ℝ (rectangularDilation Y) := by
  have h := congrArg (fun K : Set ℝ => -r ∈ K) (spectrum_real_neg_rectangularDilation Y)
  rw [← spectrum.neg_eq, Set.mem_neg, neg_neg] at h
  exact iff_of_eq h.symm

end CStarMatrix

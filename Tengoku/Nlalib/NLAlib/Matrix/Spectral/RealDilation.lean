import Tengoku.Nlalib.NLAlib.Matrix.Spectral.SingularValueSpectrum
import Tengoku.Nlalib.NLAlib.Matrix.Basic.Dilation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Real symmetric dilation and its orthogonal diagonalization

The real dilation `dilation A = [0 A; Aᵀ 0]` (`Matrix/Basic/Dilation`) has the paired singular
spectrum,
including every rectangular padded zero. Source: Bhatia 1997, Section III.4.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Mixed rectangular diagonal multiplication gives the coordinate products,
with zeros beyond the intermediate dimension. Horn–Johnson 2013, Section 2.6.
@isnad1 id=eq.0h5v.s6.9ebf7d29ed9f from=translated src=- shape=5c420b53 vocab=58b49541
-/
theorem rectDiag_mul_rectDiag {m n p : ℕ} (s t : ℕ → ℝ) :
    (rectDiag s : Matrix (Fin m) (Fin n) ℝ) *
      (rectDiag t : Matrix (Fin n) (Fin p) ℝ) =
      rectDiag (fun k => if k < n then s k * t k else 0) := by
  ext i j
  simp only [Matrix.mul_apply, rectDiag_apply]
  by_cases hi : (i : ℕ) < n
  · rw [Finset.sum_eq_single ⟨i, hi⟩]
    · split_ifs <;> simp_all
    · intro l _ hl
      rw [ite_eq_right (fun h => hl (Fin.ext h.symm)), zero_mul]
    · simp
  · rw [Finset.sum_eq_zero]
    · split_ifs <;> simp_all
    · intro l _
      rw [ite_eq_right (fun (h : (i : ℕ) = l) => hi (h.symm ▸ l.isLt)), zero_mul]

private def pairRotation (m n : ℕ) (r : ℝ) : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
  Matrix.fromBlocks (Matrix.diagonal fun i : Fin m => if (i : ℕ) < n then r else 1)
    (rectDiag fun _ => r) (rectDiag fun _ => r)
    (Matrix.diagonal fun j : Fin n => if (j : ℕ) < m then -r else 1)

end NLAlib

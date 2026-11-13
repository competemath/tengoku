import Tengoku.Nlalib.NLAlib.Matrix.Spectral.LowRankInterlacing
import Tengoku.Nlalib.NLAlib.Matrix.Spectral.EigenvalueEquality
import Tengoku.Nlalib.NLAlib.Matrix.Spectral.SingularValueInvariance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Singular-value interlacing under row and column deletion

Selecting rows splits the column Gram matrix into the selected and omitted
row Grams. Low-rank eigenvalue interlacing gives the lower shift and PSD
order gives the upper bound. Transposition treats columns, and combining
the two gives arbitrary submatrix interlacing on the padded singular
list. Source: Horn--Johnson (2013), Corollary 7.3.6.
Atlas: `singular-value-interlacing`.
-/

noncomputable section
open Matrix

namespace NLAlib

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [Fintype n] [DecidableEq n] [DecidableEq p] in
/-- A row selection and its omitted rows split the column Gram matrix.
Horn--Johnson (2013), Corollary 7.3.6;
helper for `singular-value-interlacing`.
@isnad1 id=eq.1h5v.s8.99480ac7a3bc from=translated src=- shape=c6d9134c vocab=5f9c5507
-/
theorem transpose_mul_eq_selected_omitted_grams (A : Matrix m n ℝ)
    (f : p → m) (hf : Function.Injective f) :
    Aᵀ * A = (A.submatrix f id)ᵀ * A.submatrix f id +
      (A.submatrix (Subtype.val : {i : m // i ∉ Set.range f} → m) id)ᵀ *
        A.submatrix (Subtype.val : {i : m // i ∉ Set.range f} → m) id := by
  classical
  let : Fintype (Set.range f) := Subtype.fintype (fun i => i ∈ Set.range f)
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    Function.id_def, Matrix.add_apply]
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ Set.range f)
    (fun k => A k i * A k j)
  have hselected : (∑ k : Set.range f, A k i * A k j) =
      ∑ k : p, A (f k) i * A (f k) j := by
    exact ((Equiv.ofInjective f hf).sum_comp (fun k : Set.range f => A k i * A k j)).symm
  rw [hselected] at hsplit
  exact hsplit.symm

end NLAlib

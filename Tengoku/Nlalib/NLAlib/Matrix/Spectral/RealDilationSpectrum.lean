import Tengoku.Nlalib.NLAlib.Matrix.Spectral.RealDilation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Decreasing eigenvalues of real rectangular dilation

The sorted dilation list is the row-side padded singular list followed by the
reversed negative column-side padded list. This single formula handles tall,
wide and empty matrices. Source: Bhatia 1997, Section III.4; supports `lidskii`.
-/
noncomputable section
open scoped Matrix
namespace NLAlib

/-- The decreasing paired spectrum of the real dilation: padded positive values,
then reversed padded negative values. Bhatia 1997, Section III.4.-/
def realDilationSpectrum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Fin (m + n) → ℝ :=
  fun k => if (k : ℕ) < m then singularValues A k else -singularValues A (m + n - 1 - k)

/-- The explicit paired list decreases, including all the rectangular zeros.
Bhatia 1997, Section III.4; no positive-rank hypothesis is needed.-/
theorem realDilationSpectrum_antitone {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Antitone (realDilationSpectrum A) := by
  intro i j hij
  have hij' : (i : ℕ) ≤ j := hij
  simp only [realDilationSpectrum]
  split_ifs with hj hi hi
  · exact singularValues_antitone A hij'
  · omega
  · exact (neg_nonpos.mpr (singularValues_nonneg A _)).trans (singularValues_nonneg A _)
  · exact neg_le_neg (singularValues_antitone A (by omega))

private def dilationOrderingEquiv (m n : ℕ) : Fin m ⊕ Fin n ≃ Fin (m + n) :=
  (Equiv.sumCongr (Equiv.refl (Fin m)) (Fin.revPerm (n := n))).trans finSumFinEquiv

end NLAlib

import Tengoku.Nlalib.NLAlib.Matrix.Functions.HermitianCalculus
import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Equations 2.1.27–2.1.28 — Hermitian dilation identities

Main declaration: `NLAlib.dilation_identities`.

Atlas: `hermitian-dilation`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Definition 2.1.5 and equations (2.1.27–28), printed pp. 24–25.
-/
open scoped Matrix.Norms.L2Operator

namespace NLAlib

open Matrix

private lemma isHermitian {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : (dilation A).IsHermitian := by
  unfold dilation
  simp [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose]

end NLAlib

open NLAlib

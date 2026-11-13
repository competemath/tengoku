import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.CStarAlgebra.SpectrumPerturbation
import Tengoku.Nlalib.NLAlib.Probability.Free.WordMatrixCreationNorm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Actual free linear reference spectra and their deterministic mean

Faithfulness of the concrete coefficient representation preserves the real
spectrum of the deterministic mean. Normal spectral perturbation and the
dimension-free creation norm estimate then put the two actual spectra within
twice the square root of the coefficient square mass.

This proves the concrete spectral enclosure used in Lemma 4.7 of
Bandeira--Cipolloni--Schroeder--van Handel, arXiv:2406.11453v2. The sharp
Gaussian/free comparison is a separate theorem.
-/

noncomputable section
set_option autoImplicit false
open scoped ComplexOrder

namespace NLAlib

variable {D ι : Type*} [Fintype D] [DecidableEq D]

end NLAlib

end

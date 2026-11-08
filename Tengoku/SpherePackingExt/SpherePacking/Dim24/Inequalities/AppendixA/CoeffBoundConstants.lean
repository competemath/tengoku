/-
Numeric constants for coefficient/tail bounds used throughout Appendix A.

These are kept in a standalone module to avoid duplicating the same constants across developments
and to keep import dependencies minimal.
-/
module
public import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Coefficient majorant constants used in Appendix A.

These explicit real numbers appear in `appendix.txt` as coarse bounds for coefficients of the
`phi1`/`phi2` core terms and for the numerator tail estimate of `psi_I`. The accompanying lemmas
record their numeric expansions and simple comparisons needed by later bounds.
-/

open scoped Real

namespace SpherePacking.Dim24.AppendixA

noncomputable section

/-- Coarse global coefficient majorant constant used in the `varphi` bounds in Appendix A.-/
@[expose] public def Cvarphi : ℝ := 513200655360

/-- Coefficient majorant constant for the `phi2` core term (built from `E₄` and `E₆`).-/
@[expose] public def Cphi2Core : ℝ := 683726400

/-- Coefficient majorant constant for the `phi1` core term (involving `E₂` and `phi2Core`).-/
@[expose] public def Cphi1Core : ℝ := 34212326400

/-!
### Tail-majorant constant for `ψ_I` (`appendix.txt`)
-/

/-- Coarse coefficient bound constant for the `ψ_I` numerator tail estimate in Appendix A.-/
@[expose] public def Cpsi : ℝ := 44 * 16 * (24 : ℝ) ^ (7 : ℕ)

end

end SpherePacking.Dim24.AppendixA

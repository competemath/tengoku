import Tengoku.ErdosLean.ErdosLean.Erdos996.Statement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Assembly sub-lemma 10 (ParsevalTail): the Fourier tail via Parseval

Blueprint §10. Generic: for `f ∈ L²(𝕋)`, `‖f - S_N f‖₂² = ∑_{|r| > N} |f̂(r)|²`
(`tsum_sq_fourierCoeff` applied to `f - S_N f`, whose coefficients are `f̂(r) 1_{|r|>N}`).
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos996
namespace Asm

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

end Asm
end Erdos996

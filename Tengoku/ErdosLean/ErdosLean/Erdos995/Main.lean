import Tengoku.ErdosLean.ErdosLean.Erdos995.Parts.UpperL2
import Tengoku.ErdosLean.ErdosLean.Erdos995.Parts.UpperBorelCantelli
import Tengoku.ErdosLean.ErdosLean.Erdos995.Parts.UpperDyadic
import Tengoku.ErdosLean.ErdosLean.Erdos995.Parts.Params
import Tengoku.ErdosLean.ErdosLean.Erdos995.Parts.Sequence
import Tengoku.ErdosLean.ErdosLean.Erdos995.Parts.StageProb
import Tengoku.ErdosLean.ErdosLean.Erdos995.Parts.BorelCantelli
import Tengoku.ErdosLean.ErdosLean.Erdos995.Parts.Atoms
import Tengoku.ErdosLean.ErdosLean.Erdos995.Parts.GlobalL2
import Tengoku.ErdosLean.ErdosLean.Erdos995.Parts.MeanZero
import Tengoku.ErdosLean.ErdosLean.Erdos995.Parts.Master
import Tengoku.ErdosLean.ErdosLean.Erdos995.Parts.Growth
import Tengoku.ErdosLean.ErdosLean.Erdos995.Parts.Consequences

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős Problem 995: main theorem (assembly)

`erdos_995 : Erdos995Answer`, i.e. Erdős's upper bound `o(N (log N)^{1/2+ε})`, Ho's lower bound
`limsup ∑_{k<N} f(n_k x) / (N (log N)^{1/2-ε}) = +∞`, the critical exponent `1/2`, and the negative
answer to the `o(N √(log log N))` question. All analytic input is in `ErdosLean/Erdos995/Parts/`.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos995

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

/-- **Erdős's upper bound** (in fact for every sequence `n`, lacunary or not).
@isnad1 id=erdosupp.0h0v.s0.2bd4a2bccb86 from=translated src=- shape=45709ebd vocab=2bd4a2bc
-/
theorem erdosUpperBound : ErdosUpperBound := by
  intro f n _ ε hε
  have h : ∀ᵐ x ∂μ𝕋, ∀ m : ℕ, ∀ᶠ j : ℕ in atTop, Upper.sumNorm f n (2 ^ (j + 1)) x ≤
      (1 / ((m : ℝ) + 1)) * ((2 : ℝ) ^ j * (j : ℝ) ^ ((1 : ℝ) / 2 + ε)) :=
    ae_all_iff.2 fun m => Upper.ae_eventually_sumNorm_le f n hε (by positivity)
  filter_upwards [h] with x hx
  exact Upper.isLittleO_of_dyadic (fun N => lacSum f n x N) (fun M => Upper.sumNorm f n M x)
    (fun N => Upper.norm_lacSum_le_sumNorm f n x (Nat.lt_pow_succ_log_self (by norm_num) N).le)
    hε hx

end Erdos995

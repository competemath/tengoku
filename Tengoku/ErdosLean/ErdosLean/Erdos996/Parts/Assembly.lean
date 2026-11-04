import Tengoku.ErdosLean.ErdosLean.Erdos996.Parts.SpikeGe
import Tengoku.ErdosLean.ErdosLean.Erdos996.Parts.SpikeFourierSupport
import Tengoku.ErdosLean.ErdosLean.Erdos996.Parts.SpikeTail
import Tengoku.ErdosLean.ErdosLean.Erdos996.Parts.DigitIndependence
import Tengoku.ErdosLean.ErdosLean.Erdos996.Parts.BlockFloor
import Tengoku.ErdosLean.ErdosLean.Erdos996.Parts.TrialSignal
import Tengoku.ErdosLean.ErdosLean.Erdos996.Parts.Asm.Construction
import Tengoku.ErdosLean.ErdosLean.Erdos996.Parts.Asm.Params
import Tengoku.ErdosLean.ErdosLean.Erdos996.Parts.Asm.Sequence
import Tengoku.ErdosLean.ErdosLean.Erdos996.Parts.Asm.SpikeMeasure
import Tengoku.ErdosLean.ErdosLean.Erdos996.Parts.Asm.HitWindow
import Tengoku.ErdosLean.ErdosLean.Erdos996.Parts.Asm.StageProb
import Tengoku.ErdosLean.ErdosLean.Erdos996.Parts.Asm.Atoms
import Tengoku.ErdosLean.ErdosLean.Erdos996.Parts.Asm.PartialSumL2
import Tengoku.ErdosLean.ErdosLean.Erdos996.Parts.Asm.GlobalL2
import Tengoku.ErdosLean.ErdosLean.Erdos996.Parts.Asm.Master
import Tengoku.ErdosLean.ErdosLean.Erdos996.Parts.Asm.ParsevalTail
import Tengoku.ErdosLean.ErdosLean.Erdos996.Parts.Asm.TailSum
import Tengoku.ErdosLean.ErdosLean.Erdos996.Parts.Asm.TailAsymp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős 996: global assembly (gaps G4, G5, G6)

The counterexample is the explicit construction of `Parts/Asm/Construction.lean` with the
parameter `A` supplied by `tail_asymp`.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos996

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

end Erdos996

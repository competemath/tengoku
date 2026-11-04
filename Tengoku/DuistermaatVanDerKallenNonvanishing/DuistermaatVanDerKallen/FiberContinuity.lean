import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.FiberTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Continuous dependence for the actual chosen Laurent transport trajectories.
A common proper-radius bound places the entire family in one compact regular
region. Gronwall then gives a Lipschitz estimate in the initial point. -/

open Set
open scoped Topology NNReal

namespace DuistermaatVanDerKallen

noncomputable section

/-- Proper radius is continuous on each Laurent fiber.-/
theorem fiberProperRadius_continuous {d : ℕ} (f : MultiLaurent d) (s : ℂ) :
    Continuous (fun z : LaurentFiber f s => ‖torusEmbed z.val‖) := by
  apply Continuous.norm
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (torusEmbed_contDiffAt_real z.property.1).continuousAt.comp
    continuous_subtype_val.continuousAt

end
end DuistermaatVanDerKallen

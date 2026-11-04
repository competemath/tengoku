import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.AnalyticTransport
import Tengoku.Seed.Analysis.Analytic.Within

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Analytic dependence of the actual complete Laurent segment transport,
including varying velocity, initial point, and time. The admissible parameter
set carries exactly the existing good-segment hypothesis. -/

open Set
open scoped Topology

namespace DuistermaatVanDerKallen

noncomputable section

/-- Initial points and velocities for which the manuscript's segment-exclusion
hypothesis guarantees complete transport.-/
def admissibleSegmentParameters {d : ℕ} (f : MultiLaurent d) : Set (ℂ × (Fin d → ℂ)) :=
  {p | (∀ i, p.2 i ≠ 0) ∧ GoodSegment f (laurentEval f p.2) p.1}

end

end DuistermaatVanDerKallen

import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_ModularityProps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

set_option maxHeartbeats 400000

noncomputable section

def _root_.Tengoku.FltAnthropic.Mlc1IsModularModelOfExactConductorLevel (W : WeierstrassCurve ℤ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ Squarefree N ∧
    (∀ q : ℕ, q.Prime → (q ∣ N ↔ (q : ℤ) ∣ W.Δ)) ∧
    W.IsModularModelOfLevel N

def _root_.Tengoku.FltAnthropic.Mlc1ModularityLiftingAtConductor (p : ℕ) : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 → W.IsSemistableModel → W.ModRepIsIrreducible p →
    W.IsResiduallyModular p → Mlc1IsModularModelOfExactConductorLevel W

def _root_.Tengoku.FltAnthropic.Mlc1RowStatement : Prop :=
  ∀ (p : ℕ), p = 3 ∨ p = 5 → Mlc1ModularityLiftingAtConductor p

end
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)

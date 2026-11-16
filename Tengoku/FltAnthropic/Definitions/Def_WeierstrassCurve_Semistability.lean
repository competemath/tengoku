import Tengoku.Seed.NumberTheory.Padics.PadicVal.Basic
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_FreyPackage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

namespace FreyCurve

open Tengoku.FltAnthropic.FreyPackage

def c₄Int (P : FreyPackage) : ℤ :=
  (P.a ^ P.p) ^ 2 + P.a ^ P.p * P.b ^ P.p + (P.b ^ P.p) ^ 2

def _root_.WeierstrassCurve.IsSemistableAt (W : WeierstrassCurve ℚ) (q : ℕ) : Prop :=
  padicValRat q W.Δ = 0 ∨ padicValRat q W.c₄ = 0

def _root_.WeierstrassCurve.IsSemistable (W : WeierstrassCurve ℚ) : Prop :=
  ∀ q : ℕ, q.Prime → W.IsSemistableAt q

end FreyCurve
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)

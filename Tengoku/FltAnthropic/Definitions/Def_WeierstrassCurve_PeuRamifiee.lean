import Tengoku.Seed.NumberTheory.Padics.PadicVal.Basic
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Weierstrass
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_AtPPackage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Classical in
section

namespace WeierstrassCurve

def IsPeuRamifieeAt (W : WeierstrassCurve ℚ) (p ℓ : ℕ) : Prop :=
  (p : ℤ) ∣ padicValRat ℓ W.Δ

end WeierstrassCurve

namespace ModularCurve

def peuRamifieeGuard (W : WeierstrassCurve ℚ) (p ℓ : ℕ) : Ideal HeckeAlg → Prop :=
  fun _ => W.IsPeuRamifieeAt p ℓ

end ModularCurve

end

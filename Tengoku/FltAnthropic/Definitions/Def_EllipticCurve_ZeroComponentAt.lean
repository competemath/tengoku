import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Point
import Tengoku.Seed.RingTheory.Valuation.ValuationSubring
import Tengoku.Seed.RingTheory.LocalRing.ResidueField.Basic
import Tengoku.Seed.FieldTheory.IsAlgClosed.AlgebraicClosure
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_GaloisRep

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace WeierstrassCurve

open scoped WeierstrassCurve.Affine

def InZeroComponentAt (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) : Prop :=
  P = 0 ∨ ∃ (x y : AlgebraicClosure ℚ)
      (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y),
    P = .some x y h ∧
      (x ∉ A ∨ ∃ (hx : x ∈ A) (hy : y ∈ A),
        (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).toAffine.Nonsingular
          (IsLocalRing.residue A ⟨x, hx⟩) (IsLocalRing.residue A ⟨y, hy⟩))

end WeierstrassCurve

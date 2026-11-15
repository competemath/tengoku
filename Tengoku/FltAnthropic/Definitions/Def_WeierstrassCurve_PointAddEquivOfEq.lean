import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace WeierstrassCurve

variable {L : Type*} [Field L] [DecidableEq L]

def pointAddEquivOfEq {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point :=
  e ▸ AddEquiv.refl _

/--
@isnad1 id=eq.0h2v.s6.f6eb7e20c46b from=translated src=- shape=8c5a29cd vocab=960b49e6
-/
@[simp] theorem pointAddEquivOfEq_refl (W : WeierstrassCurve L) :
    pointAddEquivOfEq (rfl : W = W) = AddEquiv.refl _ := rfl

/--
@isnad1 id=eq.1h3v.s6.aa93f03c84aa from=translated src=- shape=d274bea2 vocab=95ed17fa
-/
theorem pointAddEquivOfEq_symm {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) :
    (pointAddEquivOfEq e).symm = pointAddEquivOfEq e.symm := by subst e; rfl

/--
@isnad1 id=eq.2h5v.s7.5d7da2408834 from=translated src=- shape=3f7275f7 vocab=5475c089
-/
theorem pointAddEquivOfEq_some {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂)
    {x y : L} (h : W₁.toAffine.Nonsingular x y) :
    pointAddEquivOfEq e (.some x y h) = .some x y (e ▸ h) := by subst e; rfl

end WeierstrassCurve

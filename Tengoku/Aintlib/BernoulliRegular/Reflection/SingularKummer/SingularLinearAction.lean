module

public import Tengoku.Aintlib.BernoulliRegular.Reflection.SingularKummer.SingularZMod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Singular Kummer: multiplicative actions as additive `ZMod p`-linear actions

This file converts multiplicative automorphism actions on `p`-torsion
commutative groups into additive `ZMod p`-linear actions.  Applied to the
singular exact sequence, multiplicative equivariance of `S → A[p]` becomes
linear equivariance of the corresponding `ZMod p`-linear map.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace SingularLinearAction

variable {p : ℕ}
variable {G H D : Type*} [CommGroup G] [CommGroup H] [Monoid D]
variable [Module (ZMod p) (Additive G)] [Module (ZMod p) (Additive H)]

/-- A multiplicative equivalence between `p`-torsion commutative groups is
`ZMod p`-linear after passing to additive notation.-/
def mulEquivToAdditiveZModLinearEquiv (e : G ≃* H) :
    Additive G ≃ₗ[ZMod p] Additive H :=
  { e.toMonoidHom.toAdditive.toZModLinearMap p with
    invFun := e.symm.toMonoidHom.toAdditive
    left_inv := by
      intro x
      apply Additive.ext
      simp
    right_inv := by
      intro y
      apply Additive.ext
      simp }

/--
@isnad1 id=eq.0h5v.s8.b9eb891d34ed from=translated src=- shape=e20f6d0a vocab=7f0e4d3e
-/
@[simp]
theorem mulEquivToAdditiveZModLinearEquiv_apply_toMul
    (e : G ≃* H) (x : Additive G) :
    (mulEquivToAdditiveZModLinearEquiv (p := p) e x).toMul = e x.toMul :=
  rfl

/-- A multiplicative action by automorphisms gives a linear action after
passing to additive notation.-/
def mulActionToAdditiveLinearAction (ρ : D →* G ≃* G) :
    D →* Additive G ≃ₗ[ZMod p] Additive G where
  toFun d := mulEquivToAdditiveZModLinearEquiv (p := p) (ρ d)
  map_one' := by
    ext x
    change (ρ 1) x.toMul = x.toMul
    simp
  map_mul' a b := by
    ext x
    change (ρ (a * b)) x.toMul = ((ρ a) * (ρ b)) x.toMul
    rw [map_mul]

/--
@isnad1 id=eq.0h6v.s10.183ef669931b from=translated src=- shape=067d305d vocab=4b4d932c
-/
@[simp]
theorem mulActionToAdditiveLinearAction_apply_toMul
    (ρ : D →* G ≃* G) (d : D) (x : Additive G) :
    (mulActionToAdditiveLinearAction (p := p) ρ d x).toMul =
      ρ d x.toMul :=
  rfl

/-- Multiplicative equivariance becomes linear equivariance after passing to
additive `ZMod p`-modules.
@isnad1 id=eq.1h9v.s12.830027f92fb0 from=translated src=- shape=bc85bd98 vocab=707b7ec4
-/
theorem linear_equivariant_of_multiplicative_equivariant
    (φ : G →* H) (ρG : D →* G ≃* G) (ρH : D →* H ≃* H)
    (hφ : ∀ (d : D) (x : G), φ (ρG d x) = ρH d (φ x))
    (d : D) (x : Additive G) :
    φ.toAdditive.toZModLinearMap p
        (mulActionToAdditiveLinearAction (p := p) ρG d x) =
      mulActionToAdditiveLinearAction (p := p) ρH d
        (φ.toAdditive.toZModLinearMap p x) := by
  apply Additive.ext
  change φ (ρG d x.toMul) = ρH d (φ x.toMul)
  exact hφ d x.toMul

namespace SingularPair

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

end SingularPair

end SingularLinearAction

end SingularKummer
end Reflection
end BernoulliRegular

end

end

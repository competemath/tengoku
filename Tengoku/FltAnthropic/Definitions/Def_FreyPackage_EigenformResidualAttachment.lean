import Tengoku.Seed.RepresentationTheory.Basic
import Tengoku.Seed.NumberTheory.NumberField.Basic
import Tengoku.Seed.FieldTheory.Galois.Basic
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_ModularRep
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_FreyPackage
import Tengoku.FltAnthropic.Definitions.Def_EllipticCurve_FrobeniusTrace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine.Point
open scoped CongruenceSubgroup

namespace Tengoku.FltAnthropic.FreyPackage

noncomputable local instance instDecEqQbarCongruenceRecovery :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

def EigenformResidualAttachmentAt (P : FreyPackage) (M : ℕ) : Prop :=
  ∀ (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2), g.IsNormalizedEigenform →
    ∀ (𝔪 : Ideal (integralClosure ℤ ℂ)), 𝔪.IsMaximal → (P.p : integralClosure ℤ ℂ) ∈ 𝔪 →
      ∃ (K : Type) (_ : Field K) (_ : Algebra (ZMod P.p) K)
        (V : Type) (_ : AddCommGroup V) (_ : Module K V)
        (ρ : Representation K (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V)
        (ψ : integralClosure ℤ ℂ →+* K)
        (F : Type) (_ : Field F) (_ : NumberField F) (_ : IsGalois ℚ F)
        (_ : Algebra F (AlgebraicClosure ℚ)) (_ : IsScalarTower ℚ F (AlgebraicClosure ℚ)),
        𝔪 ≤ RingHom.ker ψ ∧
        Module.finrank K V = 2 ∧
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤
          (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) P.freyCurve P.p).ker ⊓
            ρ.ker ∧
        (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ≠ P.p →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
            ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
              ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g ℓ ∧
                LinearMap.trace K V (ρ τ) = ψ a) ∧
        (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ≠ P.p →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
            ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
              LinearMap.det (ρ τ) = (ℓ : K))

end Tengoku.FltAnthropic.FreyPackage
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)

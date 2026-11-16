import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Adic
import Tengoku.FltAnthropic.Definitions.Def_CuspidalType_IsCuspidalOfType
import Tengoku.FltAnthropic.Definitions.Def_HeckeGalois_EichlerShimura

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
local notation α "^+" M:51 => FixedPoints.addSubgroup M α

set_option autoImplicit false

noncomputable section

namespace FullLevelTate

structure Datum (q : ℕ) [Fact q.Prime] (M' : ℕ) (O' : Type) [CommRing O'] [IsLocalRing O'] :
    Type 1 where

  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module O' V]
  [instFree : Module.Free O' V]
  [instFinite : Module.Finite O' V]

  gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End O' V

  gal_isAdicContinuous : GaloisActionIsAdicContinuous O' gal

  gl2 : CuspidalType.GL2 q →* Module.End O' V

  hecke : ModularCurve.HeckeAlg →+* Module.End O' V

  gal_comm_gl2 : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : CuspidalType.GL2 q),
    gal σ * gl2 x = gl2 x * gal σ

  hecke_comm_gal : ∀ (t : ModularCurve.HeckeAlg) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
    hecke t * gal σ = gal σ * hecke t

  hecke_comm_gl2 : ∀ (t : ModularCurve.HeckeAlg) (x : CuspidalType.GL2 q),
    hecke t * gl2 x = gl2 x * hecke t

  unramified : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ q → ¬ ℓ ∣ M' → (ℓ : O') ∉ IsLocalRing.maximalIdeal O' →
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, gal σ = 1

  eichlerShimura : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ.Coprime q), ¬ ℓ ∣ M' →
    (ℓ : O') ∉ IsLocalRing.maximalIdeal O' →
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
        gal σ * gal σ - hecke (ModularCurve.heckeGen ⟨ℓ, hℓ⟩) * gal σ
          + (ℓ : O') • gl2 (CuspidalType.scalarElem q (ZMod.unitOfCoprime ℓ hℓq)) = 0

attribute [instance] Datum.instAddCommGroup Datum.instModule Datum.instFree Datum.instFinite

end FullLevelTate

end
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)

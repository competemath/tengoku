import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB1TargetNormalForm
import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB1ModuleExtraction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Genuine-module isomorphism for the live-path normal form

The source and target coordinate equivalences conjugate both structure maps.
This file packages those coordinates as a genuine `FiniteB1Rep` and upgrades
their product to a `B1Model`-linear module isomorphism.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.ExhaustivenessReduction

universe u

variable (K : Type u) [Field K]

namespace SplittingFlag

variable {K}

/-- The abstract seven-block normal representation attached to a splitting
flag.-/
def normalRep (D : FiniteB1Rep K) (F : SplittingFlag K D) :
    FiniteB1Rep K where
  V₁ := FGModuleCat.of K (NormalV₁ D F)
  V₂ := FGModuleCat.of K (NormalV₂ D F)
  loop := FGModuleCat.ofHom (normalLoop D F)
  stem := FGModuleCat.ofHom (normalStem D F)
  loop_sq := normalLoop_sq D F

/-! ### Genuine-module normal-form isomorphism -/

def normalCarrierLinearEquiv (D : FiniteB1Rep K)
    (F : SplittingFlag K D) :
    FiniteB1Rep.Carrier K (normalRep D F) ≃ₗ[K]
      FiniteB1Rep.Carrier K D := by
  change (NormalV₁ D F × NormalV₂ D F) ≃ₗ[K] (D.V₁ × D.V₂)
  exact (normalV₁Equiv D F).prodCongr (normalV₂Equiv D F)

theorem normalCarrierLinearEquiv_e1 (D : FiniteB1Rep K)
    (F : SplittingFlag K D)
    (v : FiniteB1Rep.Carrier K (normalRep D F)) :
    normalCarrierLinearEquiv D F (e1 K • v) =
      e1 K • normalCarrierLinearEquiv D F v := by
  rw [FiniteB1Rep.e1_smul, FiniteB1Rep.e1_smul]
  apply FiniteB1Rep.carrier_ext K D
  · rfl
  · change normalV₂Equiv D F 0 = 0
    rw [map_zero]

theorem normalCarrierLinearEquiv_e2 (D : FiniteB1Rep K)
    (F : SplittingFlag K D)
    (v : FiniteB1Rep.Carrier K (normalRep D F)) :
    normalCarrierLinearEquiv D F (e2 K • v) =
      e2 K • normalCarrierLinearEquiv D F v := by
  rw [FiniteB1Rep.e2_smul, FiniteB1Rep.e2_smul]
  apply FiniteB1Rep.carrier_ext K D
  · change normalV₁Equiv D F 0 = 0
    rw [map_zero]
  · rfl

theorem normalCarrierLinearEquiv_x (D : FiniteB1Rep K)
    (F : SplittingFlag K D)
    (v : FiniteB1Rep.Carrier K (normalRep D F)) :
    normalCarrierLinearEquiv D F (x K • v) =
      x K • normalCarrierLinearEquiv D F v := by
  rw [FiniteB1Rep.x_smul, FiniteB1Rep.x_smul]
  apply FiniteB1Rep.carrier_ext K D
  · exact normalV₁Equiv_loop D F v.1
  · change normalV₂Equiv D F 0 = 0
    rw [map_zero]

end SplittingFlag

end QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.ExhaustivenessReduction

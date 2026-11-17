/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.CohFT.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Genus-zero cohomological field theories

The all-genus CohFT is the primary object. This file packages its genus-zero
restriction for derived constructions such as the Frobenius product and WDVV.
-/

@[expose] public section

namespace AxiomaticGW

/-- The genus-zero restriction of a full unital CohFT.-/
structure GenusZeroCohFT (R V : Type*) [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (C : StableCurveCohomology R) where
  /-- The state-space metric.-/
  pairing : SymmetricPerfectPairing R V
  /-- The flat unit.-/
  unit : V
  /-- The genus-zero class for a stable finite label type.-/
  omega : (S : Type) → [Fintype S] → (h : StableArity 0 S) →
    MultilinearMap R (fun _ : S ↦ V) (C.H 0 S)
  /-- Naturality under relabelling.-/
  relabel : ∀ (S T : Type) [Fintype S] [Fintype T]
      (hS : StableArity 0 S) (hT : StableArity 0 T) (e : S ≃ T),
    (C.rename 0 S T hS hT e).toLinearMap.compMultilinearMap
        ((omega S hS).domDomCongr e) = omega T hT
  /-- Inserting the unit is forgetful pullback.-/
  unit_insert : ∀ (S : Type) [Fintype S] (h : StableArity 0 S) (a : S → V),
    omega (Option S) (StableArity.option h)
        (fun | none => unit | some s => a s) =
      C.forget 0 S h (omega S h a)
  /-- Separating genus-zero gluing.-/
  separating : ∀ (S T : Type) [Fintype S] [Fintype T]
      (h₁ : StableArity 0 (Option S)) (h₂ : StableArity 0 (Option T)),
    pairing.pairContractTarget (omega (Option S) h₁) (omega (Option T) h₂) =
      (C.separating 0 0 S T h₁ h₂).toLinearMap.compMultilinearMap
        (omega (S ⊕ T) (StableArity.separating h₁ h₂))
  /-- The three-point class with one unit insertion is the metric.-/
  normalization : ∀ a : Fin 2 → V,
    omega (Option (Fin 2)) StableArity.zero_option_fin_two
        (fun | none => unit | some i => a i) =
      algebraMap R (C.H 0 (Option (Fin 2))) (pairing.form (a 0) (a 1))

namespace CohFT

variable {R V : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  {C : StableCurveCohomology R}

/-- Restrict a full all-genus CohFT to genus zero.-/
def toGenusZeroCohFT (Ω : CohFT R V C) : GenusZeroCohFT R V C where
  pairing := Ω.pairing
  unit := Ω.unit
  omega := Ω.omega 0
  relabel := Ω.relabel 0
  unit_insert := Ω.unit_insert 0
  separating := Ω.separating 0 0
  normalization := Ω.normalization

end CohFT

end AxiomaticGW

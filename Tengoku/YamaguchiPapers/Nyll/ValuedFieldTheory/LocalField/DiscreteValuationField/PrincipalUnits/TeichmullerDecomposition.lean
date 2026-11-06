/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.TeichmullerLift
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Teichmuller and principal-unit decompositions

Decomposes valuation-ring units and field units into residue roots, first principal units,
and a uniformizer factor.
-/

namespace LocalFieldTheory

open ValuationTheory
open ValuationTheory.DiscreteValuationField.ResidueField

noncomputable section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

namespace higherPrincipalUnitGroup

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- Multiplication of a Teichmuller representative and a first principal unit,
as a homomorphism into the full valuation-ring unit group.-/
def residueRootsTimesPrincipalUnitMulHom
    [Finite F.residueField] :
    higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
        higherPrincipalUnitGroup F 1 →*
      F.valuationSubringˣ where
  toFun z := (z.1 : F.valuationSubringˣ) * (z.2 : F.valuationSubringˣ)
  map_one' := one_mul 1
  map_mul' := by
    intro x y
    change ((x.1 : F.valuationSubringˣ) * (y.1 : F.valuationSubringˣ)) *
        ((x.2 : F.valuationSubringˣ) * (y.2 : F.valuationSubringˣ)) =
      ((x.1 : F.valuationSubringˣ) * (x.2 : F.valuationSubringˣ)) *
        ((y.1 : F.valuationSubringˣ) * (y.2 : F.valuationSubringˣ))
    exact mul_mul_mul_comm _ _ _ _

/--
The specified map is surjective: `Function.Surjective
(higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom F)`.
@isnad1 id=surjecti.0h2v.s14.a5e4ba55b173 from=translated src=- shape=0754308d vocab=68fe6b36
-/
theorem residueRootsTimesPrincipalUnitMulHom_surjective
    [Finite F.residueField] :
    Function.Surjective
      (higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom F) := by
  intro u
  rcases higherPrincipalUnitGroup.residueRootsOfUnityResidueHom_surjective
      (F := F) (higherPrincipalUnitGroup.residueUnitHom F u) with
    ⟨zeta, hzeta⟩
  have hzeta' :
      higherPrincipalUnitGroup.residueUnitHom F
          (zeta : F.valuationSubringˣ) =
        higherPrincipalUnitGroup.residueUnitHom F u := by
    simpa [higherPrincipalUnitGroup.residueRootsOfUnityResidueHom] using hzeta
  let p : F.valuationSubringˣ := (zeta : F.valuationSubringˣ)⁻¹ * u
  have hp : p ∈ higherPrincipalUnitGroup F 1 := by
    rw [← higherPrincipalUnitGroup.residueUnitHom_eq_one_iff F p]
    dsimp [p]
    rw [map_mul, map_inv, hzeta', inv_mul_cancel]
  refine ⟨(zeta, ⟨p, hp⟩), ?_⟩
  change (zeta : F.valuationSubringˣ) * p = u
  exact mul_inv_cancel_left (zeta : F.valuationSubringˣ) u

/--
The specified map is injective: `Function.Injective
(higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom F)`.
@isnad1 id=injectiv.0h2v.s14.fdcabdf4f629 from=translated src=- shape=0754308d vocab=2756e61c
-/
theorem residueRootsTimesPrincipalUnitMulHom_injective
    [Finite F.residueField] :
    Function.Injective
      (higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom F) := by
  intro x y hxy
  have hxprincipal :
      higherPrincipalUnitGroup.residueUnitHom F
          (x.2 : F.valuationSubringˣ) = 1 :=
    (higherPrincipalUnitGroup.residueUnitHom_eq_one_iff
      F (x.2 : F.valuationSubringˣ)).2 x.2.property
  have hyprincipal :
      higherPrincipalUnitGroup.residueUnitHom F
          (y.2 : F.valuationSubringˣ) = 1 :=
    (higherPrincipalUnitGroup.residueUnitHom_eq_one_iff
      F (y.2 : F.valuationSubringˣ)).2 y.2.property
  have hmul :
      (x.1 : F.valuationSubringˣ) * (x.2 : F.valuationSubringˣ) =
        (y.1 : F.valuationSubringˣ) * (y.2 : F.valuationSubringˣ) := by
    simpa [higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom]
      using hxy
  have hresroot :
      higherPrincipalUnitGroup.residueRootsOfUnityResidueHom F x.1 =
        higherPrincipalUnitGroup.residueRootsOfUnityResidueHom F y.1 := by
    have hres :=
      congrArg (higherPrincipalUnitGroup.residueUnitHom F) hmul
    simpa [higherPrincipalUnitGroup.residueRootsOfUnityResidueHom,
      map_mul, hxprincipal, hyprincipal] using hres
  have hroot :
      x.1 = y.1 :=
    higherPrincipalUnitGroup.residueRootsOfUnityResidueHom_injective
      (F := F) hresroot
  apply Prod.ext
  · exact hroot
  · apply Subtype.ext
    calc
      (x.2 : F.valuationSubringˣ) =
          (x.1 : F.valuationSubringˣ)⁻¹ *
            ((x.1 : F.valuationSubringˣ) *
              (x.2 : F.valuationSubringˣ)) :=
        (inv_mul_cancel_left _ _).symm
      _ = (x.1 : F.valuationSubringˣ)⁻¹ *
            ((y.1 : F.valuationSubringˣ) *
              (y.2 : F.valuationSubringˣ)) := by
        rw [hmul]
      _ = (y.1 : F.valuationSubringˣ)⁻¹ *
            ((y.1 : F.valuationSubringˣ) *
              (y.2 : F.valuationSubringˣ)) := by
        rw [hroot]
      _ = (y.2 : F.valuationSubringˣ) := inv_mul_cancel_left _ _

/--
The specified map is bijective: `Function.Bijective
(higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom F)`.
@isnad1 id=bijectiv.0h2v.s14.8f6c09a1b8bf from=translated src=- shape=0754308d vocab=4c54f251
-/
theorem residueRootsTimesPrincipalUnitMulHom_bijective
    [Finite F.residueField] :
    Function.Bijective
      (higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom F) :=
  ⟨higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom_injective F,
    higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom_surjective F⟩

/-- Unit-level form of the multiplicative unit decomposition:
`O^*` is the product of the lifted `(q - 1)`-roots of unity and `U^1`.-/
noncomputable def valuationSubringUnitsEquivRootsTimesPrincipalUnits
    [Finite F.residueField] :
    higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
        higherPrincipalUnitGroup F 1 ≃*
      F.valuationSubringˣ :=
  MulEquiv.ofBijective
    (higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom F)
    (higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom_bijective F)

/--
The defining evaluation formula for `valuationSubringUnitsEquivRootsTimesPrincipalUnits` is
`higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits F z = (z.1 :
F.valuationSubringˣ) * (z.2 : F.valuationSubringˣ)`.
@isnad1 id=eq.0h3v.s14.110b97143630 from=translated src=- shape=206a7b87 vocab=7aa4ee12
-/
@[simp] theorem valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply
    [Finite F.residueField]
    (z :
      higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
        higherPrincipalUnitGroup F 1) :
    higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits
        F z =
      (z.1 : F.valuationSubringˣ) * (z.2 : F.valuationSubringˣ) :=
  rfl

/-- The natural inclusion of valuation-ring units into field units, kept local
to the principal-unit API to state the field-unit form of the multiplicative unit decomposition.-/
def valuationSubringUnitFieldUnitHom :
    F.valuationSubringˣ →* Kˣ :=
  Units.map F.valuation.valuationSubring.subtype.toMonoidHom

/--
The defining evaluation formula for `coe_valuationSubringUnitFieldUnitHom` is
`((higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u : Kˣ) : K) = (u :
F.valuationSubring)`.
@isnad1 id=eq.0h3v.s9.fe4143f387ad from=translated src=- shape=2c13689f vocab=f6733a88
-/
@[simp] theorem coe_valuationSubringUnitFieldUnitHom_apply
    (u : F.valuationSubringˣ) :
    ((higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u : Kˣ) :
        K) =
      (u : F.valuationSubring) :=
  rfl

/-- The three factors in the multiplicative field-unit decomposition: Teichmuller roots,
first principal units, and an integral power of a fixed uniformizer.-/
abbrev fieldUnitDecompositionFactors [Finite F.residueField] :
    Type u :=
  (higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
      higherPrincipalUnitGroup F 1) × Multiplicative ℤ

/--
Multiplication map from the three the multiplicative unit decomposition factors to field units.-/
noncomputable def rootsPrincipalUnitUniformizerMulHom
    [Finite F.residueField] (ϖ : Kˣ) :
    higherPrincipalUnitGroup.fieldUnitDecompositionFactors F →* Kˣ where
  toFun z :=
    higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
        (z.1.1 : F.valuationSubringˣ) *
      higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
        (z.1.2 : F.valuationSubringˣ) *
      ϖ ^ Multiplicative.toAdd z.2
  map_one' := by
    change higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F 1 *
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F 1 * ϖ ^ (0 : ℤ) = 1
    rw [map_one, zpow_zero, one_mul, one_mul]
  map_mul' := by
    intro x y
    simp [higherPrincipalUnitGroup.fieldUnitDecompositionFactors,
      mul_assoc, mul_left_comm, mul_comm, zpow_add]

/--
The defining evaluation formula for `rootsPrincipalUnitUniformizerMulHom` is
`higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom F ϖ z =
higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F (z.1.1 : F.valuationSubringˣ) *
higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F (z.1.2 : F.valuationSubringˣ) * ϖ ^
Multiplicative.toAdd z.2`.
@isnad1 id=eq.0h4v.s14.e6533751804a from=translated src=- shape=10cba47e vocab=2e89e5b8
-/
@[simp] theorem rootsPrincipalUnitUniformizerMulHom_apply
    [Finite F.residueField] (ϖ : Kˣ)
    (z : higherPrincipalUnitGroup.fieldUnitDecompositionFactors F) :
    higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom F ϖ z =
      higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (z.1.1 : F.valuationSubringˣ) *
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (z.1.2 : F.valuationSubringˣ) *
        ϖ ^ Multiplicative.toAdd z.2 :=
  rfl

end higherPrincipalUnitGroup

end CompleteDVF
end DiscreteValuationField

end

end LocalFieldTheory

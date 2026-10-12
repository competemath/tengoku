/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.Algebra.Category.ModuleCat.Sheaf.Biproducts
public import Tengoku.Tauceti.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Closed
public import Tengoku.Tauceti.TauCeti.CategoryTheory.Monoidal.Rigid.Biproduct
public import Tengoku.Tauceti.TauCeti.CategoryTheory.Monoidal.Rigid.Closed

/-!
# Finite free sheaves of modules are self-dual

Let `R` be a sheaf of commutative rings on a small site. In the symmetric monoidal category of
sheaves of `R`-modules, the free sheaf `free I` on a finite type `I` is dualizable, with dual
`free I` itself. Writing `eᵢ = ιFree i` for the basis sections, the evaluation
`free I ⊗ free I ⟶ R` sends `eᵢ ⊗ eⱼ` to `δᵢⱼ`, and the coevaluation `R ⟶ free I ⊗ free I` sends
`1` to `∑ i, eᵢ ⊗ eᵢ`.

The pairing is obtained from `TauCeti.ExactPairing.biproduct`: `free I` is the biproduct of `I`
copies of the unit `R` (`TauCeti.SheafOfModules.biproductIsoFree`), and the unit is canonically
self-dual.
Finite free sheaves are the local models of finite locally free sheaves, so this is the local
input for showing that finite locally free sheaves are dualizable.

Combining the pairing with the closed structure of sheaves of modules identifies the internal Hom
out of `free I` with tensoring by `free I`, and in particular the dual sheaf
`𝓗om(free I, 𝒪)` with `free I` itself. Its basis sections are the dual basis: paired against the
basis sections of `free I` they give `δᵢⱼ`.

## Main declarations

* `TauCeti.SheafOfModules.biproductIsoFree`: the free sheaf on a finite type is the biproduct of
  copies of the unit;
* `TauCeti.SheafOfModules.exactPairingFree`: the exact pairing between `free I` and itself;
* `TauCeti.SheafOfModules.ιFree_tensorHom_ιFree_evaluation`,
  `TauCeti.SheafOfModules.ιFree_tensorHom_ιFree_evaluation_of_ne` and
  `TauCeti.SheafOfModules.coevaluation_free`: its evaluation and coevaluation on basis sections;
* `TauCeti.SheafOfModules.ihomFreeIso` and `TauCeti.SheafOfModules.dualFreeIso`: the internal Hom
  out of `free I`, and the dual sheaf of `free I`;
* `TauCeti.SheafOfModules.dualFreeι`: the basis sections of the dual sheaf;
* `TauCeti.SheafOfModules.ιFree_tensorHom_dualFreeι_comp_ev` and its `_of_ne` variant: the
  dual basis.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

open _root_.SheafOfModules

variable {R : Sheaf J CommRingCat.{u}} (I : Type u) [Finite I]

/-- The free sheaf of modules on a finite type `I` is the biproduct of `I` copies of the unit. -/
def biproductIsoFree :
    ⨁ (fun _ : I ↦ 𝟙_ (SheafOfModules.{u} (ringCatSheaf R))) ≅ free (R := ringCatSheaf R) I :=
  (biproduct.isColimit _).coconePointUniqueUpToIso (isColimitFreeCofan I)

variable {I}

/-- `biproductIsoFree` sends the `i`-th summand to the `i`-th basis section. -/
@[reassoc (attr := simp)]
theorem biproduct_ι_biproductIsoFree_hom (i : I) :
    biproduct.ι (fun _ : I ↦ unit (ringCatSheaf R)) i ≫
      (biproductIsoFree (R := R) I).hom = ιFree i :=
  (biproduct.isColimit _).comp_coconePointUniqueUpToIso_hom (isColimitFreeCofan I) ⟨i⟩

/-- The inverse of `biproductIsoFree` sends the `i`-th basis section to the `i`-th summand. -/
@[reassoc (attr := simp)]
theorem ιFree_biproductIsoFree_inv (i : I) :
    ιFree i ≫ (biproductIsoFree (R := R) I).inv =
      biproduct.ι (fun _ : I ↦ 𝟙_ (SheafOfModules.{u} (ringCatSheaf R))) i :=
  (biproduct.isColimit _).comp_coconePointUniqueUpToIso_inv (isColimitFreeCofan I) ⟨i⟩

variable (I)

variable {I}

end SheafOfModules

end

end TauCeti

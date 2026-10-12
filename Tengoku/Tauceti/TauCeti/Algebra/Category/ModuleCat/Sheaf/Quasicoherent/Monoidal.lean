/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
public import Tengoku.Tauceti.TauCeti.Algebra.Category.ModuleCat.Sheaf.Free
public import Tengoku.Tauceti.TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Refinement
public import Tengoku.Tauceti.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Presentation
public import Tengoku.Tauceti.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Monoidal
public import Tengoku.Tauceti.TauCeti.CategoryTheory.Sites.CoversTop

/-!
# The tensor product of quasi-coherent sheaves is quasi-coherent

Let `R` be a sheaf of commutative rings on a small site with pullbacks. If `M` and `N` are
quasi-coherent sheaves of `R`-modules, then so is `M ⊗ N`: on a common refinement of covers on
which `M` and `N` have presentations, the restriction of `M ⊗ N` is the tensor product of the
restrictions of `M` and `N` (`SheafOfModules.overTensorIso`), which is presented by the tensor
product of their presentations (`SheafOfModules.Presentation.tensor`). As the unit `R` is free on
one generator, quasi-coherence is a monoidal property of sheaves of modules when the site also
has binary products, and quasi-coherent sheaves of modules then form a monoidal full
subcategory.

The same construction applied to finite presentations gives finite presentations, so finite
presentation is a monoidal property as well when the site has binary products. Applied to
presentations whose generating morphisms are isomorphisms, it gives presentations of the same
kind; this is the local input for the tensor product of locally free sheaves.

## Main declarations

* `SheafOfModules.QuasicoherentData.tensor`: quasi-coherent data for `M ⊗ N` built from
  quasi-coherent data for `M` and for `N`;
* `TauCeti.SheafOfModules.isQuasicoherent_tensorObj`: `M ⊗ N` is quasi-coherent when `M` and
  `N` are;
* `TauCeti.SheafOfModules.isMonoidal_isQuasicoherent`: quasi-coherence is an
  `ObjectProperty.IsMonoidal`;
* `SheafOfModules.QuasicoherentData.isIso_tensor_presentation_generators_π`: the tensor data
  presents `M ⊗ N` by free sheaves where the data for `M` and `N` do;
* `TauCeti.SheafOfModules.isFinitePresentation_tensorObj` and
  `TauCeti.SheafOfModules.isMonoidal_isFinitePresentation`: finite presentation is an
  `ObjectProperty.IsMonoidal`.

## References

* [The Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

variable {C : Type u} [SmallCategory C] [HasPullbacks C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}} {M N : SheafOfModules.{u} (ringCatSheaf R)}

/-- The tensor product of two quasi-coherent sheaves of modules is quasi-coherent. -/
instance isQuasicoherent_tensorObj [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⊗ N).IsQuasicoherent :=
  ((IsQuasicoherent.nonempty_quasicoherentData (M := M)).some.tensor
    (IsQuasicoherent.nonempty_quasicoherentData (M := N)).some).isQuasicoherent

/-- Quasi-coherence of sheaves of modules is a monoidal property: the unit is quasi-coherent and
quasi-coherent sheaves are closed under tensor products. Hence quasi-coherent sheaves of modules
form a monoidal full subcategory (`ObjectProperty.fullMonoidalSubcategory`). -/
instance isMonoidal_isQuasicoherent [HasBinaryProducts C] :
    ObjectProperty.IsMonoidal (isQuasicoherent (ringCatSheaf R)) where
  prop_unit := (isQuasicoherent (ringCatSheaf R)).prop_of_iso
    (freePUnitIsoUnit (ringCatSheaf R)) inferInstance
  prop_tensor M N _ _ := inferInstanceAs (M ⊗ N).IsQuasicoherent

end SheafOfModules

end

end TauCeti

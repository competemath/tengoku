import Tengoku.MiyaokaMoriCharzero.MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorPowers

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Symmetry of the existing tensor module

The symmetry is the image under module sheafification of Mathlib's sectionwise
tensor braiding. Its compatibility with the sheafification unit gives the
formula on the original pure tensor sections. Symmetry and naturality descend
by functoriality, without replacing the tensor module or assuming an isomorphism.

This is the factor-reordering interface for the coefficient pairing and tensor
powers of the paper. The underlying sheaf tensor and its
symmetry are described in Stacks Project, `modules.tex`, `section-tensor-product`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}}

-- Mathlib registers the monoidal structure only for `PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)`,
-- while `X.PresheafOfModules` unfolds to `PresheafOfModules X.ringCatSheaf.obj`, where
-- `Scheme.ringCatSheaf` goes through the non-reducible `sheafCompose`; instance search at reducible
-- transparency cannot see through it, so `MonoidalCategoryStruct X.PresheafOfModules` is never found.
-- Below, the same Mathlib instance is registered again with `R` filled in as `X.presheaf` — not a new
-- definition, only a hint for instance search. The name carries a file-specific suffix: a
-- `local instance` is local only as an **attribute**, the name is still global.
local instance schemePresheafOfModulesMonoidalStructForSymmetry (X : Scheme.{u}) :
    MonoidalCategoryStruct X.PresheafOfModules :=
  PresheafOfModules.monoidalCategoryStruct (R := X.presheaf)

local instance schemePresheafOfModulesMonoidalForSymmetry (X : Scheme.{u}) :
    MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.presheaf)

local instance schemePresheafOfModulesSymmetricForSymmetry (X : Scheme.{u}) :
    SymmetricCategory X.PresheafOfModules :=
  PresheafOfModules.symmetricCategory (R := X.presheaf)

set_option backward.isDefEq.respectTransparency false in
/-- Exchange the two factors of the same sheafified tensor module.-/
def moduleTensorSymmetry (M N : X.Modules) : moduleTensor M N ≅ moduleTensor N M :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (BraidedCategory.braiding (C := X.PresheafOfModules) M.val N.val)

set_option backward.isDefEq.respectTransparency false in
/-- The tensor symmetry descends the sectionwise symmetry along the original unit.
@isnad1 id=eq.0h3v.s14.3b8bf2943b24 from=translated src=- shape=f57297e8 vocab=b6d5c770
-/
theorem moduleTensorSymmetry_fac (M N : X.Modules) :
    moduleTensorSheafificationUnit M N ≫
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
        (moduleTensorSymmetry M N).hom.val =
      (BraidedCategory.braiding (C := X.PresheafOfModules) M.val N.val).hom ≫
        moduleTensorSheafificationUnit N M := by
  exact ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
    (BraidedCategory.braiding (C := X.PresheafOfModules) M.val N.val).hom).symm

set_option backward.isDefEq.respectTransparency false in
/-- Tensor symmetry exchanges the two specified sections.
@isnad1 id=eq.0h6v.s10.1ce5592a12db from=translated src=- shape=13bb6454 vocab=dd7ad6f3
-/
@[simp]
theorem moduleTensorSymmetry_section {M N : X.Modules} {U : X.Opens}
    (s : Γ(M, U)) (t : Γ(N, U)) :
    (moduleTensorSymmetry M N).hom.app U (moduleTensorSection s t) =
      moduleTensorSection t s := by
  exact congrArg (fun f ↦ f.app (op U) (s ⊗ₜ[Γ(X, U)] t))
    (moduleTensorSymmetry_fac M N)

set_option backward.isDefEq.respectTransparency false in
/-- Reversing tensor symmetry is the symmetry with the factors exchanged.
@isnad1 id=eq.0h3v.s5.0a013d473308 from=translated src=- shape=71f1f668 vocab=9a2cd9f5
-/
@[simp]
theorem moduleTensorSymmetry_symm (M N : X.Modules) :
    (moduleTensorSymmetry M N).symm = moduleTensorSymmetry N M := by
  apply Iso.ext
  exact congrArg (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (SymmetricCategory.braiding_swap_eq_inv_braiding M.val N.val).symm

/-- Exchanging the tensor factors twice is the identity morphism.
@isnad1 id=eq.0h3v.s6.2d7f3db1d2f6 from=translated src=- shape=08454c09 vocab=420de993
-/
@[simp]
theorem moduleTensorSymmetry_hom_hom (M N : X.Modules) :
    (moduleTensorSymmetry M N).hom ≫ (moduleTensorSymmetry N M).hom =
      𝟙 (moduleTensor M N) := by
  rw [← moduleTensorSymmetry_symm M N]
  exact (moduleTensorSymmetry M N).hom_inv_id

/-- The inverse tensor symmetry also exchanges the two specified sections.
@isnad1 id=eq.0h6v.s10.2eb133310beb from=translated src=- shape=65255cbc vocab=26e69602
-/
@[simp]
theorem moduleTensorSymmetry_inv_section {M N : X.Modules} {U : X.Opens}
    (s : Γ(M, U)) (t : Γ(N, U)) :
    (moduleTensorSymmetry M N).inv.app U (moduleTensorSection t s) =
      moduleTensorSection s t := by
  change (moduleTensorSymmetry M N).symm.hom.app U (moduleTensorSection t s) = _
  rw [moduleTensorSymmetry_symm, moduleTensorSymmetry_section]

set_option backward.isDefEq.respectTransparency false in
/-- Tensor symmetry is natural in the original two module morphisms.

Proof: `moduleTensorSymmetry` is `sheafification.mapIso` of the sectionwise braiding of
`X.PresheafOfModules`, so apply `sheafification.map` to Mathlib's
`BraidedCategory.braiding_naturality f.val g.val` and split the two `map (_ ≫ _)` with
`Functor.map_comp`. The `MonoidalCategoryStruct.tensorHom` produced by the braiding lemma is
definitionally `PresheafOfModules.Monoidal.tensorHom` (the local instance above is exactly
Mathlib's `PresheafOfModules.monoidalCategoryStruct`), so `exact` closes it under
`backward.isDefEq.respectTransparency false`; a `simp`-normalised version of the same
statement does not unify.
@isnad1 id=eq.0h7v.s14.39f9c46ff02e from=translated src=- shape=0b97f363 vocab=25840433
-/
theorem moduleTensorSymmetry_naturality {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) f.val g.val) ≫
      (moduleTensorSymmetry M' N').hom =
    (moduleTensorSymmetry M N).hom ≫
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) g.val f.val) := by
  have h := congrArg (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (BraidedCategory.braiding_naturality (C := X.PresheafOfModules) f.val g.val)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact h

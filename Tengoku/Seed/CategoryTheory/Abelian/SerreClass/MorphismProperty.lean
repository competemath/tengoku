/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.CategoryTheory.Abelian.SerreClass.Basic
public import Tengoku.Seed.CategoryTheory.Abelian.CommSq
public import Tengoku.Seed.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Tengoku.Seed.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Tengoku.Seed.CategoryTheory.MorphismProperty.Composition
public import Tengoku.Seed.CategoryTheory.MorphismProperty.Retract
public import Tengoku.Seed.CategoryTheory.MorphismProperty.Limits
public import Tengoku.Seed.CategoryTheory.MorphismProperty.IsInvertedBy

/-!
# The class of isomorphisms modulo a Serre class

Let `C` be an abelian category and `P : ObjectProperty C` a Serre class.
We define `P.isoModSerre : MorphismProperty C`, which is the class of
morphisms `f` such that `kernel f` and `cokernel f` satisfy `P`.
We show that `P.isoModSerre` is multiplicative, satisfies the two out
of three property and is stable under retracts. (Similarly, we define
`P.monoModSerre` and `P.epiModSerre`.)

## TODO

* show that a localized category with respect to `P.isoModSerre` is abelian.

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

open Category Limits ZeroObject MorphismProperty

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- The class of monomorphisms modulo a Serre class: given a
Serre class `P : ObjectProperty C`, this is the class of morphisms `f`
such that `kernel f` satisfies `P`. -/
@[nolint unusedArguments]
def monoModSerre [P.IsSerreClass] : MorphismProperty C :=
  fun _ _ f ↦ P (kernel f)

/-- The class of epimorphisms modulo a Serre class: given a
Serre class `P : ObjectProperty C`, this is the class of morphisms `f`
such that `cokernel f` satisfies `P`. -/
@[nolint unusedArguments]
def epiModSerre [P.IsSerreClass] : MorphismProperty C :=
  fun _ _ f ↦ P (cokernel f)

/-- The class of isomorphisms modulo a Serre class: given a
Serre class `P : ObjectProperty C`, this is the class of morphisms `f`
such that `kernel f` and `cokernel f` satisfy `P`. -/
@[nolint unusedArguments]
def isoModSerre [P.IsSerreClass] : MorphismProperty C :=
  P.monoModSerre ⊓ P.epiModSerre

variable [P.IsSerreClass]

/--
@isnad1 id=iff.0h5v.s5.96579a03235c from=seed src=0 shape=0e071d06 vocab=eef50f72
-/
lemma monoModSerre_iff {X Y : C} (f : X ⟶ Y) :
    P.monoModSerre f ↔ P (kernel f) := Iff.rfl

/--
@isnad1 id=le.0h2v.s6.0a1fe32e137c from=seed src=0 shape=75e484ad vocab=28edcfe9
-/
lemma monomorphisms_le_monoModSerre : monomorphisms C ≤ P.monoModSerre :=
  fun _ _ f (_ : Mono f) ↦ P.prop_of_isZero (isZero_kernel_of_mono f)

/--
@isnad1 id=monomods.0h5v.s5.49a8540f4dd0 from=seed src=0 shape=98ee2f00 vocab=bfc332cc
-/
lemma monoModSerre_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    P.monoModSerre f :=
  P.monomorphisms_le_monoModSerre f (monomorphisms.infer_property f)

/--
@isnad1 id=iff.0h5v.s5.6741795947d2 from=seed src=0 shape=0e071d06 vocab=468a0927
-/
lemma epiModSerre_iff {X Y : C} (f : X ⟶ Y) :
    P.epiModSerre f ↔ P (cokernel f) := Iff.rfl

/--
@isnad1 id=le.0h2v.s6.3cdcaea71fce from=seed src=0 shape=75e484ad vocab=bb9dac93
-/
lemma epimorphisms_le_epiModSerre : epimorphisms C ≤ P.epiModSerre :=
  fun _ _ f (_ : Epi f) ↦ P.prop_of_isZero (isZero_cokernel_of_epi f)

/--
@isnad1 id=epimodse.0h5v.s5.b0c3737b7743 from=seed src=0 shape=98ee2f00 vocab=1e3efd26
-/
lemma epiModSerre_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
    P.epiModSerre f :=
  P.epimorphisms_le_epiModSerre f (epimorphisms.infer_property f)

/--
@isnad1 id=iff.0h4v.s6.eb615edebd96 from=seed src=0 shape=23f74aef vocab=ca161b7b
-/
@[simp]
lemma epiModSerre_zero_iff (X Y : C) :
    P.epiModSerre (0 : X ⟶ Y) ↔ P Y :=
  P.prop_iff_of_iso cokernelZeroIsoTarget

/--
@isnad1 id=iff.0h4v.s6.a6cb84108ffd from=seed src=0 shape=87b92707 vocab=ff5ab322
-/
@[simp]
lemma monoModSerre_zero_iff (X Y : C) :
    P.monoModSerre (0 : X ⟶ Y) ↔ P X :=
  P.prop_iff_of_iso kernelZeroIsoSource

/--
@isnad1 id=iff.0h5v.s6.7bd1617693d2 from=seed src=0 shape=7a1fa42f vocab=9a17bc1f
-/
lemma isoModSerre_iff {X Y : C} (f : X ⟶ Y) :
    P.isoModSerre f ↔ P.monoModSerre f ∧ P.epiModSerre f := Iff.rfl

/--
@isnad1 id=iff.0h5v.s5.3106e8dfa221 from=seed src=0 shape=6abd246b vocab=3018a7f1
-/
lemma isoModSerre_iff_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    P.isoModSerre f ↔ P.epiModSerre f := by
  have := P.monoModSerre_of_mono f
  rw [isoModSerre_iff]
  tauto

/--
@isnad1 id=iff.0h5v.s5.9d046e7fd15e from=seed src=0 shape=6abd246b vocab=c7ffe30c
-/
lemma isoModSerre_iff_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
    P.isoModSerre f ↔ P.monoModSerre f := by
  have := P.epiModSerre_of_epi f
  rw [isoModSerre_iff]
  tauto

/--
@isnad1 id=isomodse.0h6v.s5.94548a41d42e from=seed src=0 shape=04fe16e1 vocab=3018a7f1
-/
lemma isoModSerre_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (hf : P.epiModSerre f) :
    P.isoModSerre f := by
  rwa [isoModSerre_iff_of_mono]

/--
@isnad1 id=isomodse.0h6v.s5.d07ef3f891cb from=seed src=0 shape=04fe16e1 vocab=c7ffe30c
-/
lemma isoModSerre_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (hf : P.monoModSerre f) :
    P.isoModSerre f := by
  rwa [isoModSerre_iff_of_epi]

/--
@isnad1 id=iff.0h4v.s6.2b8e75adb0be from=seed src=0 shape=8725c526 vocab=413300cf
-/
@[simp]
lemma isoModSerre_zero_iff (X Y : C) :
    P.isoModSerre (0 : X ⟶ Y) ↔ P X ∧ P Y := by
  simp [isoModSerre_iff]

/--
@isnad1 id=le.0h2v.s6.6e65a1817d41 from=seed src=0 shape=75e484ad vocab=704c5ab6
-/
lemma isomorphisms_le_isoModSerre : isomorphisms C ≤ P.isoModSerre :=
  fun _ _ f (_ : IsIso f) ↦ ⟨P.monoModSerre_of_mono f, P.epiModSerre_of_epi f⟩

/--
@isnad1 id=isomodse.0h5v.s5.2d8bdf300dc7 from=seed src=0 shape=98ee2f00 vocab=8f967aed
-/
lemma isoModSerre_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : P.isoModSerre f :=
  P.isomorphisms_le_isoModSerre f (isomorphisms.infer_property f)

instance : P.monoModSerre.IsMultiplicative where
  id_mem _ := P.monoModSerre_of_mono _
  comp_mem f g hf hg :=
    P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 0) hf hg

instance : P.epiModSerre.IsMultiplicative where
  id_mem _ := P.epiModSerre_of_epi _
  comp_mem f g hf hg :=
    P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 3) hf hg

instance : P.isoModSerre.IsMultiplicative := by
  dsimp only [isoModSerre]
  infer_instance

instance : P.monoModSerre.IsStableUnderRetracts where
  of_retract {X' Y' X Y} f' f h hf :=
    P.prop_of_mono (kernel.map f' f h.left.i h.right.i (by simp)) hf

instance : P.epiModSerre.IsStableUnderRetracts where
  of_retract {X' Y' X Y} f' f h hf :=
    P.prop_of_epi (cokernel.map f f' h.left.r h.right.r (by simp)) hf

instance : P.isoModSerre.IsStableUnderRetracts := by
  dsimp only [isoModSerre]
  infer_instance

instance : P.isoModSerre.HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg :=
    ⟨P.prop_of_mono (kernel.map f (f ≫ g) (𝟙 _) g (by simp)) hfg.1,
      P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 2) hg.1 hfg.2⟩
  of_precomp f g hf hfg :=
    ⟨P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 1) hfg.1 hf.2,
      P.prop_of_epi (cokernel.map (f ≫ g) g f (𝟙 _) (by simp)) hfg.2⟩

/--
@isnad1 id=le.1h4v.s6.6539528ce7e8 from=seed src=0 shape=167c24ed vocab=b6aeb62d
-/
lemma le_kernel_of_isoModSerre_isInvertedBy (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hF : P.isoModSerre.IsInvertedBy F) :
    P ≤ F.kernel := by
  intro X hX
  let f : 0 ⟶ X := 0
  have := hF _ ((P.isoModSerre_iff_of_mono f).2
    ((P.prop_iff_of_iso cokernelZeroIsoTarget).2 hX))
  exact (asIso (F.map f)).isZero_iff.1 (F.map_isZero (isZero_zero C))

/--
@isnad1 id=iff.0h4v.s6.fabee81ed8f6 from=seed src=0 shape=2278aa1a vocab=1544df3d
-/
lemma isoModSerre_isInvertedBy_iff (F : C ⥤ D)
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    P.isoModSerre.IsInvertedBy F ↔ P ≤ F.kernel := by
  refine ⟨P.le_kernel_of_isoModSerre_isInvertedBy F, fun hF X Y f ⟨h₁, h₂⟩ ↦ ?_⟩
  have : Mono (F.map f) :=
    (((ShortComplex.mk _ _ (kernel.condition f)).exact_of_f_is_kernel
      (kernelIsKernel f)).map F).mono_g (((hF _ h₁).eq_of_src _ _))
  have : Epi (F.map f) :=
    (((ShortComplex.mk _ _ (cokernel.condition f)).exact_of_g_is_cokernel
      (cokernelIsCokernel f)).map F).epi_f (((hF _ h₂).eq_of_tgt _ _))
  exact isIso_of_mono_of_epi (F.map f)

instance : P.monoModSerre.IsStableUnderBaseChange where
  of_isPullback sq h :=
    have := isIso_kernel_map_of_isPullback sq.flip
    P.prop_of_iso (asIso (kernel.map _ _ _ _ sq.w.symm)).symm h

instance : P.epiModSerre.IsStableUnderBaseChange where
  of_isPullback sq h :=
    have := Abelian.mono_cokernel_map_of_isPullback sq.flip
    P.prop_of_mono (cokernel.map _ _ _ _ sq.w.symm) h

instance : P.isoModSerre.IsStableUnderBaseChange := by
  dsimp [isoModSerre]
  infer_instance

instance : P.monoModSerre.IsStableUnderCobaseChange where
  of_isPushout sq h :=
    have := Abelian.epi_kernel_map_of_isPushout sq.flip
    P.prop_of_epi (kernel.map _ _ _ _ sq.w.symm) h

instance : P.epiModSerre.IsStableUnderCobaseChange where
  of_isPushout sq h :=
    have := isIso_cokernel_map_of_isPushout sq.flip
    P.prop_of_iso (asIso (cokernel.map _ _ _ _ sq.w.symm)) h

instance : P.isoModSerre.IsStableUnderCobaseChange := by
  dsimp [isoModSerre]
  infer_instance

end ObjectProperty

end CategoryTheory

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import Tengoku.Seed.Algebra.Category.ModuleCat.Sheaf.Free

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Free sheaves of modules: coordinates, projections, and sections over a terminal object

Material for `Mathlib/Algebra/Category/ModuleCat/Sheaf/Free.lean`; see `README.md` on the mirror
tree. This file imports its target and nothing else, so upstreaming it adds nothing to that
file's transitive imports — but see the note on destinations below, which is a different question
from the import cost and is the one that matters here.

Mathlib's `SheafOfModules.free I` is the coproduct of `I` copies of the unit, and its API is
stated through `SheafOfModules.freeHomEquiv`: morphisms out of it are families of *global*
sections. What this development needs is the same object read **over a fixed object of the site**,
where a section of `free I` is a tuple of sections of `R`. Supplying that dictionary is most of
this file.

* `SheafOfModules.freeProj` is the `i`-th projection onto the unit, and
  `SheafOfModules.sum_freeProj_comp_ιFree` says that for a *finite* index type the projections and
  the inclusions sum to the identity — which is what makes a finite free sheaf usable as a
  biproduct in practice.
* `SheafOfModules.freeEval` reads a section over `Z` as a tuple of sections of `R` over `Z`,
  `SheafOfModules.freeEvalSymm` inverts it for finite `I`, and `SheafOfModules.freeEvalEquiv`
  packages the two as an equivalence.
* `SheafOfModules.val_app_eq_sum` evaluates a morphism out of a finite free sheaf as the sum of
  its coordinates against the images of the generators. That is the form in which a relation
  between sections is checked, and its three consumers are
  `Oka/Algebra/Category/ModuleCat/Sheaf/LocallySurjective.lean` — the only one of the three that
  imports this file directly, and the one that cites the lemma by name in
  `SheafOfModules.exists_free_app_eq_of_epi`'s own docstring —
  `Oka/Geometry/RingedSpace/LocallyRingedSpace/Coherent.lean`, which is a mirror file too, and
  `Oka/AnalyticSpace/IdealSheaf.lean`, the only analytic one. The last two reach the lemma
  transitively.

Two smaller groups sit beside it. `SheafOfModules.freePUnitIso` and
`SheafOfModules.isZero_free_of_isEmpty` are the free sheaf on one generator and on none; the first
is what lets a theorem about a morphism of free sheaves be applied to a morphism into
`SheafOfModules.unit`, which is how a quotient of the structure sheaf is presented.
`SheafOfModules.sectionOfTerminal` and its two lemmas say that on a site with a terminal object a
global section is constructed from, and determined by, its value there — which is what lets the
`Oka/AnalyticSpace/` files, whose sites have a terminal object, work with global sections at all.

**One declaration here would not go where this mirror path says, and saying so is cheaper than
moving it in a documentation change.** `PresheafOfModules.map_apply_congr` is about
`PresheafOfModules` and not about free sheaves; its destination is
`Mathlib/Algebra/Category/ModuleCat/Presheaf.lean`, where `PresheafOfModules` is defined, and not
the target of this path. It is used once, in `SheafOfModules.sectionOfTerminal`'s proof, which is
why it is here. `README.md` says that a mirror file whose declarations could not all go where its
docstring says tells a Mathlib reviewer something untrue; this paragraph is the alternative to
that, and moving the lemma is a separate change.

**All twenty-five declarations below now carry a docstring.** Fourteen did not until taxis #906,
and all fourteen were `lemma`s — which is why `lake lint` was silent about them: Batteries'
`docBlame` linter covers definitions, and `docBlameThm`, which covers theorems, is off by default
in Batteries and not turned on here. Nothing in `.orchestra/validation.sh` sees a missing lemma
docstring, so this paragraph is the only record that the gap existed; turning `docBlameThm` on
repository-wide is a separate question, and taxis #928 is where it has been costed.

## Main definitions

- `SheafOfModules.freeProj`, `SheafOfModules.freeEval`, `SheafOfModules.freeEvalEquiv`
- `SheafOfModules.sectionOfTerminal`

## Main results

- `SheafOfModules.val_app_eq_sum`
- `SheafOfModules.sum_freeProj_comp_ιFree`
-/

@[expose] public section

universe u v' u'

open CategoryTheory Limits

namespace PresheafOfModules

/-- Restriction maps of a presheaf of modules only depend on the underlying morphism. -/
lemma map_apply_congr {C : Type u'} [Category.{v'} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M : PresheafOfModules.{u} R} {X Y : Cᵒᵖ} {f g : X ⟶ Y} (h : f = g) (x : M.obj X) :
    M.map f x = M.map g x := by
  subst h
  rfl

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The free sheaf of modules on a type with a unique element is the unit. -/
noncomputable def freePUnitIso : free (R := R) PUnit.{u + 1} ≅ unit R :=
  (isColimitFreeCofan PUnit.{u + 1}).coconePointUniqueUpToIso
    (Cofan.IsColimit.mk (Cofan.mk (unit R) (fun _ ↦ 𝟙 _)) (fun s ↦ s.inj PUnit.unit)
      (fun s j ↦ by cases j; exact Category.id_comp _)
      (fun s m hm ↦ by rw [← hm PUnit.unit]; exact (Category.id_comp m).symm))

/-- The free sheaf of modules on an empty type is zero. -/
lemma isZero_free_of_isEmpty (I : Type u) [IsEmpty I] : IsZero (free (R := R) I) :=
  (IsZero.iff_id_eq_zero _).mpr <|
    (freeHomEquiv _).injective (funext fun i ↦ (IsEmpty.false i).elim)

section Evaluation

variable {M N : SheafOfModules.{u} R} {I : Type u}

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A finite sum of morphisms of sheaves of modules acts on a section as the sum of the
actions. -/
lemma val_app_sum {ι : Type*} (s : Finset ι) (φ : ι → (M ⟶ N)) (Z : Cᵒᵖ)
    (x : M.val.obj Z) :
    (∑ i ∈ s, φ i).val.app Z x = ∑ i ∈ s, (φ i).val.app Z x := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]; rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The morphism `unit R ⟶ M` corresponding to a section `s` multiplies by `s`: it sends a section
`r` of the sheaf of rings to `r • s`. -/
lemma unitHomEquiv_symm_val_app (s : M.sections) (Z : Cᵒᵖ) (r : R.obj.obj Z) :
    (M.unitHomEquiv.symm s).val.app Z r = r • PresheafOfModules.sections.eval s Z :=
  rfl

variable (R) in
/-- The `i`-th projection of a free sheaf of modules onto the unit. -/
noncomputable def freeProj [DecidableEq I] (i : I) : free (R := R) I ⟶ unit R :=
  Cofan.IsColimit.desc (isColimitFreeCofan I) (fun j ↦ if j = i then 𝟙 (unit R) else 0)

/-- The inclusions and the projections of a free sheaf of modules are dual to each other:
`ιFree i ≫ freeProj R j` is the identity when `i = j` and zero otherwise. -/
@[reassoc (attr := simp)]
lemma ιFree_comp_freeProj [DecidableEq I] (i j : I) :
    ιFree i ≫ freeProj R j = if i = j then 𝟙 (unit R) else 0 :=
  Cofan.IsColimit.fac (isColimitFreeCofan I) _ i

/-- The other half of the dual-basis relation, and the half that needs `I` finite: the
projections followed by the inclusions sum to the identity. This is what makes a finite free
sheaf usable as a biproduct. -/
lemma sum_freeProj_comp_ιFree [Fintype I] [DecidableEq I] :
    ∑ i : I, freeProj R i ≫ ιFree (R := R) i = 𝟙 (free I) := by
  refine Cofan.IsColimit.hom_ext (isColimitFreeCofan I) _ _ (fun j ↦ ?_)
  change ιFree j ≫ _ = ιFree j ≫ _
  rw [Preadditive.comp_sum, Category.comp_id, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [← Category.assoc, ιFree_comp_freeProj, ite_eq_right (Ne.symm hij), Limits.zero_comp]
  · simp

variable [DecidableEq I] (Z : Cᵒᵖ)

/-- The coordinates of a section of a finite free sheaf of modules. -/
noncomputable def freeEval :
    (free (R := R) I).val.obj Z →ₗ[R.obj.obj Z] (I → R.obj.obj Z) :=
  LinearMap.pi fun i ↦ ((freeProj R i).val.app Z).hom

/-- The `i`-th coordinate of a section is its image under the `i`-th projection. -/
@[simp]
lemma freeEval_apply (b : (free (R := R) I).val.obj Z) (i : I) :
    freeEval Z b i = (freeProj R i).val.app Z b :=
  rfl

variable [Fintype I]

/-- A tuple of sections of `R` over `Z` defines a section of the finite free sheaf of modules. -/
noncomputable def freeEvalSymm :
    (I → R.obj.obj Z) →ₗ[R.obj.obj Z] (free (R := R) I).val.obj Z :=
  ∑ i : I, ((ιFree (R := R) i).val.app Z).hom ∘ₗ LinearMap.proj i

omit [DecidableEq I] in
/-- The section built from a tuple is the sum of its entries along the inclusions. -/
lemma freeEvalSymm_apply (a : I → R.obj.obj Z) :
    freeEvalSymm (R := R) (I := I) Z a = ∑ i : I, (ιFree i).val.app Z (a i) := by
  rw [freeEvalSymm, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ ↦ rfl

/-- Reading off the coordinates of the section built from a tuple returns that tuple. -/
@[simp]
lemma freeEval_freeEvalSymm (a : I → R.obj.obj Z) :
    freeEval Z (freeEvalSymm (R := R) (I := I) Z a) = a := by
  ext j
  rw [freeEval_apply, freeEvalSymm_apply, map_sum, Finset.sum_eq_single j]
  · change (ιFree j ≫ freeProj R j).val.app Z (a j) = a j
    rw [ιFree_comp_freeProj, ite_eq_left rfl]
    rfl
  · intro i _ hij
    change (ιFree i ≫ freeProj R j).val.app Z (a i) = 0
    rw [ιFree_comp_freeProj, ite_eq_right hij]
    rfl
  · simp

/-- Rebuilding a section from its own coordinates returns that section. -/
@[simp]
lemma freeEvalSymm_freeEval (b : (free (R := R) I).val.obj Z) :
    freeEvalSymm Z (freeEval (R := R) (I := I) Z b) = b := by
  rw [freeEvalSymm_apply]
  have : ∀ i : I, (ιFree (R := R) i).val.app Z (freeEval Z b i) =
      (freeProj R i ≫ ιFree i).val.app Z b := fun i ↦ rfl
  simp_rw [this]
  rw [← val_app_sum, sum_freeProj_comp_ιFree]
  rfl

/-- Sections of a finite free sheaf of modules over an object are tuples of sections
of the sheaf of rings. -/
noncomputable def freeEvalEquiv :
    (free (R := R) I).val.obj Z ≃ₗ[R.obj.obj Z] (I → R.obj.obj Z) :=
  LinearEquiv.ofLinearMap (freeEval Z) (freeEvalSymm Z)
    (LinearMap.ext fun a ↦ freeEval_freeEvalSymm Z a)
    (LinearMap.ext fun b ↦ freeEvalSymm_freeEval Z b)

/-- The equivalence is `SheafOfModules.freeEval` in the forward direction. -/
@[simp]
lemma freeEvalEquiv_apply (b : (free (R := R) I).val.obj Z) :
    freeEvalEquiv Z b = freeEval Z b :=
  rfl

/-- The equivalence is `SheafOfModules.freeEvalSymm` in the backward direction. -/
@[simp]
lemma freeEvalEquiv_symm_apply (a : I → R.obj.obj Z) :
    (freeEvalEquiv (R := R) (I := I) Z).symm a = freeEvalSymm Z a :=
  rfl

omit [Fintype I] in
/-- A section of a free sheaf of modules on a finite index type is determined by its
coordinates. Stated at `Finite I` rather than `Fintype I`, which is what a consumer usually has;
the proof supplies the `Fintype` and reads the injectivity off
`SheafOfModules.freeEvalEquiv`. -/
lemma freeEval_injective [Finite I] : Function.Injective (freeEval (R := R) (I := I) Z) := by
  haveI := Fintype.ofFinite I
  exact (freeEvalEquiv Z).injective

omit [Fintype I] in
/-- Taking coordinates commutes with restriction. -/
lemma freeEval_naturality {Z W : Cᵒᵖ} (f : Z ⟶ W) (b : (free (R := R) I).val.obj Z) (i : I) :
    freeEval W ((free (R := R) I).val.map f b) i = R.obj.map f (freeEval Z b i) :=
  PresheafOfModules.naturality_apply (freeProj R i).val f b

omit [DecidableEq I] in
/-- The same in the other direction: restricting the section built from a tuple is building it
from the restricted tuple. -/
lemma map_freeEvalSymm {Z W : Cᵒᵖ} (f : Z ⟶ W) (a : I → R.obj.obj Z) :
    (free (R := R) I).val.map f (freeEvalSymm Z a) =
      freeEvalSymm W (fun i ↦ R.obj.map f (a i)) := by
  classical
  refine freeEval_injective W (funext fun i ↦ ?_)
  rw [freeEval_naturality, freeEval_freeEvalSymm, freeEval_freeEvalSymm]

/-- The action of a morphism out of a finite free sheaf of modules on sections, in terms of
the corresponding family of sections. -/
lemma val_app_eq_sum (φ : free (R := R) I ⟶ M) (b : (free (R := R) I).val.obj Z) :
    φ.val.app Z b =
      ∑ i : I, freeEval Z b i • PresheafOfModules.sections.eval (M.freeHomEquiv φ i) Z := by
  conv_lhs => rw [← freeEvalSymm_freeEval Z b, freeEvalSymm_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  change (ιFree i ≫ φ).val.app Z (freeEval Z b i) = _
  rw [← unitHomEquiv_symm_freeHomEquiv_apply φ i, unitHomEquiv_symm_val_app]

end Evaluation

section Sections

variable {T : C} (hT : IsTerminal T) (M : SheafOfModules.{u} R)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A section of a sheaf of modules on a site with terminal object `T` is the same thing as
an element over `T`. -/
noncomputable def sectionOfTerminal (b : M.val.obj (Opposite.op T)) : M.sections :=
  PresheafOfModules.sectionsMk (fun Z ↦ M.val.map (hT.from Z.unop).op b) (fun {Z W} f ↦ by
    rw [← PresheafOfModules.map_comp_apply]
    exact PresheafOfModules.map_apply_congr (Quiver.Hom.unop_inj (hT.hom_ext _ _)) b)

/-- The section built from an element over the terminal object restricts it along the unique
morphism into `T`. -/
@[simp]
lemma sectionOfTerminal_val (b : M.val.obj (Opposite.op T)) (Z : Cᵒᵖ) :
    PresheafOfModules.sections.eval (sectionOfTerminal hT M b) Z =
      M.val.map (hT.from Z.unop).op b :=
  rfl

/-- A section is determined by its value over the terminal object: the two directions of
`SheafOfModules.sectionOfTerminal` are mutually inverse. -/
@[simp]
lemma sectionOfTerminal_eval (s : M.sections) :
    sectionOfTerminal hT M (PresheafOfModules.sections.eval s (Opposite.op T)) = s := by
  ext Z
  exact PresheafOfModules.sections_property s (hT.from Z.unop).op

variable {M} in
/-- Pushing a section forward along a morphism is pushing its value over the terminal object
forward. -/
lemma sectionsMap_sectionOfTerminal {N : SheafOfModules.{u} R} (p : M ⟶ N)
    (b : M.val.obj (Opposite.op T)) :
    sectionsMap p (sectionOfTerminal hT M b) =
      sectionOfTerminal hT N (p.val.app (Opposite.op T) b) := by
  ext Z
  exact PresheafOfModules.naturality_apply p.val (hT.from Z.unop).op b

end Sections

end SheafOfModules

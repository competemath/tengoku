import Tengoku.MagnitudeConjecture.MagnitudeConjecture.CategoryTheory.ShiftOrbitObjectIso
import Tengoku.Seed.Algebra.Category.ModuleCat.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Direct-sum push-down to a shift-orbit category

For a linear module `M : C ⥤ ModuleCat k`, its push-down to the
shift-orbit category has value `⨁ b, M(X⟦b⟧)` at `X`. A homogeneous
map of degree `a` sends the `b`-summand to the `(a + b)`-summand.

This file constructs that action, verifies its unit and composition laws
from Mathlib's shift coherence, and packages it as an additive linear
module over the orbit category. The construction is generic; covering-specific
finite-support hypotheses enter only when restricting its values to
finite-dimensional modules.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK uM

variable {k : Type uK} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]

variable (M : C ⥤ ModuleCat.{uM} k) [M.Additive] [M.Linear k]

/-- The value of the push-down module at an object of the orbit category.-/
abbrev orbitPushdownValue (X : C) :=
  DirectSum A (fun b ↦ M.obj ((shiftFunctor C b).obj X))

/-- Inclusion of one translated value into the push-down direct sum.-/
noncomputable def orbitPushdownLof (X : C) (b : A) :
    M.obj ((shiftFunctor C b).obj X) →ₗ[k]
      orbitPushdownValue (A := A) M X := by
  classical
  exact DirectSum.lof k A
    (fun c ↦ M.obj ((shiftFunctor C c).obj X)) b

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] in
/-- The push-down summand inclusion is the standard direct-sum generator.
@isnad1 id=eq.0h7v.s11.f1e779779b96 from=translated src=- shape=47416591 vocab=e050d8b4
-/
theorem orbitPushdownLof_eq_directSumOf [DecidableEq A]
    (X : C) (b : A) (x : M.obj ((shiftFunctor C b).obj X)) :
    orbitPushdownLof M X b x =
      DirectSum.of
        (fun c : A ↦ M.obj ((shiftFunctor C c).obj X)) b x := by
  unfold orbitPushdownLof
  rw [DirectSum.lof_eq_of]
  have h : (fun c d : A ↦ Classical.propDecidable (c = d)) =
      (inferInstance : DecidableEq A) :=
    Subsingleton.elim _ _
  rw [h]

/-- The map from the `b`-summand induced by a homogeneous orbit morphism of
degree `a`, with an explicitly chosen output degree.-/
def orbitPushdownArrow'
    {X Y : C} {a b c : A} (h : a + b = c) (f : ShiftHom X Y a) :
    (shiftFunctor C b).obj X ⟶ (shiftFunctor C c).obj Y :=
  (shiftFunctor C b).map f ≫
    (shiftFunctorAdd' C a b c h).inv.app Y

/-- Applying the upstairs module to the component arrow.-/
def orbitPushdownComponent'
    {X Y : C} {a b c : A} (h : a + b = c) (f : ShiftHom X Y a) :
    M.obj ((shiftFunctor C b).obj X) →ₗ[k]
      M.obj ((shiftFunctor C c).obj Y) :=
  (M.map (orbitPushdownArrow' h f)).hom

/-- The component map with its canonical output degree.-/
def orbitPushdownComponent
    {X Y : C} (a b : A) (f : ShiftHom X Y a) :
    M.obj ((shiftFunctor C b).obj X) →ₗ[k]
      M.obj ((shiftFunctor C (a + b)).obj Y) :=
  orbitPushdownComponent' M rfl f

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] in
/-- The canonical component map agrees heterogeneously with the component
map at any propositionally equal output degree.
@isnad1 id=heq.1h11v.s10.fc634b9abaa6 from=translated src=- shape=36221a7e vocab=cc6bbc4b
-/
theorem orbitPushdownComponent_apply_heq_component'_apply
    {X Y : C} {a b c : A} (h : a + b = c)
    (f : ShiftHom X Y a)
    (x : M.obj ((shiftFunctor C b).obj X)) :
    HEq (orbitPushdownComponent M a b f x)
      (orbitPushdownComponent' M h f x) := by
  subst c
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] in
/--
@isnad1 id=eq.0h6v.s9.f156afb96c4a from=translated src=- shape=2b86736b vocab=533eb3c5
-/
@[simp]
theorem orbitPushdownComponent'_id
    (X : C) (b : A) :
    orbitPushdownComponent' M (zero_add b)
        (shiftHomId (A := A) X) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp only [orbitPushdownComponent', orbitPushdownArrow', shiftHomId,
    shiftFunctorAdd'_zero_add_inv_app]
  rw [← Functor.map_comp]
  simp

set_option backward.isDefEq.respectTransparency false in
omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive] in
/-- Component arrows respect homogeneous composition, including all degree
reassociations.
@isnad1 id=eq.4h13v.s8.fa9b3351ec77 from=translated src=- shape=3a0a11f7 vocab=b56c4ab0
-/
theorem orbitPushdownArrow'_comp
    {X Y Z : C} {a c b ab ca d : A}
    (hab : a + b = ab) (hca : c + a = ca)
    (hleft : ca + b = d) (hright : c + ab = d)
    (f : ShiftHom X Y a) (g : ShiftHom Y Z c) :
    orbitPushdownArrow' hleft (shiftHomComp' hca f g) =
      orbitPushdownArrow' hab f ≫ orbitPushdownArrow' hright g := by
  have htotal : c + a + b = d := by rw [hca, hleft]
  simp only [orbitPushdownArrow', shiftHomComp', Functor.map_comp,
    Category.assoc]
  rw [shiftFunctorAdd'_assoc_inv_app c a b ca ab d hca hab htotal]
  have hn := (shiftFunctorAdd' C a b ab hab).inv.naturality_assoc g
    ((shiftFunctorAdd' C c ab d hright).inv.app Z)
  simp only [Functor.comp_map] at hn
  rw [hn]

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] in
/-- Applying the module turns composition of component arrows into
composition of component linear maps.
@isnad1 id=eq.4h15v.s10.ae01bc0d53f0 from=translated src=- shape=99f3b0b6 vocab=0f3d1d01
-/
theorem orbitPushdownComponent'_comp
    {X Y Z : C} {a c b ab ca d : A}
    (hab : a + b = ab) (hca : c + a = ca)
    (hleft : ca + b = d) (hright : c + ab = d)
    (f : ShiftHom X Y a) (g : ShiftHom Y Z c) :
    orbitPushdownComponent' M hleft (shiftHomComp' hca f g) =
      (orbitPushdownComponent' M hright g).comp
        (orbitPushdownComponent' M hab f) := by
  apply LinearMap.ext
  intro x
  simp only [orbitPushdownComponent', LinearMap.comp_apply]
  rw [orbitPushdownArrow'_comp hab hca hleft hright f g,
    M.map_comp, ModuleCat.comp_apply]

/-- A homogeneous orbit morphism acts on the direct sum by translating the
summand index on the left by its degree.-/
def orbitPushdownHomogeneousMap
    {X Y : C} (a : A) (f : ShiftHom X Y a) :
    orbitPushdownValue (A := A) M X →ₗ[k]
      orbitPushdownValue (A := A) M Y := by
  classical
  exact DirectSum.toModule k A _ fun b ↦
    (orbitPushdownLof M Y (a + b)).comp
      (orbitPushdownComponent M a b f)

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] in
/--
@isnad1 id=eq.0h10v.s12.51c30814e191 from=translated src=- shape=25a76f75 vocab=2e5b3f20
-/
@[simp]
theorem orbitPushdownHomogeneousMap_lof
    {X Y : C} (a b : A) (f : ShiftHom X Y a)
    (x : M.obj ((shiftFunctor C b).obj X)) :
    orbitPushdownHomogeneousMap M a f
        (orbitPushdownLof M X b x) =
      orbitPushdownLof M Y (a + b)
        (orbitPushdownComponent M a b f x) := by
  classical
  simp [orbitPushdownHomogeneousMap, orbitPushdownLof]

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] in
/-- Homogeneous push-down maps respect homogeneous composition.
@isnad1 id=eq.0h11v.s10.0bcd615b45d5 from=translated src=- shape=0d051639 vocab=a855ee6b
-/
theorem orbitPushdownHomogeneousMap_comp
    {X Y Z : C} {a c : A}
    (f : ShiftHom X Y a) (g : ShiftHom Y Z c) :
    orbitPushdownHomogeneousMap M (c + a) (shiftHomComp f g) =
      (orbitPushdownHomogeneousMap M c g).comp
        (orbitPushdownHomogeneousMap M a f) := by
  classical
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  change orbitPushdownHomogeneousMap M (c + a) (shiftHomComp f g)
      (orbitPushdownLof M X b x) =
    orbitPushdownHomogeneousMap M c g
      (orbitPushdownHomogeneousMap M a f
        (orbitPushdownLof M X b x))
  rw [orbitPushdownHomogeneousMap_lof,
    orbitPushdownHomogeneousMap_lof,
    orbitPushdownHomogeneousMap_lof]
  change DirectSum.of
      (fun e ↦ M.obj ((shiftFunctor C e).obj Z)) ((c + a) + b)
        (orbitPushdownComponent M (c + a) b (shiftHomComp f g) x) =
    DirectSum.of (fun e ↦ M.obj ((shiftFunctor C e).obj Z))
      (c + (a + b))
      (orbitPushdownComponent M c (a + b) g
        (orbitPushdownComponent M a b f x))
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (add_assoc c a b)
  exact
    (orbitPushdownComponent_apply_heq_component'_apply M
      (add_assoc c a b) (shiftHomComp f g) x).trans
      (heq_of_eq (DFunLike.congr_fun
        (orbitPushdownComponent'_comp M rfl rfl
          (add_assoc c a b) rfl f g) x))

/-- The action of degree-`a` homogeneous morphisms is linear in the
morphism.-/
def orbitPushdownHomogeneousLinearMap
    {X Y : C} (a : A) :
    ShiftHom X Y a →ₗ[k]
      (orbitPushdownValue (A := A) M X →ₗ[k]
        orbitPushdownValue (A := A) M Y) where
  toFun := orbitPushdownHomogeneousMap M a
  map_add' f g := by
    classical
    apply DirectSum.linearMap_ext
    intro b
    apply LinearMap.ext
    intro x
    simp [orbitPushdownHomogeneousMap, orbitPushdownLof,
      orbitPushdownComponent, orbitPushdownComponent', Functor.map_add,
      orbitPushdownArrow', Preadditive.add_comp]
  map_smul' r f := by
    classical
    apply DirectSum.linearMap_ext
    intro b
    apply LinearMap.ext
    intro x
    simp [orbitPushdownHomogeneousMap, orbitPushdownLof,
      orbitPushdownComponent, orbitPushdownComponent', Functor.map_smul,
      orbitPushdownArrow', CategoryTheory.Linear.smul_comp]

/-- The linear action of all finite-support orbit morphisms.-/
def orbitPushdownMapLinear
    {X Y : C} :
    ShiftOrbitHom A X Y →ₗ[k]
      (orbitPushdownValue (A := A) M X →ₗ[k]
        orbitPushdownValue (A := A) M Y) := by
  classical
  exact DirectSum.toModule k A _ fun a ↦
    orbitPushdownHomogeneousLinearMap M a

/--
@isnad1 id=eq.0h8v.s12.80510b401a6e from=translated src=- shape=0fe1a1ba vocab=3a61f59d
-/
@[simp]
theorem orbitPushdownMapLinear_of
    {X Y : C} (a : A) (f : ShiftHom X Y a) :
    orbitPushdownMapLinear M (shiftOrbitOf X Y a f) =
      orbitPushdownHomogeneousMap M a f := by
  classical
  change orbitPushdownMapLinear M
      (DirectSum.lof k A (fun c ↦ ShiftHom X Y c) a f) = _
  simp [orbitPushdownMapLinear]
  rfl

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [M.Additive] [M.Linear k] in
/--
@isnad1 id=eq.0h5v.s9.4d05b13e20dd from=translated src=- shape=b85a97c3 vocab=8f75ed98
-/
@[simp]
theorem orbitPushdownHomogeneousMap_id (X : C) :
    orbitPushdownHomogeneousMap M (0 : A) (shiftHomId (A := A) X) =
      LinearMap.id := by
  classical
  apply DirectSum.linearMap_ext
  intro b
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  change orbitPushdownHomogeneousMap M (0 : A)
      (shiftHomId (A := A) X) (orbitPushdownLof M X b x) =
    orbitPushdownLof M X b x
  rw [orbitPushdownHomogeneousMap_lof]
  change DirectSum.of
      (fun c ↦ M.obj ((shiftFunctor C c).obj X)) (0 + b)
        (orbitPushdownComponent M 0 b (shiftHomId (A := A) X) x) =
    DirectSum.of (fun c ↦ M.obj ((shiftFunctor C c).obj X)) b x
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (zero_add b)
  exact
    (orbitPushdownComponent_apply_heq_component'_apply M
      (zero_add b) (shiftHomId (A := A) X) x).trans
      (heq_of_eq (DFunLike.congr_fun
        (orbitPushdownComponent'_id M X b) x))

end MagnitudeConjecture.CoveringHom

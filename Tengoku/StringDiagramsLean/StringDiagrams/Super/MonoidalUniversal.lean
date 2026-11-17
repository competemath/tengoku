import Tengoku.StringDiagramsLean.StringDiagrams.Super.MonoidalPi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The universal property of the monoidal Π-envelope

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Theorem 1.15 (first half): the functor `-_π : SMon → Π-SMon` of (1.9) is left 2-adjoint to the
forgetful functor. The paper deduces it from Theorem 4.9 by specializing to 2-supercategories
with one object; here it is proved directly for monoidal supercategories, following the proof
of Lemma 4.7.

Let `A` be a monoidal supercategory and `B` a monoidal Π-supercategory, viewed as a
Π-supercategory with `Π = π ⊗ -` (`MonoidalPiSupercategory.toPiSupercategory`).

* A monoidal superfunctor `F : A → B` extends to a monoidal superfunctor `F̃ : A_π → B`
  (`Envelope.extendMonoidal`) with `F̃ J = F` as monoidal superfunctors (`J_comp_extend` on the
  underlying superfunctors and `Envelope.extendMonoidal_μIso_J`,
  `Envelope.extendMonoidal_εIso` on the coherence maps). The underlying superfunctor is
  `Envelope.extend`
  (Lemma 4.2(i)); the coherence map is
  `c̃_{Πᵃλ, Πᵇμ} = (ζᵃ_{Fλ} ⊗ ζᵇ_{Fμ}) ≫ c_{λ,μ} ≫ (ζ^{a+b}_{F(λ⊗μ)})⁻¹` (`extendμ`), where
  `⊗` is Mathlib's `tensorHom` (`f ▷ _ ≫ _ ◁ g`), and `ĩ = i`.
* A monoidal natural transformation `x : F ⇒ G` extends uniquely to a monoidal natural
  transformation `x̃ : F̃ ⇒ G̃` restricting to `x` (`Envelope.extendMonoidalNatTrans`,
  `Envelope.extendMonoidalNatTrans_unique`), given by (4.2) with `|x| = 0`.
* Restriction along `J` is a bijection from monoidal natural transformations `F̃ ⇒ G̃` to
  monoidal natural transformations `F ⇒ G` (`Envelope.restrictMonoidal_bijective`), and the
  extension respects identities and composition.
* Every monoidal superfunctor `H : A_π → B` (with restriction `H J`,
  `Envelope.restrictMonoidal`) is isomorphic, by mutually inverse even monoidal natural
  transformations, to the extension of its restriction (`Envelope.extendRestrictMonoidalHom`,
  `Envelope.extendRestrictMonoidalInv`, `Envelope.extendRestrictMonoidal_hom_inv`).

Together these say that `F ↦ F̃`, `x ↦ x̃` is an equivalence from the category of monoidal
superfunctors `A → νB` and monoidal natural transformations to that of monoidal superfunctors
`A_π → B`, which is the monoidal case of Theorem 4.9 (Theorem 1.15, first half).

The proofs do not use the monoidal Π-structure of `B` beyond the Π-supercategory structure,
so the statements are made for any monoidal supercategory `B` with a Π-supercategory
structure. The coherence axioms for `F̃`, `x̃` and the isomorphism are proved by the argument
behind the uniqueness in Lemma 4.2(ii): both sides are natural in each variable with respect
to the isomorphisms `(1_λ)_0^a : Π⁰λ ≅ Πᵃλ`, so they agree once they agree on objects `Π⁰λ`,
where they reduce to the axioms for `F`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory

universe w w₁ w₂ w₃ w₄

namespace Envelope

/-- Two morphisms that are conjugate, by the same isomorphisms, to equal morphisms are
equal.-/
theorem eq_of_conj {D : Type*} [Category D] {X X' Y Y' : D} (e : X ≅ X') (g : Y ≅ Y')
    {φ ψ : X' ⟶ Y'} {φ₀ ψ₀ : X ⟶ Y} (hφ : e.hom ≫ φ = φ₀ ≫ g.hom)
    (hψ : e.hom ≫ ψ = ψ₀ ≫ g.hom) (h : φ₀ = ψ₀) : φ = ψ := by
  rw [← cancel_epi e.hom, hφ, hψ, h]

variable {R : Type w} [CommRing R]
  {A : Type w₁} [Category.{w₂} A] [Preadditive A] [Linear R A] [Supercategory R A]
  [MonoidalCategoryStruct A] [MonoidalSupercategory R A]
  {B : Type w₃} [Category.{w₄} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [MonoidalCategoryStruct B] [MonoidalSupercategory R B]

section Helpers

variable (R) in
include R in
@[reassoc]
theorem inv_hom_whiskerRight' {X Y : B} (e : X ≅ Y) (Z : B) :
    e.inv ▷ Z ≫ e.hom ▷ Z = 𝟙 (Y ⊗ Z) := by
  rw [← MonoidalSupercategory.comp_whiskerRight (R := R), e.inv_hom_id,
    MonoidalSupercategory.id_whiskerRight (R := R)]

variable (R) in
include R in
@[reassoc]
theorem hom_inv_whiskerRight' {X Y : B} (e : X ≅ Y) (Z : B) :
    e.hom ▷ Z ≫ e.inv ▷ Z = 𝟙 (X ⊗ Z) := by
  rw [← MonoidalSupercategory.comp_whiskerRight (R := R), e.hom_inv_id,
    MonoidalSupercategory.id_whiskerRight (R := R)]

variable (R) in
include R in
@[reassoc]
theorem whiskerLeft_inv_hom' (Z : B) {X Y : B} (e : X ≅ Y) :
    Z ◁ e.inv ≫ Z ◁ e.hom = 𝟙 (Z ⊗ Y) := by
  rw [← MonoidalSupercategory.whiskerLeft_comp (R := R), e.inv_hom_id,
    MonoidalSupercategory.whiskerLeft_id (R := R)]

variable (R) in
include R in
@[reassoc]
theorem whiskerLeft_hom_inv' (Z : B) {X Y : B} (e : X ≅ Y) :
    Z ◁ e.hom ≫ Z ◁ e.inv = 𝟙 (Z ⊗ X) := by
  rw [← MonoidalSupercategory.whiskerLeft_comp (R := R), e.hom_inv_id,
    MonoidalSupercategory.whiskerLeft_id (R := R)]

variable (R) in
include R in
/-- The interchange law without sign when the left morphism is even and the right one is
arbitrary.-/
theorem interchange_even_left' {X X' Y Y' : B} {f : X ⟶ X'} (hf : f ∈ parity (R := R) X X' 0)
    (g : Y ⟶ Y') : f ▷ Y ≫ X' ◁ g = X ◁ g ≫ f ▷ Y' := by
  refine Supercategory.induction_on (R := R) g ?_ (fun q g hg => ?_) (fun g h hg hh => ?_)
  · rw [MonoidalSupercategory.whiskerLeft_zero R, MonoidalSupercategory.whiskerLeft_zero R,
      Limits.comp_zero, Limits.zero_comp]
  · exact MonoidalSupercategory.interchange_of_even_left hf hg
  · rw [MonoidalSupercategory.whiskerLeft_add (R := R), MonoidalSupercategory.whiskerLeft_add
      (R := R), Preadditive.comp_add, Preadditive.add_comp, hg, hh]

variable (R) in
include R in
/-- The interchange law without sign when the right morphism is even and the left one is
arbitrary.-/
theorem interchange_even_right' {X X' Y Y' : B} (f : X ⟶ X') {g : Y ⟶ Y'}
    (hg : g ∈ parity (R := R) Y Y' 0) : f ▷ Y ≫ X' ◁ g = X ◁ g ≫ f ▷ Y' := by
  refine Supercategory.induction_on (R := R) f ?_ (fun q f hf => ?_) (fun f h hf hh => ?_)
  · rw [MonoidalSupercategory.zero_whiskerRight R, MonoidalSupercategory.zero_whiskerRight R,
      Limits.comp_zero, Limits.zero_comp]
  · exact MonoidalSupercategory.interchange_of_even_right hf hg
  · rw [MonoidalSupercategory.add_whiskerRight (R := R), MonoidalSupercategory.add_whiskerRight
      (R := R), Preadditive.comp_add, Preadditive.add_comp, hf, hh]

variable (R) in
include R in
theorem whiskerLeft_comp_comp (X : B) {Y Z W V : B} (f : Y ⟶ Z) (g : Z ⟶ W) (h : X ⊗ W ⟶ V) :
    X ◁ f ≫ X ◁ g ≫ h = X ◁ (f ≫ g) ≫ h := by
  rw [MonoidalSupercategory.whiskerLeft_comp (R := R), Category.assoc]

variable (R) in
/-- Right whiskering of an isomorphism.-/
@[simps]
def wRIso {X Y : B} (e : X ≅ Y) (Z : B) : X ⊗ Z ≅ Y ⊗ Z where
  hom := e.hom ▷ Z
  inv := e.inv ▷ Z
  hom_inv_id := hom_inv_whiskerRight' R e Z
  inv_hom_id := inv_hom_whiskerRight' R e Z

variable (R) in
/-- Left whiskering of an isomorphism.-/
@[simps]
def wLIso (Z : B) {X Y : B} (e : X ≅ Y) : Z ⊗ X ≅ Z ⊗ Y where
  hom := Z ◁ e.hom
  inv := Z ◁ e.inv
  hom_inv_id := whiskerLeft_hom_inv' R Z e
  inv_hom_id := whiskerLeft_inv_hom' R Z e

end Helpers

variable [PiSupercategory R B]

variable {F : A ⥤ B} [F.Additive] [F.Linear R] [IsSuperfunctor R F]
  (cF : MonoidalSuperfunctor R F)

local notation "F̃" => extend R F

/-- The coherence map `c̃_{X,Y} : F̃ X ⊗ F̃ Y ⟶ F̃ (X ⊗ Y)` of the extension:
`(ζᵃ ⊗ ζᵇ) ≫ c ≫ (ζ^{a+b})⁻¹`.-/
def extendμ (X Y : Envelope R A) : (F̃).obj X ⊗ (F̃).obj Y ⟶ (F̃).obj (X ⊗ Y) :=
  (ζPow R X.par (F.obj X.obj)).hom ▷ (F̃).obj Y ≫ F.obj X.obj ◁ (ζPow R Y.par (F.obj Y.obj)).hom ≫
    (cF.μIso X.obj Y.obj).hom ≫ (ζPow R (X.par + Y.par) (F.obj (X.obj ⊗ Y.obj))).inv

/-- The inverse of `extendμ`.-/
def extendμInv (X Y : Envelope R A) : (F̃).obj (X ⊗ Y) ⟶ (F̃).obj X ⊗ (F̃).obj Y :=
  (ζPow R (X.par + Y.par) (F.obj (X.obj ⊗ Y.obj))).hom ≫ (cF.μIso X.obj Y.obj).inv ≫
    F.obj X.obj ◁ (ζPow R Y.par (F.obj Y.obj)).inv ≫
      (ζPow R X.par (F.obj X.obj)).inv ▷ (F̃).obj Y

set_option backward.isDefEq.respectTransparency false in
omit [MonoidalSupercategory R A] in
theorem extendμ_extendμInv (X Y : Envelope R A) : extendμ cF X Y ≫ extendμInv cF X Y = 𝟙 _ := by
  simp only [extendμ, extendμInv, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    whiskerLeft_hom_inv'_assoc R, hom_inv_whiskerRight' R]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [MonoidalSupercategory R A] in
theorem extendμInv_extendμ (X Y : Envelope R A) : extendμInv cF X Y ≫ extendμ cF X Y = 𝟙 _ := by
  simp only [extendμ, extendμInv, Category.assoc, inv_hom_whiskerRight'_assoc R,
    whiskerLeft_inv_hom'_assoc R, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id]

/-- The coherence isomorphism `c̃`.-/
@[simps]
def extendμIso (X Y : Envelope R A) : (F̃).obj X ⊗ (F̃).obj Y ≅ (F̃).obj (X ⊗ Y) where
  hom := extendμ cF X Y
  inv := extendμInv cF X Y
  hom_inv_id := extendμ_extendμInv cF X Y
  inv_hom_id := extendμInv_extendμ cF X Y

omit [MonoidalSupercategory R A] in
theorem extendμ_mem (X Y : Envelope R A) :
    extendμ cF X Y ∈ parity (R := R) _ _ 0 := by
  have h1 := MonoidalSupercategory.whiskerRight_mem ((F̃).obj Y)
    (ζPow_hom_mem (R := R) X.par (F.obj X.obj))
  have h2 := MonoidalSupercategory.whiskerLeft_mem (F.obj X.obj)
    (ζPow_hom_mem (R := R) Y.par (F.obj Y.obj))
  have h3 := cF.μ_mem X.obj Y.obj
  have h4 := ζPow_inv_mem (R := R) (X.par + Y.par) (F.obj (X.obj ⊗ Y.obj))
  have := comp_mem h1 (comp_mem h2 (comp_mem h3 h4))
  have e : X.par + (Y.par + (0 + (X.par + Y.par))) = 0 := by
    generalize X.par = a; generalize Y.par = b; revert a b; decide
  rw [e] at this
  exact this

set_option backward.isDefEq.respectTransparency false in
theorem extendμ_naturality_left {X X' : Envelope R A} (u : X ⟶ X') (Y : Envelope R A) :
    (F̃).map u ▷ (F̃).obj Y ≫ extendμ cF X' Y = extendμ cF X Y ≫ (F̃).map (u ▷ Y) := by
  refine induction_on' (R := R) u ?_ (fun r u hu => ?_) (fun u v hu hv => ?_)
  · rw [Functor.map_zero, MonoidalSupercategory.zero_whiskerRight R, zero_whiskerRight',
      Functor.map_zero, Limits.zero_comp, Limits.comp_zero]
  · have hi := MonoidalSupercategory.super_interchange (map_mem F hu)
      (ζPow_hom_mem (R := R) Y.par (F.obj Y.obj))
    simp only [extend_map, extendμ, tensorObj_obj, tensorObj_par]
    rw [toHom_whiskerRight_of_mem hu Y, Functor.map_smul]
    simp only [MonoidalSupercategory.comp_whiskerRight (R := R), Category.assoc,
      inv_hom_whiskerRight'_assoc R, Iso.inv_hom_id_assoc, Linear.smul_comp, Linear.comp_smul]
    erw [reassoc_of% hi]
    rw [Linear.smul_comp, Linear.comp_smul, Category.assoc,
      reassoc_of% (cF.μ_natural_left _ _),
      koszulSign_smul (R := R), mul_comm]
  · rw [Functor.map_add, MonoidalSupercategory.add_whiskerRight (R := R), add_whiskerRight',
      Functor.map_add, Preadditive.add_comp, Preadditive.comp_add, hu, hv]

set_option backward.isDefEq.respectTransparency false in
theorem extendμ_naturality_right (X : Envelope R A) {Y Y' : Envelope R A} (v : Y ⟶ Y') :
    (F̃).obj X ◁ (F̃).map v ≫ extendμ cF X Y' = extendμ cF X Y ≫ (F̃).map (X ◁ v) := by
  refine induction_on' (R := R) v ?_ (fun r v hv => ?_) (fun u v hu hv => ?_)
  · rw [Functor.map_zero, MonoidalSupercategory.whiskerLeft_zero R, whiskerLeft_zero',
      Functor.map_zero, Limits.zero_comp, Limits.comp_zero]
  · have hw : (ζPow R Y.par (F.obj Y.obj)).hom ≫ F.map (toHom v) ≫
        (ζPow R Y'.par (F.obj Y'.obj)).inv ∈ parity (R := R) _ _ (Y.par + r + Y'.par) := by
      simpa only [Category.assoc] using comp_mem (comp_mem (ζPow_hom_mem (R := R) Y.par
        (F.obj Y.obj)) (map_mem F hv)) (ζPow_inv_mem (R := R) Y'.par (F.obj Y'.obj))
    have hi := MonoidalSupercategory.super_interchange
      (ζPow_hom_mem (R := R) X.par (F.obj X.obj)) hw
    have hi' := congrArg (fun t => koszulSign X.par (Y.par + r + Y'.par) • t) hi
    simp only [koszulSign_smul_smul] at hi'
    simp only [extend_map, extendμ, tensorObj_obj, tensorObj_par]
    rw [toHom_whiskerLeft_of_mem X hv, Functor.map_smul]
    erw [reassoc_of% hi'.symm]
    simp only [MonoidalSupercategory.whiskerLeft_comp (R := R), Category.assoc,
      whiskerLeft_inv_hom'_assoc R, Iso.inv_hom_id_assoc, Linear.smul_comp, Linear.comp_smul]
    rw [reassoc_of% (cF.μ_natural_right _ _), koszulSign_smul (R := R)]
    congr 2
    ring
  · rw [Functor.map_add, MonoidalSupercategory.whiskerLeft_add (R := R), whiskerLeft_add',
      Functor.map_add, Preadditive.add_comp, Preadditive.comp_add, hu, hv]

omit [MonoidalSupercategory R A] in
/-- On objects `Π⁰λ`, `Π⁰μ` the coherence map `c̃` is `c`.-/
theorem extendμ_J (x y : A) : extendμ cF ((J R A).obj x) ((J R A).obj y) = (cF.μIso x y).hom := by
  show 𝟙 (F.obj x) ▷ F.obj y ≫ F.obj x ◁ 𝟙 (F.obj y) ≫ (cF.μIso x y).hom ≫ 𝟙 _ = _
  rw [MonoidalSupercategory.id_whiskerRight (R := R), MonoidalSupercategory.whiskerLeft_id (R := R),
    Category.id_comp, Category.id_comp, Category.comp_id]

omit [MonoidalSupercategory R A] in
theorem extendμ_J_tensor_left (x y z : A) :
    extendμ cF ((J R A).obj x ⊗ (J R A).obj y) ((J R A).obj z) = (cF.μIso (x ⊗ y) z).hom := by
  show 𝟙 (F.obj (x ⊗ y)) ▷ F.obj z ≫ F.obj (x ⊗ y) ◁ 𝟙 (F.obj z) ≫ (cF.μIso (x ⊗ y) z).hom ≫
    𝟙 _ = _
  rw [MonoidalSupercategory.id_whiskerRight (R := R), MonoidalSupercategory.whiskerLeft_id (R := R),
    Category.id_comp, Category.id_comp, Category.comp_id]

omit [MonoidalSupercategory R A] in
theorem extendμ_J_tensor_right (x y z : A) :
    extendμ cF ((J R A).obj x) ((J R A).obj y ⊗ (J R A).obj z) = (cF.μIso x (y ⊗ z)).hom := by
  show 𝟙 (F.obj x) ▷ F.obj (y ⊗ z) ≫ F.obj x ◁ 𝟙 (F.obj (y ⊗ z)) ≫ (cF.μIso x (y ⊗ z)).hom ≫
    𝟙 _ = _
  rw [MonoidalSupercategory.id_whiskerRight (R := R), MonoidalSupercategory.whiskerLeft_id (R := R),
    Category.id_comp, Category.id_comp, Category.comp_id]

omit [Preadditive A] [Linear R A] [Supercategory R A] [F.Additive] [F.Linear R]
  [IsSuperfunctor R F] [MonoidalCategoryStruct A] [MonoidalSupercategory R A]
  [MonoidalCategoryStruct B] [MonoidalSupercategory R B] in
/-- On morphisms between objects `Π⁰λ`, `F̃` is `F`.-/
theorem extend_map_J {x y : A} (f : (J R A).obj x ⟶ (J R A).obj y) :
    (F̃).map f = F.map (toHom f) := by
  show 𝟙 _ ≫ F.map (toHom f) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

/-- The left-hand side of the associativity axiom for `F̃`.-/
def assocL (X Y Z : Envelope R A) : ((F̃).obj X ⊗ (F̃).obj Y) ⊗ (F̃).obj Z ⟶ (F̃).obj (X ⊗ (Y ⊗ Z)) :=
  extendμ cF X Y ▷ (F̃).obj Z ≫ extendμ cF (X ⊗ Y) Z ≫ (F̃).map (α_ X Y Z).hom

/-- The right-hand side of the associativity axiom for `F̃`.-/
def assocR (X Y Z : Envelope R A) : ((F̃).obj X ⊗ (F̃).obj Y) ⊗ (F̃).obj Z ⟶ (F̃).obj (X ⊗ (Y ⊗ Z)) :=
  (α_ ((F̃).obj X) ((F̃).obj Y) ((F̃).obj Z)).hom ≫ (F̃).obj X ◁ extendμ cF Y Z ≫
    extendμ cF X (Y ⊗ Z)

theorem assocR_nat₁ {X X' : Envelope R A} (u : X ⟶ X') (Y Z : Envelope R A) :
    ((F̃).map u ▷ (F̃).obj Y) ▷ (F̃).obj Z ≫ assocR cF X' Y Z =
      assocR cF X Y Z ≫ (F̃).map (u ▷ (Y ⊗ Z)) := by
  simp only [assocR]
  rw [reassoc_of% (MonoidalSupercategory.associator_naturality_left R ((F̃).map u) _ _),
    reassoc_of% (interchange_even_right' R ((F̃).map u) (extendμ_mem cF Y Z)),
    extendμ_naturality_left]
  simp only [Category.assoc]

theorem assocR_nat₂ (X : Envelope R A) {Y Y' : Envelope R A} (v : Y ⟶ Y') (Z : Envelope R A) :
    ((F̃).obj X ◁ (F̃).map v) ▷ (F̃).obj Z ≫ assocR cF X Y' Z =
      assocR cF X Y Z ≫ (F̃).map (X ◁ (v ▷ Z)) := by
  simp only [assocR]
  rw [reassoc_of% (MonoidalSupercategory.associator_naturality_middle R _ ((F̃).map v) _),
    whiskerLeft_comp_comp R, extendμ_naturality_left, ← whiskerLeft_comp_comp R,
    extendμ_naturality_right]
  simp only [Category.assoc]

theorem assocR_nat₃ (X Y : Envelope R A) {Z Z' : Envelope R A} (w : Z ⟶ Z') :
    ((F̃).obj X ⊗ (F̃).obj Y) ◁ (F̃).map w ≫ assocR cF X Y Z' =
      assocR cF X Y Z ≫ (F̃).map (X ◁ (Y ◁ w)) := by
  simp only [assocR]
  rw [reassoc_of% (MonoidalSupercategory.associator_naturality_right R _ _ ((F̃).map w)),
    whiskerLeft_comp_comp R, extendμ_naturality_right, ← whiskerLeft_comp_comp R,
    extendμ_naturality_right]
  simp only [Category.assoc]

end Envelope

/-! ## The restriction argument for monoidal natural transformations -/

namespace Envelope

variable {R : Type w} [CommRing R]
  {A : Type w₁} [Category.{w₂} A] [Preadditive A] [Linear R A] [Supercategory R A]
  [MonoidalCategoryStruct A] [MonoidalSupercategory R A]
  {B : Type w₃} [Category.{w₄} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [MonoidalCategoryStruct B] [MonoidalSupercategory R B]

end Envelope

/-! ## Extension of monoidal natural transformations -/

namespace Envelope

variable {R : Type w} [CommRing R]
  {A : Type w₁} [Category.{w₂} A] [Preadditive A] [Linear R A] [Supercategory R A]
  [MonoidalCategoryStruct A] [MonoidalSupercategory R A]
  {B : Type w₃} [Category.{w₄} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [MonoidalCategoryStruct B] [MonoidalSupercategory R B] [PiSupercategory R B]
  {F G : A ⥤ B} [F.Additive] [F.Linear R] [IsSuperfunctor R F] [G.Additive] [G.Linear R]
  [IsSuperfunctor R G] {cF : MonoidalSuperfunctor R F} {cG : MonoidalSuperfunctor R G}

omit [MonoidalSupercategory R A] [MonoidalSupercategory R B] [PiSupercategory R B] in
/-- The components of a monoidal natural transformation form an even supernatural
transformation.-/
theorem isSupernatural_monoidalNatTrans {C : Type*} [Category C] [Preadditive C] [Linear R C]
    [Supercategory R C] [MonoidalCategoryStruct C] {F G : C ⥤ B} [F.Additive] [F.Linear R]
    [IsSuperfunctor R F] [G.Additive] [G.Linear R] [IsSuperfunctor R G]
    {cF : MonoidalSuperfunctor R F} {cG : MonoidalSuperfunctor R G}
    (x : MonoidalNatTrans R cF cG) : IsSupernatural R 0 x.toNatTrans.app :=
  isSupernatural_of_natTrans x.toNatTrans x.app_mem

omit [MonoidalSupercategory R A] [MonoidalSupercategory R B] [PiSupercategory R B] in
/-- Monoidal natural transformations with the same components are equal.-/
theorem monoidalNatTrans_eq {C : Type*} [Category C] [Preadditive C] [Linear R C]
    [Supercategory R C] [MonoidalCategoryStruct C] {F G : C ⥤ B} [F.Additive] [F.Linear R]
    [IsSuperfunctor R F] [G.Additive] [G.Linear R] [IsSuperfunctor R G]
    {cF : MonoidalSuperfunctor R F} {cG : MonoidalSuperfunctor R G}
    {x y : MonoidalNatTrans R cF cG} (h : ∀ X, x.toNatTrans.app X = y.toNatTrans.app X) :
    x = y := by
  have e : x.toNatTrans = y.toNatTrans := by ext1; funext X; exact h X
  cases x; cases y; cases e; rfl

/-- The natural transformation `x̃ : F̃ ⟶ G̃` extending the even supernatural
transformation underlying `x`, given by (4.2).-/
def extendNatTrans (x : MonoidalNatTrans R cF cG) : extend R F ⟶ extend R G :=
  (isSupernatural_extendNat (isSupernatural_monoidalNatTrans x)).toNatTrans

omit [MonoidalSupercategory R A] [MonoidalSupercategory R B] in
@[simp] theorem extendNatTrans_app (x : MonoidalNatTrans R cF cG) (X : Envelope R A) :
    (extendNatTrans x).app X = extendNat R F G 0 x.toNatTrans.app X :=
  IsSupernatural.toNatTrans_app _ X

omit [MonoidalSupercategory R A] [MonoidalSupercategory R B] in
theorem extendNatTrans_app_J (x : MonoidalNatTrans R cF cG) (y : A) :
    (extendNatTrans x).app ((J R A).obj y) = x.toNatTrans.app y := by
  rw [extendNatTrans_app, extendNat_zero_par]

omit [MonoidalSupercategory R A] [MonoidalSupercategory R B] in
theorem extendNatTrans_app_mem (x : MonoidalNatTrans R cF cG) (X : Envelope R A) :
    (extendNatTrans x).app X ∈ parity (R := R) _ _ 0 :=
  (isSupernatural_extendNat (isSupernatural_monoidalNatTrans x)).mem X

omit [MonoidalSupercategory R A] [MonoidalSupercategory R B] [PiSupercategory R B] in
/-- **Lemma 4.7(ii), monoidal case, uniqueness.** A monoidal natural transformation
`F̃ ⇒ G̃` is determined by its components at the objects `Π⁰λ`.-/
theorem monoidalNatTrans_ext {F' G' : Envelope R A ⥤ B} [F'.Additive] [F'.Linear R]
    [IsSuperfunctor R F'] [G'.Additive] [G'.Linear R] [IsSuperfunctor R G']
    {cF' : MonoidalSuperfunctor R F'} {cG' : MonoidalSuperfunctor R G'}
    {y y' : MonoidalNatTrans R cF' cG'}
    (h : ∀ z : A, y.toNatTrans.app ((J R A).obj z) = y'.toNatTrans.app ((J R A).obj z)) :
    y = y' := by
  refine monoidalNatTrans_eq fun X => ?_
  exact congrFun (eq_of_restrict_eq (isSupernatural_monoidalNatTrans y) (isSupernatural_monoidalNatTrans y') h) X

end Envelope

/-! ## Monoidal superfunctors out of the Π-envelope -/

namespace Envelope

variable {R : Type w} [CommRing R]
  {A : Type w₁} [Category.{w₂} A] [Preadditive A] [Linear R A] [Supercategory R A]
  [MonoidalCategoryStruct A] [MonoidalSupercategory R A]
  {B : Type w₃} [Category.{w₄} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [MonoidalCategoryStruct B] [MonoidalSupercategory R B]
  {H : Envelope R A ⥤ B} [H.Additive] [H.Linear R] [IsSuperfunctor R H]

omit [MonoidalSupercategory R A] [MonoidalSupercategory R B] in
theorem J_map_whiskerRight {x y : A} (f : x ⟶ y) (z : A) :
    (J R A).map f ▷ (J R A).obj z = (J R A).map (f ▷ z) :=
  hom_ext (toHom_whiskerRight_of_par_zero _ _ rfl)

omit [MonoidalSupercategory R A] [MonoidalSupercategory R B] in
theorem J_map_whiskerLeft (z : A) {x y : A} (f : x ⟶ y) :
    (J R A).obj z ◁ (J R A).map f = (J R A).map (z ◁ f) :=
  hom_ext (toHom_whiskerLeft_of_par_zero _ rfl _)

/-- The restriction `H J : A → B` of a monoidal superfunctor `H : A_π → B`, with the coherence
maps of `H` at objects `Π⁰λ`.-/
def restrictMonoidal (cH : MonoidalSuperfunctor R H) : MonoidalSuperfunctor R (J R A ⋙ H) where
  μIso x y := cH.μIso ((J R A).obj x) ((J R A).obj y)
  εIso := cH.εIso
  μ_mem x y := cH.μ_mem _ _
  ε_mem := cH.ε_mem
  μ_natural_left f x' := by
    have := cH.μ_natural_left ((J R A).map f) ((J R A).obj x')
    rw [J_map_whiskerRight] at this
    exact this
  μ_natural_right x' f := by
    have := cH.μ_natural_right ((J R A).obj x') ((J R A).map f)
    rw [J_map_whiskerLeft] at this
    exact this
  associativity x y z := cH.associativity _ _ _
  left_unitality x := cH.left_unitality _
  right_unitality x := cH.right_unitality _

variable [PiSupercategory R B]

omit [MonoidalCategoryStruct A] [MonoidalSupercategory R A] [MonoidalCategoryStruct B]
  [MonoidalSupercategory R B] in
theorem extendRestrictIso_hom_app_J (x : A) :
    (extendRestrictIso H).hom.app ((J R A).obj x) = 𝟙 _ := by
  show 𝟙 _ ≫ H.map (𝟙 _) = _
  rw [H.map_id, Category.comp_id]
  rfl

omit [MonoidalCategoryStruct A] [MonoidalSupercategory R A] [MonoidalCategoryStruct B]
  [MonoidalSupercategory R B] in
set_option backward.isDefEq.respectTransparency false in
theorem extendRestrictIso_inv_app_J (x : A) :
    (extendRestrictIso H).inv.app ((J R A).obj x) = 𝟙 _ := by
  have := (extendRestrictIso H).hom_inv_id_app ((J R A).obj x)
  rw [extendRestrictIso_hom_app_J, Category.id_comp] at this
  exact this

omit [MonoidalCategoryStruct A] [MonoidalSupercategory R A] [MonoidalCategoryStruct B]
  [MonoidalSupercategory R B] in
theorem extendRestrictIso_inv_mem (X : Envelope R A) :
    (extendRestrictIso H).inv.app X ∈ parity (R := R) _ _ 0 := by
  have := inv_mem ((extendRestrictIso H).app X) (extendRestrictIso_hom_mem H X)
  exact this

end Envelope

/-! ## Monoidal Π-supercategories -/

namespace Envelope

variable {R : Type w} [CommRing R]
  {A : Type w₁} [Category.{w₂} A] [Preadditive A] [Linear R A] [Supercategory R A]
  [MonoidalCategoryStruct A] [MonoidalSupercategory R A]
  {B : Type w₃} [Category.{w₄} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [MonoidalCategoryStruct B] [MonoidalSupercategory R B] [MonoidalPiSupercategory R B]

end Envelope

end StringDiagrams

end

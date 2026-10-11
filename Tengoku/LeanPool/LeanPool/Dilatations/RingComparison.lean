/-
Copyright (c) 2026 Arnaud Mayeux, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arnaud Mayeux, Jujian Zhang
-/
module

public import Tengoku.LeanPool.LeanPool.Dilatations.Centers
public import Tengoku.LeanPool.LeanPool.Dilatations.Rings
public import Tengoku

/-!
# Exponent-profile centers recover ring dilatations

From Arnaud Mayeux, *Dilatations of categories, via their Lean formalization*,
https://arxiv.org/abs/2608.09305, and `rndmx/DilCat` at commit
`604559654c948566675da3f7709b8ad3126bd487` (Apache-2.0).
The ring construction includes work by Arnaud Mayeux and Jujian Zhang from
`ProjConstruction/Proj` (Apache-2.0).
-/

@[expose] public section

noncomputable section

open CategoryTheory Finset
open CategoryTheory.Localization.Construction

universe v u v' pu pv u₁ v₁ u₂ v₂ u₃ v₃

namespace CategoryTheory.Dilatations

variable {C : Type u} [Category.{v} C]
variable (Z : Center C)
variable {D : Type u} [Category.{v'} D]
variable (F : C ⥤ D)

open Family

/-! ## The corrected ring comparison

The one-object category `SingleObj A'` has the elements of the commutative ring `A'`
as morphisms, with composition given by multiplication. A multicenter supplies a categorical
center indexed by finitely supported exponent profiles `ν`: the denominator is `M.elem ^ ν`,
and the numerator sieve comes from `M.LargeIdeal ^ ν`. Each enlarged ideal is
`M.LargeIdeal i = M.ideal i + (M.elem i)`.

The resulting dilatation is isomorphic to `SingleObj A'[M]` (Theorem 10.1 of the source).
This replaces the naive single-index identification in the original Proposition 5.1;
`NaiveCenterCounterexample` gives the explicit obstruction to that earlier statement.
-/
namespace Prop51

open CategoryTheory Multicenter Multicenter.Dilatation

variable {A' : Type u} [CommRing A']

/-- An ideal of `A'`, regarded as a sieve over the unique object of `SingleObj A'`: ideals absorb
multiplication by arbitrary ring elements, which is exactly a sieve's stability under
precomposition, since composition in `SingleObj A'` *is* ring multiplication. -/
def Sieve.ofIdeal (I : Ideal A') : Sieve (CategoryTheory.SingleObj.star A') where
  arrows {_} f := (f : A') ∈ I
  downward_closed {_ _ f} hf g := by
    change (f * g : A') ∈ I
    exact I.mul_mem_right g hf

/-- A `Multicenter A'` as a `Center (SingleObj A')`, indexed by exponent profiles `ν : M^ℕ`: the
generator at `ν` divides by `aᵢ ^ ν := M.elem ^ ν` with numerator ranging over `M.LargeIdeal ^ ν`,
matching `Dilatation.frac` exactly (needed for `Phi51` to be surjective — a single-index
generator only reaches products, not sums, of `LargeIdeal` elements). -/
def centerOfMulticenter (M : Multicenter A') :
    Center (CategoryTheory.SingleObj A') where
  I := M^ℕ
  nonempty := ⟨0⟩
  dom _ := CategoryTheory.SingleObj.star A'
  cod _ := CategoryTheory.SingleObj.star A'
  mor ν := M.elem ^ ν
  N ν := Sieve.ofIdeal (M.LargeIdeal ^ ν)

variable (M : Multicenter A')

/-- The functor `SingleObj A' ⥤ SingleObj A'[M]` induced by the canonical ring map `A' → A'[M]`
(`CategoryTheory.SingleObj.mapHom` turns any monoid hom into a functor between the attached
one-object categories). This plays the role of `Θ` on the "attached-to-a-ring" side. -/
def toDilatationFunctor : CategoryTheory.SingleObj A' ⥤ CategoryTheory.SingleObj A'[M] :=
  CategoryTheory.SingleObj.mapHom A' A'[M] (algebraMap A' A'[M]).toMonoidHom

/-- **General fact**: in the one-object category `SingleObj R` attached to a monoid `R`, a
morphism is an isomorphism iff it is a unit of `R` — composition unwinds to multiplication
(`SingleObj.comp_as_mul`), so a two-sided categorical inverse is exactly a two-sided
multiplicative inverse. -/
lemma isIso_iff_isUnit {R : Type*} [Monoid R]
    (x : CategoryTheory.SingleObj.star R ⟶ CategoryTheory.SingleObj.star R) :
    CategoryTheory.IsIso x ↔ IsUnit x := by
  constructor
  · intro h
    have := h
    refine ⟨⟨x, CategoryTheory.inv x, ?_, ?_⟩, rfl⟩
    · change x * CategoryTheory.inv x = (1 : R)
      have := CategoryTheory.IsIso.inv_hom_id x
      rwa [CategoryTheory.SingleObj.comp_as_mul, CategoryTheory.SingleObj.id_as_one] at this
    · change CategoryTheory.inv x * x = (1 : R)
      have := CategoryTheory.IsIso.hom_inv_id x
      rwa [CategoryTheory.SingleObj.comp_as_mul, CategoryTheory.SingleObj.id_as_one] at this
  · rintro ⟨u, rfl⟩
    refine ⟨⟨(↑u⁻¹ : R), ?_, ?_⟩⟩
    · change (↑u⁻¹ : R) * (↑u : R) = (1 : R)
      exact u.inv_mul
    · change (↑u : R) * (↑u⁻¹ : R) = (1 : R)
      exact u.mul_inv

/-- **General fact**: if `W.IsInvertedBy e` for some *faithful* `e`, then `W.Q` is faithful —
`e` factors as `W.Q ⋙ (lift of e)` (universal property of the localization), and a functor whose
composite with something else is faithful is itself faithful (`faithful_of_comp_faithful_gen`,
applied to the *lift*, not `e` itself : here we need the reverse composition order, so we go via
`e`'s own factorization instead). -/
lemma faithful_Q_of_isInvertedBy_of_faithful {E : Type u} [Category.{v'} E] (W : MorphismProperty E)
    {E' : Type u} [Category.{v'} E'] (e : E ⥤ E') (he : W.IsInvertedBy e) (hefaith : e.Faithful) :
    W.Q.Faithful := by
  apply faithful_of_comp_faithful_gen W.Q (Localization.Construction.lift e he)
  rw [Localization.Construction.fac]
  exact hefaith

/-- The images of `M`'s generators in `A'[M]` are non-zero-divisors — an unconditional structural
fact about dilatations (`Multicenter.Dilatation.nonzerodiv_image`, specialized to a single
generator). -/
lemma nonzerodiv_image_single (i : M.index) :
    algebraMap A' A'[M] (M.elem i) ∈ nonZeroDivisors A'[M] := by
  have h := Multicenter.Dilatation.nonzerodiv_image (M := M) (Finsupp.single i 1)
  simpa [familyPow_def] using h

/-! ##### Injectivity of `Φ`

Compare both `Φ` and the (unconditionally faithful) raw-localization comparison `DilaToLoc`
against a common target : the categorical localization `(CenterMorphismProperty
(centerOfMulticenter M)).Localization`, reached from `SingleObj A'[M]` via the *ring-theoretic*
localization of `A'` at `M`'s generators (using the monoid-level universal property of
`Localization`, since the target's endomorphism monoid need not be a ring). -/
/-- `M`'s generators, viewed as a submonoid of `A'` itself (not of `A'[M]`). -/
def genSubmonoid : Submonoid A' :=
  Submonoid.closure (Set.range M.elem)

lemma genSubmonoid_nonZeroDivisors (i : M.index) :
    algebraMap A' (Localization (genSubmonoid M)) (M.elem i) ∈
      nonZeroDivisors (Localization (genSubmonoid M)) :=
  (IsLocalization.map_units (Localization (genSubmonoid M))
    (⟨M.elem i, Submonoid.subset_closure ⟨i, rfl⟩⟩ : genSubmonoid M)).mem_nonZeroDivisors

lemma genSubmonoid_gen (i : M.index) :
    Ideal.span {algebraMap A' (Localization (genSubmonoid M)) (M.elem i)} =
      Ideal.map (algebraMap A' (Localization (genSubmonoid M))) (M.LargeIdeal i) := by
  have hunit : IsUnit (algebraMap A' (Localization (genSubmonoid M)) (M.elem i)) :=
    IsLocalization.map_units (Localization (genSubmonoid M))
      (⟨M.elem i, Submonoid.subset_closure ⟨i, rfl⟩⟩ : genSubmonoid M)
  have hspan_top : Ideal.span {algebraMap A' (Localization (genSubmonoid M)) (M.elem i)} = ⊤ :=
    Ideal.span_singleton_eq_top.mpr hunit
  have hmap_top :
      Ideal.map (algebraMap A' (Localization (genSubmonoid M))) (M.LargeIdeal i) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (M.elem_mem_LargeIdeal i)) hunit
  rw [hspan_top, hmap_top]

/-- The canonical map from `A'[M]` into the *full* localization of `A'` at the generators —
trivial to build via `desc`, since generators become units there. -/
noncomputable def descToLoc : A'[M] →ₐ[A'] Localization (genSubmonoid M) :=
  Multicenter.desc M (genSubmonoid_nonZeroDivisors M) (genSubmonoid_gen M)

/-- `A'`, as a monoid hom into the endomorphism monoid of the raw localization
`(CenterMorphismProperty (centerOfMulticenter M)).Localization`, matching
`LocalizationFunctor (centerOfMulticenter M)`. -/
def toLocEnd : A' →* CategoryTheory.End
    ((LocalizationFunctor (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A')) where
  toFun a := (LocalizationFunctor (centerOfMulticenter M)).map
    (a : CategoryTheory.SingleObj.star A' ⟶ CategoryTheory.SingleObj.star A')
  map_one' := by
    change (LocalizationFunctor (centerOfMulticenter M)).map
        (𝟙 (CategoryTheory.SingleObj.star A')) =
      𝟙 ((LocalizationFunctor (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A'))
    rw [CategoryTheory.Functor.map_id]
  map_mul' a b := by
    change (LocalizationFunctor (centerOfMulticenter M)).map
        ((a * b : A') : CategoryTheory.SingleObj.star A' ⟶ CategoryTheory.SingleObj.star A') =
      (LocalizationFunctor (centerOfMulticenter M)).map
          (b : CategoryTheory.SingleObj.star A' ⟶ CategoryTheory.SingleObj.star A') ≫
        (LocalizationFunctor (centerOfMulticenter M)).map
          (a : CategoryTheory.SingleObj.star A' ⟶ CategoryTheory.SingleObj.star A')
    rw [← CategoryTheory.SingleObj.comp_as_mul, CategoryTheory.Functor.map_comp]

lemma toLocEnd_inverts_gen : ∀ y : genSubmonoid M, IsUnit (toLocEnd M (y : A')) := by
  rintro ⟨y, hy⟩
  induction hy using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [CategoryTheory.isUnit_iff_isIso]
    change CategoryTheory.IsIso (toLocEnd M (M.elem i))
    exact CategoryTheory.MorphismProperty.Q_inverts (CenterMorphismProperty (centerOfMulticenter M))
      (M.elem i : CategoryTheory.SingleObj.star A' ⟶ CategoryTheory.SingleObj.star A')
      ⟨Finsupp.single i 1, by
        have heq : M.elem i = M.elem ^ (Finsupp.single i 1) := by simp [familyPow_def]
        exact congrArg
          (fun x => (⟨CategoryTheory.SingleObj.star A', CategoryTheory.SingleObj.star A', x⟩ :
            Σ X Y : CategoryTheory.SingleObj A', X ⟶ Y)) heq⟩
  | one =>
    rw [CategoryTheory.isUnit_iff_isIso]
    change CategoryTheory.IsIso (toLocEnd M (1 : A'))
    rw [map_one, CategoryTheory.End.one_def]
    infer_instance
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy

/-- General fact : if `u` commutes with `v₁` and with `v₂`, it commutes with `v₁ ≫ v₂`. -/
private lemma commutesComp {E : Type*} [CategoryTheory.Category E] {X : E} {u v₁ v₂ : X ⟶ X}
    (h₁ : u ≫ v₁ = v₁ ≫ u) (h₂ : u ≫ v₂ = v₂ ≫ u) : u ≫ (v₁ ≫ v₂) = (v₁ ≫ v₂) ≫ u := by
  rw [← CategoryTheory.Category.assoc, h₁, CategoryTheory.Category.assoc, h₂,
    ← CategoryTheory.Category.assoc]

/-- General fact : if `u` commutes with the `hom` of an iso `α : X ≅ X`, it commutes with
`α.inv` too. Stated for an explicit `Iso` (rather than `[IsIso _]`) so that it applies directly
to `Localization.Construction.wIso`, without worrying about which `IsIso` witness is in scope. -/
private lemma commutesInv {E : Type*} [CategoryTheory.Category E] {X : E} {u : X ⟶ X}
    (α : X ≅ X) (h : u ≫ α.hom = α.hom ≫ u) : u ≫ α.inv = α.inv ≫ u := by
  rw [CategoryTheory.Iso.comp_inv_eq, CategoryTheory.Category.assoc, h,
    ← CategoryTheory.Category.assoc, α.inv_hom_id, CategoryTheory.Category.id_comp]

/-- **Key structural fact**: since `A'` is commutative, every image `toLocEnd M a` is *central*
in the raw localization's endomorphism monoid — it commutes with everything. Proved via
`Localization.Construction.morphismProperty_eq_top`: a `MorphismProperty` stable under
composition, containing every generator-image and every formal inverse, is everything. -/
lemma genImage_central (a : A') :
    ∀ ⦃X Y : (CenterMorphismProperty (centerOfMulticenter M)).Localization⦄ (v : X ⟶ Y),
      (toLocEnd M a) ≫ v = v ≫ (toLocEnd M a) := by
  let P : CategoryTheory.MorphismProperty
      (CenterMorphismProperty (centerOfMulticenter M)).Localization :=
    fun _ _ v => (toLocEnd M a) ≫ v = v ≫ (toLocEnd M a)
  have : P.IsStableUnderComposition := ⟨fun _ _ hf hg => commutesComp hf hg⟩
  have hP : P = ⊤ := by
    apply Localization.Construction.morphismProperty_eq_top P
    · intro X Y f
      change toLocEnd M a ≫ toLocEnd M (f : A') = toLocEnd M (f : A') ≫ toLocEnd M a
      rw [← CategoryTheory.End.mul_def, ← CategoryTheory.End.mul_def, ← map_mul, ← map_mul,
        mul_comm]
    · intro X Y w hw
      change toLocEnd M a ≫ (Localization.Construction.wIso w hw).inv =
        (Localization.Construction.wIso w hw).inv ≫ toLocEnd M a
      apply commutesInv (Localization.Construction.wIso w hw)
      change toLocEnd M a ≫ toLocEnd M (w : A') = toLocEnd M (w : A') ≫ toLocEnd M a
      rw [← CategoryTheory.End.mul_def, ← CategoryTheory.End.mul_def, ← map_mul, ← map_mul,
        mul_comm]
  intro X Y v
  simpa only [← hP] using CategoryTheory.MorphismProperty.top_apply v

/-- The single object of the raw localization, viewed as an object of
`(CenterMorphismProperty (centerOfMulticenter M)).Localization`. -/
noncomputable abbrev localizationPoint : (CenterMorphismProperty (centerOfMulticenter
    M)).Localization :=
  (LocalizationFunctor (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A')

/-- Every object of the raw localization is (canonically, but non-computably) equal to
    `localizationPoint`,
since the localization of a single-object category is again single-object. -/
lemma isoObj_eq_localizationPoint :
    ∀ X : (CenterMorphismProperty (centerOfMulticenter M)).Localization, X = localizationPoint
      M := by
  have : Subsingleton (CenterMorphismProperty (centerOfMulticenter M)).Localization :=
    Equiv.subsingleton.symm (CategoryTheory.Localization.Construction.objEquiv
      (CenterMorphismProperty (centerOfMulticenter M)))
  intro X
  exact Subsingleton.elim _ _

/-- Cast a morphism between arbitrary objects of the raw localization into an endomorphism of
`localizationPoint`, using that the localization has (up to equality) a single object. -/
noncomputable def castEndomorphism ⦃X Y : (CenterMorphismProperty (centerOfMulticenter
    M)).Localization⦄
    (u : X ⟶ Y) : CategoryTheory.End (localizationPoint M) :=
  CategoryTheory.eqToHom (isoObj_eq_localizationPoint M X).symm ≫ u ≫
    CategoryTheory.eqToHom (isoObj_eq_localizationPoint M Y)

private lemma castE_comp ⦃X Y Z : (CenterMorphismProperty (centerOfMulticenter M)).Localization⦄
    (f : X ⟶ Y) (g : Y ⟶ Z) : castEndomorphism M (f ≫ g) = castEndomorphism M f ≫
      castEndomorphism M g := by
  change CategoryTheory.eqToHom _ ≫ (f ≫ g) ≫ CategoryTheory.eqToHom _ =
    (CategoryTheory.eqToHom _ ≫ f ≫ CategoryTheory.eqToHom _) ≫
      (CategoryTheory.eqToHom _ ≫ g ≫ CategoryTheory.eqToHom _)
  simp only [CategoryTheory.Category.assoc, eqToHom_trans_assoc, CategoryTheory.eqToHom_refl,
    CategoryTheory.Category.id_comp]

private lemma castE_eq_self (u : CategoryTheory.End (localizationPoint M)) : castEndomorphism
    M u = u := by
  change CategoryTheory.eqToHom _ ≫ u ≫ CategoryTheory.eqToHom _ = u
  simp only [CategoryTheory.eqToHom_refl, CategoryTheory.Category.id_comp,
    CategoryTheory.Category.comp_id]

/-- **Key structural fact, part 2**: *every* endomorphism of the raw localization is central
(commutes with everything) — same argument as `genImage_central`, one level up : generator-images
are central by `genImage_central`, and formal inverses of central elements are central too. -/
lemma allCentral (v : CategoryTheory.End (localizationPoint M)) :
    ∀ ⦃X Y : (CenterMorphismProperty (centerOfMulticenter M)).Localization⦄ (u : X ⟶ Y),
      castEndomorphism M u ≫ v = v ≫ castEndomorphism M u := by
  let P : CategoryTheory.MorphismProperty
      (CenterMorphismProperty (centerOfMulticenter M)).Localization :=
    fun _ _ u => castEndomorphism M u ≫ v = v ≫ castEndomorphism M u
  have hcomp : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z), P f → P g → P (f ≫ g) := by
    intro X Y Z f g hf hg
    change castEndomorphism M (f ≫ g) ≫ v = v ≫ castEndomorphism M (f ≫ g)
    rw [castE_comp, CategoryTheory.Category.assoc, hg, ← CategoryTheory.Category.assoc, hf,
      CategoryTheory.Category.assoc]
  have : P.IsStableUnderComposition := ⟨hcomp⟩
  have hP : P = ⊤ := by
    apply Localization.Construction.morphismProperty_eq_top P
    · intro X Y f
      change castEndomorphism M ((LocalizationFunctor (centerOfMulticenter M)).map f) ≫ v =
        v ≫ castEndomorphism M ((LocalizationFunctor (centerOfMulticenter M)).map f)
      obtain rfl : X = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
      obtain rfl : Y = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
      rw [castE_eq_self]
      exact genImage_central M (f : A') v
    · intro X Y w hw
      obtain rfl : X = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
      obtain rfl : Y = CategoryTheory.SingleObj.star A' := Subsingleton.elim _ _
      change castEndomorphism M (Localization.Construction.wIso w hw).inv ≫ v =
        v ≫ castEndomorphism M (Localization.Construction.wIso w hw).inv
      erw [castE_eq_self]
      apply Eq.symm
      apply commutesInv (Localization.Construction.wIso w hw)
      change v ≫ (LocalizationFunctor (centerOfMulticenter M)).map w =
        (LocalizationFunctor (centerOfMulticenter M)).map w ≫ v
      exact (genImage_central M (w : A') v).symm
  intro X Y u
  simpa only [← hP] using CategoryTheory.MorphismProperty.top_apply u

/-- The endomorphism monoid of the raw localization's single object is commutative : this is
what makes `LocEndLift` (a monoid-localization universal-property construction) type-check. -/
noncomputable instance commEnd : CommMonoid (CategoryTheory.End (localizationPoint M)) where
  __ := CategoryTheory.End.monoid
  mul_comm u v := by
    change v ≫ u = u ≫ v
    have h := allCentral M v u
    rw [castE_eq_self] at h
    exact h.symm

/-- The universal monoid-level extension of `toLocEnd` along `A' → Localization (genSubmonoid M)`
(the generators already become units under `toLocEnd`, so the monoid-localization universal
property applies unconditionally). -/
noncomputable def LocEndLift :
    Localization (genSubmonoid M) →* CategoryTheory.End
      ((LocalizationFunctor (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A')) :=
  (IsLocalization.toLocalizationMap (genSubmonoid M) (Localization (genSubmonoid M))).lift
    (g := toLocEnd M) (toLocEnd_inverts_gen M)

/-- The comparison map `A'[M] → (CenterMorphismProperty (centerOfMulticenter M)).Localization`,
as a monoid hom on the (single) Hom-set. -/
noncomputable def kappaHom : A'[M] →* CategoryTheory.End
    ((LocalizationFunctor (centerOfMulticenter M)).obj (CategoryTheory.SingleObj.star A')) :=
  (LocEndLift M).comp (descToLoc M).toRingHom.toMonoidHom

/-- `kappaHom` as a functor `SingleObj A'[M] ⥤ (CenterMorphismProperty
(centerOfMulticenter M)).Localization`. -/
noncomputable def kappaFunctor :
    CategoryTheory.SingleObj A'[M] ⥤
      (CenterMorphismProperty (centerOfMulticenter M)).Localization :=
  CategoryTheory.SingleObj.functor (kappaHom M)

/-! ##### Surjectivity of `Φ`

With the `ν`-indexed sieve, a *single* fraction-generator edge at profile `ν` already reaches an
*arbitrary* element of `LargeIdeal ^ ν` (the whole ideal, not just a product of simpler pieces), so
every `Dilatation.frac` fraction — hence every element of `A'[M]`, by `induction_on` — is directly
the `Φ`-image of one such generator. No path/product induction is needed at all. -/

/-! ##### Packaging `Φ` into an isomorphism of categories

`Phi51` is full and faithful, and both `Dila (centerOfMulticenter M)` and `SingleObj A'[M]` have a
single object, so `Φ` restricts to a bijection on the (unique) Hom-set — a `MonoidHom` inverse to
`Phi51.map` builds the inverse functor `Psi51` directly, mirroring `Iso315` in Proposition 3.15. -/

end Prop51

end CategoryTheory.Dilatations

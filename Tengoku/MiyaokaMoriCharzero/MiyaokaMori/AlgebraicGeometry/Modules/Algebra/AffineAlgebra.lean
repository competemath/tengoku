import Tengoku.Seed.AlgebraicGeometry.Sites.SmallAffineZariski
import Tengoku.Seed.AlgebraicGeometry.RelativeGluing
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Affine

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Quasi-coherent algebras on the small affine Zariski site and their relative Spec

A **quasi-coherent `O_X`-algebra** on `X`, encoded as a presheaf of commutative rings `ring` on the small
affine Zariski site `X.AffineZariskiSite` (objects: affine opens; arrows: principal opens `D(f) ⊆ U`)
together with a structure map `unit : O_X ⟶ ring`; **quasi-coherence is a field**
`coequifibered : unit.Coequifibered` (⇔ for every affine open `U` and `f ∈ Γ(X,U)`,
`ring(D(f)) = ring(U)[1/f]`; Mathlib `coequifibered_iff_forall_isLocalizationAway`). The relative Spec
`A.relativeSpec : Over X` is the gluing of Mathlib's `Scheme.AffineZariskiSite.relativeGluingData` (the same
machinery as Mathlib's `Scheme.Hom.normalization`); the charts `A.chart U : Spec A(U) ⟶ Spec_X A` are open
immersions, `π⁻¹U = range (chart U)`, the chart squares are pullbacks, and the structure morphism is affine.
Algebra homomorphisms `AffineAlgebra.Hom` give `relativeSpec.map` contravariantly.

Design: the quasi-coherent algebras used in the paper (jet algebras `J_r(B_U, ε_U)`, `⊕ L^{-q}`, `Sym E^∨`) are
all given by "rings on affine opens compatible with localization", and sections over non-affine opens are
never needed. The encoding on the affine site makes the data fully constructive, and quasi-coherence is a
propositional field proved case by case, with no fallback branch. This agrees with Mathlib's direction:
`SmallAffineZariski.lean` describes `Coequifibered` as "quasi-coherent `𝒪ₓ`-algebras".

References: Stacks 01LL–01LQ (relative Spec); Mathlib `AlgebraicGeometry/Sites/SmallAffineZariski.lean`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- A quasi-coherent `O_X`-algebra on `X`: a presheaf of rings on the affine site + structure map +
compatibility with localization.-/
structure AffineAlgebra (X : Scheme.{u}) where
  /-- Affine open `U ↦` ring `A(U)`; principal open `D(f) ⊆ U ↦` restriction map.-/
  ring : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}
  /-- The structure map `O_X(U) → A(U)`.-/
  unit : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ ring
  /-- Quasi-coherence: `A(D(f)) = A(U)[1/f]`.-/
  coequifibered : unit.Coequifibered

namespace AffineAlgebra

variable {X : Scheme.{u}} (A : X.AffineAlgebra)

/-- The section ring on an affine open `U`.-/
abbrev sections (U : X.AffineZariskiSite) : CommRingCat.{u} := A.ring.obj (op U)

/-- The restriction map `A(V) → A(U)` (`U ≤ V`, i.e. `U` is a principal open of `V`).-/
def restrict {U V : X.AffineZariskiSite} (h : U ≤ V) : A.sections V →+* A.sections U :=
  (A.ring.map (homOfLE h).op).hom

/-- The structure map `Γ(X, U) → A(U)`.-/
def unitHom (U : X.AffineZariskiSite) : Γ(X, U.toOpens) →+* A.sections U :=
  (A.unit.app (op U)).hom

/--
@isnad1 id=eq.0h4v.s7.30edd8dbd559 from=translated src=- shape=d447fe5a vocab=02e2f4bf
-/
@[simp] theorem restrict_refl (U : X.AffineZariskiSite) (a : A.sections U) :
    A.restrict (le_refl U) a = a := by
  show (A.ring.map (𝟙 (op U))).hom a = a
  rw [A.ring.map_id]; rfl

/--
@isnad1 id=eq.2h6v.s8.6491a9a5d35c from=translated src=- shape=bb5e2f20 vocab=ca0b0c75
-/
theorem restrict_restrict {U V W : X.AffineZariskiSite} (hUV : U ≤ V) (hVW : V ≤ W)
    (a : A.sections W) : A.restrict hUV (A.restrict hVW a) = A.restrict (hUV.trans hVW) a := by
  show ((A.ring.map (homOfLE hVW).op) ≫ (A.ring.map (homOfLE hUV).op)).hom a = _
  rw [← A.ring.map_comp]; rfl

/-- The structure map commutes with restriction.
@isnad1 id=eq.1h5v.s12.07ef961f455a from=translated src=- shape=020a4b99 vocab=b198c055
-/
theorem restrict_unitHom {U V : X.AffineZariskiSite} (h : U ≤ V) (r : Γ(X, V.toOpens)) :
    A.restrict h (A.unitHom V r) =
      A.unitHom U ((X.presheaf.map (homOfLE (AffineZariskiSite.toOpens_mono h)).op).hom r) :=
  (congrArg (fun φ => φ.hom r) (A.unit.naturality (homOfLE h).op)).symm

/-- **Usable form of quasi-coherence**: `A(D(f))` is the localization of `A(U)` at the image of `f`.
@isnad1 id=away.0h4v.s10.2284cf9cd7dd from=translated src=- shape=78e6b040 vocab=a3312508
-/
theorem isLocalization_basicOpen (U : X.AffineZariskiSite) (f : Γ(X, U.toOpens)) :
    letI := (A.restrict (U.basicOpen_le f)).toAlgebra
    IsLocalization.Away (A.unitHom U f) (A.sections (U.basicOpen f)) :=
  AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mp A.coequifibered U f

/-- The gluing data: the `Spec A(U)` over the `U`.-/
def gluingData : (AffineZariskiSite.directedCover X).RelativeGluingData :=
  AffineZariskiSite.relativeGluingData A.coequifibered

/--
@isnad1 id=islocall.0h2v.s6.8f2298290f5d from=translated src=- shape=c0d88263 vocab=0ced6321
-/
instance gluingData_isLocallyDirected :
    (A.gluingData.functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- **The relative Spec** `Spec_X A → X`.-/
def relativeSpec : Over X := Over.mk A.gluingData.toBase

/-- The chart `Spec A(U) → Spec_X A`.-/
def chart (U : X.AffineZariskiSite) : Spec (A.sections U) ⟶ A.relativeSpec.left :=
  colimit.ι A.gluingData.functor U

/--
@isnad1 id=isopenim.0h3v.s4.b72dbcb6cdd4 from=translated src=- shape=a1cec9bb vocab=3ee5a5c1
-/
instance chart_isOpenImmersion (U : X.AffineZariskiSite) : IsOpenImmersion (A.chart U) := by
  change IsOpenImmersion (colimit.ι A.gluingData.functor U)
  infer_instance

/-- The morphism from the chart to `U`: `Spec(unit)` followed by the inverse of `U ≅ Spec Γ(X,U)`.-/
def chartToOpen (U : X.AffineZariskiSite) : Spec (A.sections U) ⟶ U.toOpens.toScheme :=
  Spec.map (A.unit.app (op U)) ≫ U.2.isoSpec.inv

/--
@isnad1 id=eq.0h3v.s7.700dac0a13eb from=translated src=- shape=feea3698 vocab=b3e1ccca
-/
theorem gluingData_natTrans_app (U : X.AffineZariskiSite) :
    A.gluingData.natTrans.app U = A.chartToOpen U := rfl

/--
@isnad1 id=eq.0h3v.s6.81d3ea3fca5b from=translated src=- shape=8e47e7e6 vocab=0beffc41
-/
@[reassoc (attr := simp)]
theorem chart_hom (U : X.AffineZariskiSite) :
    A.chart U ≫ A.relativeSpec.hom = A.chartToOpen U ≫ U.toOpens.ι := by
  change colimit.ι A.gluingData.functor U ≫ A.gluingData.toBase = _
  rw [A.gluingData.ι_toBase U]
  rfl

/-- The charts are compatible with restriction.
@isnad1 id=eq.1h4v.s7.fda9e6ad8fd8 from=translated src=- shape=448b823f vocab=6205bf50
-/
@[reassoc]
theorem map_chart {U V : X.AffineZariskiSite} (h : U ≤ V) :
    Spec.map (A.ring.map (homOfLE h).op) ≫ A.chart V = A.chart U :=
  colimit.w A.gluingData.functor (homOfLE h)

/-- `π⁻¹(U)` is the image of the chart.
@isnad1 id=eq.0h3v.s8.a59129d1cb65 from=translated src=- shape=4d501ee4 vocab=94f127e1
-/
theorem preimage_eq_opensRange (U : X.AffineZariskiSite) :
    A.relativeSpec.hom ⁻¹ᵁ U.toOpens = (A.chart U).opensRange := by
  have h := A.gluingData.toBase_preimage_eq_opensRange_ι U
  rw [← show A.gluingData.toBase ⁻¹ᵁ ((AffineZariskiSite.directedCover X).f U).opensRange =
    A.relativeSpec.hom ⁻¹ᵁ U.toOpens from by
      congr 1
      exact Scheme.Opens.opensRange_ι U.toOpens]
  exact h

/-- The chart square is a pullback (`Spec_X A` restricted to `U` is `Spec A(U)`).
@isnad1 id=ispullba.0h3v.s5.2fa001e34428 from=translated src=- shape=65c3592a vocab=36045726
-/
theorem chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback (A.chartToOpen U) (A.chart U) U.toOpens.ι A.relativeSpec.hom :=
  A.gluingData.isPullback_natTrans_ι_toBase U

/-- The charts are jointly surjective.
@isnad1 id=ex.0h3v.s8.8ea039531f99 from=translated src=- shape=326c801a vocab=ab150389
-/
theorem exists_chart_mem (x : A.relativeSpec.left) :
    ∃ (U : X.AffineZariskiSite) (y : Spec (A.sections U)), A.chart U y = x :=
  Scheme.IsLocallyDirected.ι_jointly_surjective A.gluingData.functor x

/-- The structure morphism of the relative Spec is affine (half of Stacks 01LQ).
@isnad1 id=isaffine.0h2v.s4.a441c4962fed from=translated src=- shape=2073cbf8 vocab=4c0cfd7b
-/
instance relativeSpec_isAffineHom : IsAffineHom A.relativeSpec.hom := by
  refine isAffineHom_of_forall_exists_isAffineOpen _ fun x => ?_
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
  let V : X.AffineZariskiSite := ⟨U.1, U.2⟩
  refine ⟨V.toOpens, hU, V.2, ?_⟩
  rw [A.preimage_eq_opensRange V]
  exact isAffineOpen_opensRange (A.chart V)

/-! ## Algebra homomorphisms and functoriality -/

/-- A homomorphism of quasi-coherent algebras: a natural transformation of presheaves of rings compatible with
the structure maps.-/
@[ext] structure Hom (A B : X.AffineAlgebra) where
  app : A.ring ⟶ B.ring
  unit_app : A.unit ≫ app = B.unit

namespace Hom

variable {A} {B C : X.AffineAlgebra}

/-- The identity homomorphism.-/
@[simps] def id (A : X.AffineAlgebra) : Hom A A := ⟨𝟙 _, Category.comp_id _⟩

/-- Composition of homomorphisms.-/
@[simps] def comp (φ : Hom A B) (ψ : Hom B C) : Hom A C :=
  ⟨φ.app ≫ ψ.app, by rw [← Category.assoc, φ.unit_app, ψ.unit_app]⟩

/-- The component ring homomorphism `A(U) → B(U)`.-/
def appHom (φ : Hom A B) (U : X.AffineZariskiSite) : A.sections U →+* B.sections U :=
  (φ.app.app (op U)).hom

/--
@isnad1 id=eq.0h6v.s11.459cb3b94f94 from=translated src=- shape=698bf076 vocab=fab8ef72
-/
theorem appHom_unitHom (φ : Hom A B) (U : X.AffineZariskiSite) (r : Γ(X, U.toOpens)) :
    φ.appHom U (A.unitHom U r) = B.unitHom U r :=
  congrArg (fun α => (α.app (op U)).hom r) φ.unit_app

end Hom

instance : Category X.AffineAlgebra where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext (Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _)

/-- The natural transformation between charts `Spec B(U) → Spec A(U)` induced by an algebra homomorphism.-/
def specNatTrans {A B : X.AffineAlgebra} (φ : Hom A B) :
    B.gluingData.functor ⟶ A.gluingData.functor :=
  Functor.whiskerRight (NatTrans.rightOp φ.app) Scheme.Spec

/--
@isnad1 id=eq.0h5v.s8.a2c49a3c26a6 from=translated src=- shape=8f8a23b1 vocab=5fa7d815
-/
theorem specNatTrans_app {A B : X.AffineAlgebra} (φ : Hom A B) (U : X.AffineZariskiSite) :
    (specNatTrans φ).app U = Spec.map (φ.app.app (op U)) := rfl

/-- Functoriality (contravariant): an algebra homomorphism `A → B` gives a morphism `Spec_X B → Spec_X A` over
`X`.-/
def relativeSpec.map {A B : X.AffineAlgebra} (φ : Hom A B) :
    B.relativeSpec.left ⟶ A.relativeSpec.left :=
  colimMap (specNatTrans φ)

/--
@isnad1 id=eq.0h5v.s7.d81a26158b5e from=translated src=- shape=1d8ca22e vocab=d52f3079
-/
@[reassoc (attr := simp)]
theorem relativeSpec.chart_map {A B : X.AffineAlgebra} (φ : Hom A B) (U : X.AffineZariskiSite) :
    B.chart U ≫ relativeSpec.map φ = Spec.map (φ.app.app (op U)) ≫ A.chart U := by
  change colimit.ι B.gluingData.functor U ≫ colimMap (specNatTrans φ) =
    (specNatTrans φ).app U ≫ colimit.ι A.gluingData.functor U
  exact ι_colimMap _ _

/--
@isnad1 id=eq.0h5v.s9.898e86c72878 from=translated src=- shape=e0490a06 vocab=3dad7dac
-/
theorem spec_map_unit {A B : X.AffineAlgebra} (φ : Hom A B) (U : X.AffineZariskiSite) :
    Spec.map (φ.app.app (op U)) ≫ Spec.map (A.unit.app (op U)) = Spec.map (B.unit.app (op U)) := by
  rw [← Spec.map_comp]
  exact congrArg Spec.map (congrArg (fun α => α.app (op U)) φ.unit_app)

/--
@isnad1 id=eq.0h5v.s7.a54c486206f6 from=translated src=- shape=a7f98425 vocab=bb247f29
-/
theorem specMap_chartToOpen {A B : X.AffineAlgebra} (φ : Hom A B) (U : X.AffineZariskiSite) :
    Spec.map (φ.app.app (op U)) ≫ A.chartToOpen U = B.chartToOpen U := by
  unfold chartToOpen
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun g => g ≫ U.2.isoSpec.inv) (spec_map_unit φ U))

/-- `relativeSpec.map` is a morphism over `X`.
@isnad1 id=eq.0h4v.s6.0e9d8447741a from=translated src=- shape=f3f6fff0 vocab=7f93b503
-/
@[reassoc (attr := simp)]
theorem relativeSpec.map_hom {A B : X.AffineAlgebra} (φ : Hom A B) :
    relativeSpec.map φ ≫ A.relativeSpec.hom = B.relativeSpec.hom := by
  refine colimit.hom_ext fun (U : X.AffineZariskiSite) => ?_
  change B.chart U ≫ relativeSpec.map φ ≫ A.relativeSpec.hom = B.chart U ≫ B.relativeSpec.hom
  rw [relativeSpec.chart_map_assoc, chart_hom, chart_hom, ← Category.assoc,
    specMap_chartToOpen]

/-! ## The structure sheaf itself -/

/-- `O_X` as a quasi-coherent algebra; its `relativeSpec` is `X` (Mathlib `AffineZariskiSite.isColimitCocone`).-/
@[simps] def structureSheaf (X : Scheme.{u}) : X.AffineAlgebra where
  ring := (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf
  unit := 𝟙 _
  coequifibered := .of_isIso _

/-- Every quasi-coherent algebra lies under `O_X`.-/
@[simps] def unitHomAlg : Hom (structureSheaf X) A := ⟨A.unit, Category.id_comp _⟩

end AffineAlgebra

end AlgebraicGeometry.Scheme

end

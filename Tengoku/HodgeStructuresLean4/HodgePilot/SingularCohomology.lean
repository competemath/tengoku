import Tengoku.HodgeStructuresLean4.HodgePilot.Analytic
import Tengoku.Seed.AlgebraicTopology.SingularHomology.Basic
import Tengoku.Seed.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Tengoku.Seed.Algebra.Homology.Opposite
import Tengoku.Seed.Algebra.Category.ModuleCat.Abelian
import Tengoku.Seed.CategoryTheory.Linear.Yoneda

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Singular cohomology with rational coefficients as a functor

For a topological space `X`, singular *homology* with coefficients in a
preadditive category is already available in the pinned Mathlib as
`AlgebraicTopology.singularChainComplexFunctor` (with homotopy invariance).
Singular *cohomology* is not.  This file constructs it, at rational
coefficients, by `ℚ`-dualizing the singular chain complex:

* `dualFunctor` — the `ℚ`-linear dual `Hom(-, ℚ)` as a contravariant additive
  functor on `ModuleCat ℚ` (via `linearYoneda`).
* `singularCochainFunctor : TopCat.{0}ᵒᵖ ⥤ CochainComplex (ModuleCat ℚ) ℕ`
  — the singular cochain complex, obtained as
  `chains ⋙ op ⋙ HomologicalComplex.opFunctor ⋙ dualFunctor.mapHomologicalComplex`.
  (The reindexing is free: `(ComplexShape.down ℕ).symm = ComplexShape.up ℕ`
  definitionally, so op-ing a chain complex *is* a cochain complex.)
* `singularCohomologyFunctor n : TopCat.{0}ᵒᵖ ⥤ ModuleCat ℚ` — the `n`-th
  singular cohomology `Hⁿ(-, ℚ)`, a contravariant functor on topological
  spaces, with `singularCohomologyMap`/`_id`/`_comp` its functorial action.
* `cohomology_congr_of_homotopy` — **homotopy invariance**: homotopic
  continuous maps induce equal maps on cohomology (transported for free from
  the homotopy invariance of the chain complex).

Evaluated on the analytic point-spaces of `HodgePilot.Analytic`
(`CPoints A` for a commutative `ℂ`-algebra `A`), this yields
`analyticCohomology A n`, the singular cohomology `Hⁿ(CPoints A, ℚ)` of the
analytic space of `ℂ`-points, contravariantly functorial in `A`
(`analyticCohomologyMap`/`_id`/`_comp`) via `Analytic.comap`.

Coefficients are an *object* `ModuleCat ℚ`, so the additive / `ℚ`-linear
structure on cohomology is automatic.  No cup product (no ring structure), no
comparison with de Rham cohomology, no Hodge structure, and no
Eilenberg–Steenrod axioms are claimed or provided here; the point-space
version is affine only.  Everything is at universe `0` (forced by the `ℚ`
coefficient module: singular chains on `X : TopCat.{w}` are free on a
`Type w` basis, so `ModuleCat.{0} ℚ` coefficients require `TopCat.{0}`).
-/

open CategoryTheory AlgebraicTopology Opposite

noncomputable section

namespace HodgePilot.SingularCohomology

/-- Rational coefficients: the category of `ℚ`-modules at universe `0`.-/
abbrev QMod := ModuleCat.{0} ℚ

/-- The `ℚ`-linear dual, `Hom(-, ℚ)`, as a contravariant additive functor on
`ModuleCat ℚ`.-/
def dualFunctor : QModᵒᵖ ⥤ QMod := (linearYoneda ℚ QMod).obj (ModuleCat.of ℚ ℚ)

instance dualFunctor_additive : dualFunctor.Additive := by
  unfold dualFunctor
  infer_instance

/-- The singular **cochain** complex functor with `ℚ` coefficients:
`ℚ`-dualize the pinned singular chain complex.  Because
`(ComplexShape.down ℕ).symm = ComplexShape.up ℕ` definitionally, op-ing the
chain complex lands in `CochainComplex (ModuleCat ℚ) ℕ` with no reindexing.-/
def singularCochainFunctor : TopCat.{0}ᵒᵖ ⥤ CochainComplex QMod ℕ :=
  ((singularChainComplexFunctor QMod).obj (ModuleCat.of ℚ ℚ)).op ⋙
    HomologicalComplex.opFunctor _ _ ⋙
    dualFunctor.mapHomologicalComplex ((ComplexShape.down ℕ).symm)

/-- Singular cohomology `Hⁿ(-, ℚ)` as a contravariant functor on topological
spaces.-/
def singularCohomologyFunctor (n : ℕ) : TopCat.{0}ᵒᵖ ⥤ QMod :=
  singularCochainFunctor ⋙
    HomologicalComplex.homologyFunctor QMod ((ComplexShape.down ℕ).symm) n

/-- The cochain shape is the cochain (ascending) shape: op-ing a chain complex
is a cochain complex, definitionally (no reindexing layer).-/
theorem cochainShape_eq : (ComplexShape.down ℕ).symm = ComplexShape.up ℕ := rfl

/-- **Homotopy invariance of singular cohomology**: homotopic continuous maps
`f, g : X ⟶ Y` induce equal maps on `Hⁿ(-, ℚ)`.  Transported for free from the
homotopy invariance of the singular chain complex.-/
theorem cohomology_congr_of_homotopy {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (n : ℕ) :
    (singularCohomologyFunctor n).map f.op = (singularCohomologyFunctor n).map g.op := by
  have hchain := H.singularChainComplexFunctorObjMap (ModuleCat.of ℚ ℚ)
  have h2 : Homotopy (singularCochainFunctor.map f.op) (singularCochainFunctor.map g.op) :=
    dualFunctor.mapHomotopy hchain.op
  exact h2.homologyMap_eq n

/-! ### Functorial action on maps (naturality package) -/

/-- The contravariant action of singular cohomology on a continuous map:
`h : X ⟶ Y` induces `Hⁿ(Y, ℚ) ⟶ Hⁿ(X, ℚ)`.-/
def singularCohomologyMap (n : ℕ) {X Y : TopCat.{0}} (h : X ⟶ Y) :
    (singularCohomologyFunctor n).obj (op Y) ⟶ (singularCohomologyFunctor n).obj (op X) :=
  (singularCohomologyFunctor n).map h.op

@[simp]
theorem singularCohomologyMap_id (n : ℕ) (X : TopCat.{0}) :
    singularCohomologyMap n (𝟙 X) = 𝟙 ((singularCohomologyFunctor n).obj (op X)) := by
  simp [singularCohomologyMap]

theorem singularCohomologyMap_comp (n : ℕ) {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    singularCohomologyMap n (f ≫ g) = singularCohomologyMap n g ≫ singularCohomologyMap n f := by
  simp [singularCohomologyMap, op_comp]

/-! ### Singular cohomology of the analytic space of `ℂ`-points

Evaluating on the analytic point-spaces of `HodgePilot.Analytic` (universe `0`,
as `singularCohomologyFunctor` demands). -/

section Analytic

open HodgePilot.Analytic

variable (A : Type) [CommRing A] [Algebra ℂ A]

/-- The analytic space of `ℂ`-points of `Spec A` as an object of `TopCat.{0}`.-/
abbrev analyticSpace : TopCat.{0} := TopCat.of (CPoints A)

/-- The singular cohomology `Hⁿ(CPoints A, ℚ)` of the analytic space of
`ℂ`-points of an affine `ℂ`-algebra `A`.-/
def analyticCohomology (n : ℕ) : QMod :=
  (singularCohomologyFunctor n).obj (op (analyticSpace A))

variable {A}

/-- An algebra map `A →ₐ[ℂ] B` as a (continuous) morphism of analytic
point-spaces `CPoints B ⟶ CPoints A` in `TopCat`.-/
def comapC {B : Type} [CommRing B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) :
    analyticSpace B ⟶ analyticSpace A :=
  TopCat.ofHom ⟨comap f, continuous_comap f⟩

/-- Contravariant functoriality of analytic cohomology in the algebra: an
algebra map `A →ₐ[ℂ] B` induces `Hⁿ(CPoints A, ℚ) ⟶ Hⁿ(CPoints B, ℚ)`.-/
def analyticCohomologyMap {B : Type} [CommRing B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) (n : ℕ) :
    analyticCohomology A n ⟶ analyticCohomology B n :=
  singularCohomologyMap n (comapC f)

@[simp]
theorem comapC_id : comapC (AlgHom.id ℂ A) = 𝟙 (analyticSpace A) := rfl

theorem comapC_comp {B : Type} [CommRing B] [Algebra ℂ B]
    {C : Type} [CommRing C] [Algebra ℂ C] (f : A →ₐ[ℂ] B) (g : B →ₐ[ℂ] C) :
    comapC (g.comp f) = comapC g ≫ comapC f := rfl

@[simp]
theorem analyticCohomologyMap_id (n : ℕ) :
    analyticCohomologyMap (AlgHom.id ℂ A) n = 𝟙 (analyticCohomology A n) :=
  (congrArg (singularCohomologyMap n) comapC_id).trans (singularCohomologyMap_id n (analyticSpace A))

theorem analyticCohomologyMap_comp {B : Type} [CommRing B] [Algebra ℂ B]
    {C : Type} [CommRing C] [Algebra ℂ C] (f : A →ₐ[ℂ] B) (g : B →ₐ[ℂ] C) (n : ℕ) :
    analyticCohomologyMap (g.comp f) n
      = analyticCohomologyMap f n ≫ analyticCohomologyMap g n :=
  (congrArg (singularCohomologyMap n) (comapC_comp f g)).trans
    (singularCohomologyMap_comp n (comapC g) (comapC f))

end Analytic

end HodgePilot.SingularCohomology

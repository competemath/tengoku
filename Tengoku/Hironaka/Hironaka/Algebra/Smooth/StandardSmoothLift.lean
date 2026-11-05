/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Seed.RingTheory.Smooth.StandardSmooth
public import Tengoku.Seed.Algebra.Category.Ring.Basic
public import Tengoku.Seed.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Tengoku.Seed.Algebra.Category.Ring.Constructions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The standard-smooth lift of a presentation along a closed embedding

The algebraic core of Kollár's Lemma 41 ([Kol07, Lemma 41]). Kollár writes `Y` near `y` as an open
of a hypersurface `H ⊂ X × 𝔸^{d+1}` after a general projection, extends the coefficients `φ_I` of
its equation to `Φ_I` on the ambient `A_X` and sets `A_Y := (Σ Φ_I z^I = 0) ⊂ A_X × 𝔸^{d+1}`,
smooth over `A_X` at `y`. Here the general projection is replaced by Mathlib's local structure of
smooth algebras: `S` (the ring of `Y` near `y`) has a submersive presentation `P` over `R` (the
ring of `X`), `S = R[ι]/(f_r)` with an invertible Jacobian. Fix a surjective `R' → R` (the ring of
`A_X` onto the ring of `X`).

* `liftRelation`, `LiftedQuot`: the relations `f_r` lifted coefficientwise to `F_r ∈ R'[ι]`
  (Kollár's `Φ_I`), and `T := R'[ι]/(F)`; `liftedPre`, `liftedJac`: the same variables give a
  pre-submersive presentation of `T` with Jacobian `Δ` lifting `P`'s.
* `Ambient := T[1/Δ]`, `ambientPres`, `isStandardSmooth_ambient`,
  `isStandardSmoothOfRelativeDimension_ambient`: the basic open `D(Δ)` (Kollár's `A⁰_Y`, on which
  the projection is smooth) is standard smooth of relative dimension `P.dimension` over `R'` (the
  localisation adds one variable and one relation; `comp_jacobian_eq_jacobian_smul_jacobian`).
* `baseChangeEquiv : R ⊗[R'] T ≃ₐ[R] S`, `isPushout_liftedQuot`: the base change of `T` along
  `R' → R` is `S`, the fibre square of the lemma at the level of rings, through
  `Presentation.baseChange` (the base-changed relations are `P`'s) and `Presentation.quotientEquiv`.
* `baseChangeEquiv_one_tmul_liftedJac`, `ambientToS`, `ambientToS_surjective`: `Δ` maps to `P`'s
  Jacobian, a unit of `S`, so `T → S` extends to `T[1/Δ] → S`, surjective (as `R' → R` is):
  `Spec S ↪ D(Δ)` is Kollár's closed embedding `j`.

The scheme-level assembly (the charts, the `Spec` square, the shrinking to a surjective `h_A`) is
`Hironaka/Scheme/Smooth/SmoothAmbientLift.lean`. Compare [Wlo05, Lemma 4.9.1], the extension of an
étale morphism of embedded affine varieties to the ambient spaces.
-/

@[expose] public section

open Algebra MvPolynomial _root_.TensorProduct

namespace Algebra.StandardSmoothLift

universe u

variable {R' R S : Type u} [CommRing R'] [CommRing R] [CommRing S] [Algebra R' R] [Algebra R S]
variable {ι σ : Type} [Finite σ]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Lift

variable (hφ : Function.Surjective (algebraMap R' R)) (P : SubmersivePresentation R S ι σ)

/-- A lift of the relation `P.relation r ∈ R[ι]` to `R'[ι]` along the coefficientwise surjection
`MvPolynomial.map (algebraMap R' R)` (`Function.surjInv`): the coefficients `φ_I` of the equations
of `Y` extended to `Φ_I` on `A_X` in the proof of [Kol07, Lemma 41].-/
noncomputable def liftRelation (r : σ) : MvPolynomial ι R' :=
  Function.surjInv (MvPolynomial.map_surjective (algebraMap R' R) hφ) (P.relation r)

/-- The lifted relation maps back to `P.relation r`.
@isnad1 id=eq.1h7v.s8.d7f4ef62615a from=translated src=- shape=cb6f91f1 vocab=9867d266
-/
theorem map_liftRelation (r : σ) :
    MvPolynomial.map (algebraMap R' R) (liftRelation hφ P r) = P.relation r :=
  Function.surjInv_eq (MvPolynomial.map_surjective (algebraMap R' R) hφ) _

/-- The lifted quotient `T := R'[ι]/(F_r)`: Kollár's `A_Y` as an algebra over `Γ(A_X)`, before
localising, with the standard-smooth equations in place of his single hypersurface equation
([Kol07, Lemma 41], the proof).-/
abbrev LiftedQuot : Type u :=
  MvPolynomial ι R' ⧸ Ideal.span (Set.range (liftRelation hφ P))

/-- The naive pre-submersive presentation of `T` with `P`'s choice of variables
(`PreSubmersivePresentation.naive`); its Jacobian is the lift of `P`'s.-/
noncomputable def liftedPre : PreSubmersivePresentation R' (LiftedQuot hφ P) ι σ :=
  PreSubmersivePresentation.naive (v := liftRelation hφ P) P.map P.map_inj

/-- The lifted Jacobian determinant `Δ ∈ T`, which cuts out the smooth locus of `A_Y → A_X`.-/
noncomputable def liftedJac : LiftedQuot hφ P := (liftedPre hφ P).jacobian

/-- The lifted quotient localised at the lifted Jacobian, `T[1/Δ]`, i.e. the basic open `D(Δ)` of
`Spec T` on which the Jacobian is a unit: Kollár's open `A⁰_Y` on which "the projection
`A_Y → A_X` is smooth" ([Kol07, Lemma 41], the proof).-/
abbrev Ambient : Type u := Localization.Away (liftedJac hφ P)

/-- The pre-submersive presentation of the ambient over `R'`: the localisation presentation (one
variable `w`, one relation `w·Δ − 1`) composed with the lifted one
(`PreSubmersivePresentation.comp`).-/
noncomputable def ambientPre :
    PreSubmersivePresentation R' (Ambient hφ P) (Unit ⊕ ι) (Unit ⊕ σ) :=
  (PreSubmersivePresentation.localizationAway (Ambient hφ P) (liftedJac hφ P)).comp
    (liftedPre hφ P)

/-- The composite presentation's Jacobian is the unit `Δ · Δ` of `T[1/Δ]`.
@isnad1 id=isunit.1h6v.s10.9a504b2c99df from=translated src=- shape=b9cc0c9b vocab=97260c0b
-/
theorem isUnit_jacobian_ambientPre : IsUnit (ambientPre hφ P).jacobian := by
  unfold ambientPre
  rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    PreSubmersivePresentation.localizationAway_jacobian]
  have hu : IsUnit (algebraMap (LiftedQuot hφ P) (Ambient hφ P) (liftedJac hφ P)) :=
    IsLocalization.Away.algebraMap_isUnit (liftedJac hφ P)
  rw [Algebra.smul_def]
  exact hu.mul hu

/-- The submersive presentation of the ambient over `R'`.-/
noncomputable def ambientPres : SubmersivePresentation R' (Ambient hφ P) (Unit ⊕ ι) (Unit ⊕ σ) where
  __ := ambientPre hφ P
  jacobian_isUnit := isUnit_jacobian_ambientPre hφ P

/-- The ambient `T[1/Δ]` is standard smooth over `R'`: `h_A` is smooth.
@isnad1 id=isstanda.1h6v.s10.df17857b0774 from=translated src=- shape=0c50ca4e vocab=e2e431c9
-/
theorem isStandardSmooth_ambient [Finite ι] : IsStandardSmooth R' (Ambient hφ P) :=
  (ambientPres hφ P).isStandardSmooth

/-! ### The base change of the lifted quotient is `S` -/

/-- The base change of the lifted presentation along `R' → R`, a presentation of `R ⊗[R'] T` over
`R`.-/
noncomputable def liftedBase : Presentation R (R ⊗[R'] LiftedQuot hφ P) ι σ :=
  (liftedPre hφ P).toPresentation.baseChange R

/-- The base-changed relations are `P`'s.
@isnad1 id=eq.1h7v.s11.e2bbdde6a28b from=translated src=- shape=bcf64c95 vocab=40af75b1
-/
theorem liftedBase_relation (r : σ) : (liftedBase hφ P).relation r = P.relation r := by
  unfold liftedBase
  rw [Presentation.baseChange_relation]
  exact map_liftRelation hφ P r

/-- The base-changed presentation has `P`'s kernel.
@isnad1 id=eq.1h6v.s11.72763dfd02fb from=translated src=- shape=d1c65c90 vocab=e988d4d2
-/
theorem liftedBase_ker : (liftedBase hφ P).ker = P.ker := by
  rw [← (liftedBase hφ P).span_range_relation_eq_ker, ← P.span_range_relation_eq_ker]
  congr 1
  ext x
  simp only [Set.mem_range, liftedBase_relation]

/-- `R ⊗[R'] R'[ι]/(F) ≃ R[ι]/(P.relation) ≃ S`: the fibre square of [Kol07, Lemma 41] at the level
of rings, before localising.-/
noncomputable def baseChangeEquiv : (R ⊗[R'] LiftedQuot hφ P) ≃ₐ[R] S :=
  ((liftedBase hφ P).quotientEquiv.symm.restrictScalars R).trans
    (((Ideal.quotientEquivAlgOfEq R (liftedBase_ker hφ P)).trans
      (P.quotientEquiv.restrictScalars R)))

/-! ### The relative dimension and the image of the lifted Jacobian -/

/-- The ambient's presentation has `P`'s dimension (the localisation adds one variable and one
relation): Kollár's relative dimension `d`.
@isnad1 id=eq.1h6v.s11.256d21acaada from=translated src=- shape=d8108388 vocab=71e4b697
-/
theorem dimension_ambientPre [Finite ι] : (ambientPre hφ P).dimension = P.dimension := by
  unfold ambientPre
  rw [PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
  simp [Presentation.dimension]

/-- The ambient is standard smooth of relative dimension `P.dimension` over `R'`: the constant
relative dimension of `h_A`.
@isnad1 id=isstanda.1h6v.s10.f8f4f999846c from=translated src=- shape=e213684c vocab=9780c975
-/
theorem isStandardSmoothOfRelativeDimension_ambient [Finite ι] :
    IsStandardSmoothOfRelativeDimension P.dimension R' (Ambient hφ P) :=
  (ambientPres hφ P).isStandardSmoothOfRelativeDimension (dimension_ambientPre hφ P)

/-- Under the base change, the class of a lifted polynomial `q` goes to `q` evaluated at `P`'s
generators.
@isnad1 id=eq.1h7v.s11.95130fdc424a from=translated src=- shape=f17f9205 vocab=87f3df27
-/
theorem baseChangeEquiv_one_tmul_mk (q : MvPolynomial ι R') :
    baseChangeEquiv hφ P (1 ⊗ₜ[R'] (algebraMap (MvPolynomial ι R') (LiftedQuot hφ P) q)) =
      aeval P.val (MvPolynomial.map (algebraMap R' R) q) := by
  have hval : (liftedBase hφ P).val =
      ⇑(Algebra.TensorProduct.includeRight (R := R') (A := R) (B := LiftedQuot hφ P)) ∘
        (liftedPre hφ P).val := by
    funext i
    rfl
  have hcomp : aeval (⇑(Algebra.TensorProduct.includeRight (R := R') (A := R)
      (B := LiftedQuot hφ P)) ∘ (liftedPre hφ P).val) q =
      Algebra.TensorProduct.includeRight (aeval (liftedPre hφ P).val q) := by
    induction q using MvPolynomial.induction_on with
    | C r =>
      simp only [MvPolynomial.aeval_C, Algebra.TensorProduct.includeRight_apply]
      rw [Algebra.TensorProduct.algebraMap_apply, ← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.aeval_X, map_mul]
      rfl
  have h1 : (liftedBase hφ P).quotientEquiv
      (Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R' R) q)) =
      1 ⊗ₜ[R'] (algebraMap (MvPolynomial ι R') (LiftedQuot hφ P) q) := by
    rw [Presentation.quotientEquiv_mk, Generators.algebraMap_apply, hval,
      MvPolynomial.aeval_map_algebraMap, hcomp, ← Generators.algebraMap_apply,
      Algebra.TensorProduct.includeRight_apply]
    rfl
  unfold baseChangeEquiv
  simp only [AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply]
  rw [← h1, AlgEquiv.symm_apply_apply, Ideal.quotientEquivAlgOfEq_mk,
    Presentation.quotientEquiv_mk, Generators.algebraMap_apply]

/-- The lifted Jacobian maps to `P`'s Jacobian under the base change, a unit of `S`, so `Spec S`
lies in `D(Δ)`.
@isnad1 id=eq.1h6v.s11.acc630504fe3 from=translated src=- shape=3a80d739 vocab=697c7809
-/
theorem baseChangeEquiv_one_tmul_liftedJac :
    baseChangeEquiv hφ P (1 ⊗ₜ[R'] liftedJac hφ P) = P.jacobian := by
  classical
  have : Fintype σ := Fintype.ofFinite σ
  have key := baseChangeEquiv_one_tmul_mk hφ P (liftedPre hφ P).jacobiMatrix.det
  unfold liftedJac
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  refine key.trans ?_
  rw [P.jacobian_eq_jacobiMatrix_det, Generators.algebraMap_apply]
  congr 1
  rw [RingHom.map_det]
  refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, PreSubmersivePresentation.jacobiMatrix_apply,
    PreSubmersivePresentation.jacobiMatrix_apply, ← MvPolynomial.pderiv_map]
  change pderiv (P.map i) (MvPolynomial.map (algebraMap R' R) (liftRelation hφ P j)) =
    pderiv (P.map i) (P.relation j)
  rw [map_liftRelation]

/-! ### The pushout: `S` is the base change of the lifted quotient -/

variable [Algebra R' S] [IsScalarTower R' R S]

/-- The algebra map `T → S` through the base change, `t ↦ e (1 ⊗ t)`: Kollár's closed embedding
`Y ⊂ A_Y` at the level of rings, before localising.-/
noncomputable def liftedToS : LiftedQuot hφ P →ₐ[R'] S :=
  ((baseChangeEquiv hφ P).toAlgHom.restrictScalars R').comp
    (Algebra.TensorProduct.includeRight (R := R') (A := R) (B := LiftedQuot hφ P))

/-- The defining formula of `liftedToS`.
@isnad1 id=eq.1h7v.s11.14d7ecb84b83 from=translated src=- shape=db115095 vocab=d0b72ee2
-/
theorem liftedToS_apply (t : LiftedQuot hφ P) :
    liftedToS hφ P t = baseChangeEquiv hφ P (1 ⊗ₜ[R'] t) := rfl

/-- `liftedToS` is a map of `R'`-algebras.
@isnad1 id=eq.1h7v.s10.3ef38fac7b95 from=translated src=- shape=ba8bbd53 vocab=4ec99a27
-/
theorem liftedToS_algebraMap (r : R') :
    liftedToS hφ P (algebraMap R' (LiftedQuot hφ P) r) = algebraMap R' S r := by
  rw [liftedToS, AlgHom.comp_apply, AlgHom.commutes, AlgHom.commutes]

/-- The pushout square in `CommRingCat`: `S` is the base change of the lifted quotient along
`R' → R`, so `Spec S = Spec R ×_{Spec R'} Spec T` (`isPullback_SpecMap_of_isPushout`).
@isnad1 id=ispushou.1h6v.s9.18ee11a21997 from=translated src=- shape=7209372d vocab=d3eaa125
-/
theorem isPushout_liftedQuot :
    CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap R' R))
      (CommRingCat.ofHom (algebraMap R' (LiftedQuot hφ P)))
      (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (liftedToS hφ P).toRingHom) := by
  let : Algebra (LiftedQuot hφ P) S := (liftedToS hφ P).toRingHom.toAlgebra
  have : IsScalarTower R' (LiftedQuot hφ P) S :=
    IsScalarTower.of_algebraMap_eq fun r => (liftedToS_algebraMap hφ P r).symm
  have h : Algebra.IsPushout R' R (LiftedQuot hφ P) S :=
    Algebra.IsPushout.of_equiv (S' := R ⊗[R'] LiftedQuot hφ P) (baseChangeEquiv hφ P)
      (RingHom.ext fun t => by
        simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
        rfl)
  exact CommRingCat.isPushout_iff_isPushout.mpr h

/-! ### The ambient localised at the Jacobian maps onto `S` -/

/-- The lifted Jacobian is a unit in `S`.
@isnad1 id=isunit.1h6v.s9.afb2ca2aae43 from=translated src=- shape=82ddaebb vocab=b73ab9bb
-/
theorem isUnit_liftedToS_liftedJac : IsUnit (liftedToS hφ P (liftedJac hφ P)) := by
  rw [liftedToS_apply, baseChangeEquiv_one_tmul_liftedJac]
  exact P.jacobian_isUnit

/-- The ring map `T[1/Δ] → S` extending `liftedToS`: the closed embedding `j : Y⁰ ↪ A⁰_Y` of
[Kol07, Lemma 41] at the level of rings.-/
noncomputable def ambientToS : Ambient hφ P →+* S :=
  IsLocalization.Away.lift (g := (liftedToS hφ P).toRingHom) (liftedJac hφ P)
    (isUnit_liftedToS_liftedJac hφ P)

/-- `ambientToS` extends `liftedToS`.
@isnad1 id=eq.1h6v.s11.b8b0b7a7023c from=translated src=- shape=caa67081 vocab=d55f51e0
-/
theorem ambientToS_comp_algebraMap :
    (ambientToS hφ P).comp (algebraMap (LiftedQuot hφ P) (Ambient hφ P)) =
      (liftedToS hφ P).toRingHom :=
  IsLocalization.Away.lift_comp _ _

/-- `ambientToS` on the image of `T`.
@isnad1 id=eq.1h7v.s11.e0ab6d392e20 from=translated src=- shape=829757ac vocab=35e443ae
-/
theorem ambientToS_algebraMap (t : LiftedQuot hφ P) :
    ambientToS hφ P (algebraMap (LiftedQuot hφ P) (Ambient hφ P) t) = liftedToS hφ P t :=
  IsLocalization.Away.lift_eq _ _ _

end Lift

end Algebra.StandardSmoothLift

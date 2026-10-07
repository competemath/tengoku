/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Algebra.Pi
public import Tengoku.Seed.Algebra.Algebra.Shrink
public import Tengoku.Seed.Algebra.Category.AlgCat.Basic
public import Tengoku.Seed.Algebra.Category.ModuleCat.Basic
public import Tengoku.Seed.Algebra.Category.ModuleCat.Limits
public import Tengoku.Seed.Algebra.Category.Ring.Limits

/-!
# The category of R-algebras has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section


open CategoryTheory Limits

universe v w u t

-- `u` is determined by the ring, so can come later
noncomputable section

namespace AlgCat

variable {R : Type u} [CommRing R]
variable {J : Type v} [Category.{t} J] (F : J ⥤ AlgCat.{w} R)

instance semiringObj (j) : Semiring ((F ⋙ forget (AlgCat R)).obj j) :=
  inferInstanceAs <| Semiring (F.obj j)

instance algebraObj (j) :
    Algebra R ((F ⋙ forget (AlgCat R)).obj j) :=
  inferInstanceAs <| Algebra R (F.obj j)

/-- The flat sections of a functor into `AlgCat R` form a submodule of all sections.
-/
def sectionsSubalgebra : Subalgebra R (∀ j, F.obj j) :=
  { SemiRingCat.sectionsSubsemiring
      (F ⋙ forget₂ (AlgCat R) RingCat.{w} ⋙ forget₂ RingCat SemiRingCat.{w}) with
    algebraMap_mem' := fun r _ _ f => (F.map f).hom.commutes r }

instance (F : J ⥤ AlgCat.{w} R) : Ring (F ⋙ forget _).sections :=
  inferInstanceAs <| Ring (sectionsSubalgebra F)

instance (F : J ⥤ AlgCat.{w} R) : Algebra R (F ⋙ forget _).sections :=
  inferInstanceAs <| Algebra R (sectionsSubalgebra F)

variable [Small.{w} (F ⋙ forget (AlgCat.{w} R)).sections]

instance : Small.{w} (sectionsSubalgebra F) :=
  inferInstanceAs <| Small.{w} (F ⋙ forget _).sections

instance limitSemiring :
    Ring.{w} (Types.Small.limitCone.{v, w} (F ⋙ forget (AlgCat.{w} R))).pt :=
  inferInstanceAs <| Ring (Shrink (sectionsSubalgebra F))

instance limitAlgebra :
    Algebra R (Types.Small.limitCone (F ⋙ forget (AlgCat.{w} R))).pt :=
  inferInstanceAs <| Algebra R (Shrink (sectionsSubalgebra F))

set_option backward.isDefEq.respectTransparency false in
/-- `limit.π (F ⋙ forget (AlgCat R)) j` as an `AlgHom`. -/
def limitπAlgHom (j) :
    (Types.Small.limitCone (F ⋙ forget (AlgCat R))).pt →ₐ[R]
      (F ⋙ forget (AlgCat.{w} R)).obj j :=
  letI : Small.{w}
      (Functor.sections ((F ⋙ forget₂ _ RingCat ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{w} (F ⋙ forget _).sections
  { SemiRingCat.limitπRingHom
      (F ⋙ forget₂ (AlgCat R) RingCat.{w} ⋙ forget₂ RingCat SemiRingCat.{w}) j with
    toFun := (Types.Small.limitCone (F ⋙ forget (AlgCat.{w} R))).π.app j
    commutes' := fun x => by
      simp only [Functor.comp_obj, Types.Small.limitCone_pt, Functor.const_obj_obj,
        Types.Small.limitCone_π_app, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk,
        ← Shrink.algEquiv_apply R, AlgEquiv.commutes]
      rfl
    }

namespace HasLimits

-- The next two definitions are used in the construction of `HasLimits (AlgCat R)`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.isLimit F`.
/-- Construction of a limit cone in `AlgCat R`.
(Internal use only; use the limits API.)
-/
def limitCone : Cone F where
  pt := AlgCat.of R (Types.Small.limitCone (F ⋙ forget _)).pt
  π :=
    { app := fun j ↦ ofHom <| limitπAlgHom F j
      naturality := fun _ _ f => by
        ext
        simpa using! (Types.Small.limitCone (F ⋙ forget _)).π.naturality_apply f _ }

set_option backward.isDefEq.respectTransparency false in
/-- Witness that the limit cone in `AlgCat R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limitConeIsLimit : IsLimit (limitCone.{v, w} F) := by
  refine
    IsLimit.ofFaithful (forget (AlgCat R)) (Types.Small.limitConeIsLimit.{v, w} _)
      (fun s => ofHom
        { toFun := _, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_,
          commutes' := ?_ })
      (fun s => rfl)
  · congr
    ext j
    simp
  · intro x y
    ext j
    simp
    rfl
  · ext j
    simp
    rfl
  · intro x y
    ext j
    simp
    rfl
  · intro r
    simp only [Equiv.algebraMap_def, Equiv.symm_symm]
    apply congrArg
    apply Subtype.ext
    ext j
    exact (s.π.app j).hom.commutes r

end HasLimits

open HasLimits

/-- The category of R-algebras has all limits.
@isnad1 id=haslimit.0h1v.s3.fa6e2c9b79cd from=seed src=0 shape=2fe8c59c vocab=65cba84a
-/
lemma hasLimitsOfSize [UnivLE.{v, w}] : HasLimitsOfSize.{t, v} (AlgCat.{w} R) :=
  { has_limits_of_shape := fun _ _ =>
    { has_limit := fun F => HasLimit.mk
        { cone := limitCone F
          isLimit := limitConeIsLimit F } } }

/--
@isnad1 id=haslimit.0h1v.s3.f9a4a6438732 from=seed src=0 shape=1666ae32 vocab=51aabb4e
-/
instance hasLimits : HasLimits (AlgCat.{w} R) :=
  AlgCat.hasLimitsOfSize.{w, w, u}

/-- The forgetful functor from R-algebras to rings preserves all limits.
@isnad1 id=preserve.0h1v.s7.63875fd12587 from=seed src=0 shape=7e8c778d vocab=27be6d6e
-/
instance forget₂Ring_preservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v} (forget₂ (AlgCat.{w} R) RingCat.{w}) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} ↦
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (RingCat.limitConeIsLimit.{v, w}
            (_ ⋙ forget₂ (AlgCat.{w} R) RingCat.{w})) }

/--
@isnad1 id=preserve.0h1v.s7.377fd4106ca7 from=seed src=0 shape=9beb2f11 vocab=70cdc257
-/
instance forget₂Ring_preservesLimits : PreservesLimits (forget₂ (AlgCat R) RingCat.{w}) :=
  AlgCat.forget₂Ring_preservesLimitsOfSize.{w, w}

/-- The forgetful functor from R-algebras to R-modules preserves all limits.
@isnad1 id=preserve.0h1v.s8.58035ac321ad from=seed src=0 shape=5f42f27c vocab=39c76324
-/
instance forget₂Module_preservesLimitsOfSize [UnivLE.{v, w}] : PreservesLimitsOfSize.{t, v}
    (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} ↦
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (ModuleCat.HasLimits.limitConeIsLimit
            (K ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) }

/--
@isnad1 id=preserve.0h1v.s8.37f2ef25bd37 from=seed src=0 shape=85022f7f vocab=43ab1ebf
-/
instance forget₂Module_preservesLimits :
    PreservesLimits (forget₂ (AlgCat R) (ModuleCat.{w} R)) :=
  AlgCat.forget₂Module_preservesLimitsOfSize.{w, w}

/-- The forgetful functor from R-algebras to types preserves all limits.
@isnad1 id=preserve.0h1v.s6.7eb82d3b44bd from=seed src=0 shape=9aef521b vocab=51da5823
-/
instance forget_preservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v} (forget (AlgCat.{w} R)) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} ↦
       preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (Types.Small.limitConeIsLimit.{v} (K ⋙ forget _)) }

/--
@isnad1 id=preserve.0h1v.s6.9e6fa10e30d3 from=seed src=0 shape=2740f13a vocab=bf9d1590
-/
instance forget_preservesLimits : PreservesLimits (forget (AlgCat.{w} R)) :=
  AlgCat.forget_preservesLimitsOfSize.{w, w}

end AlgCat

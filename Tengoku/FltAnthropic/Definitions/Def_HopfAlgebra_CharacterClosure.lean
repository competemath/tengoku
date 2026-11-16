import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.Definitions.Def_FiniteFlat_SchematicClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

open scoped TensorProduct

namespace HopfAlgebra

section FieldLevel

variable {F : Type*} [CommRing F] {A : Type*} [CommRing A] [Algebra F A]
variable {L : Type*} [CommRing L] [Algebra F L]

def vanishingIdealOfPoints (S : Set (A →ₐ[F] L)) : Ideal A where
  carrier := {a | ∀ ν ∈ S, ν a = 0}
  add_mem' {a b} ha hb := fun ν hν => by rw [map_add, ha ν hν, hb ν hν, add_zero]
  zero_mem' := fun ν _ => map_zero ν
  smul_mem' c {a} ha := fun ν hν => by rw [smul_eq_mul, map_mul, ha ν hν, mul_zero]

/--
@isnad1 id=iff.0h5v.s8.faed76bbaa4b from=translated src=- shape=a906e42e vocab=563f1bcd
-/
@[simp] theorem mem_vanishingIdealOfPoints_iff (S : Set (A →ₐ[F] L)) (a : A) :
    a ∈ vanishingIdealOfPoints S ↔ ∀ ν ∈ S, ν a = 0 := Iff.rfl

/--
@isnad1 id=le.1h5v.s7.833b017a8e3e from=translated src=- shape=42591816 vocab=d86c62e4
-/
theorem vanishingIdealOfPoints_antitone {S T : Set (A →ₐ[F] L)} (h : S ⊆ T) :
    vanishingIdealOfPoints T ≤ vanishingIdealOfPoints S := fun _ ha ν hν => ha ν (h hν)

def liftPoint (S : Set (A →ₐ[F] L)) (ν : A →ₐ[F] L) (hν : ν ∈ S) :
    (A ⧸ vanishingIdealOfPoints S) →ₐ[F] L :=
  Ideal.Quotient.liftₐ (vanishingIdealOfPoints S) ν (fun a ha => ha ν hν)

/--
@isnad1 id=eq.1h6v.s9.43808d800c69 from=translated src=- shape=e989fb02 vocab=3258f7d5
-/
@[simp] theorem liftPoint_mk (S : Set (A →ₐ[F] L)) (ν : A →ₐ[F] L) (hν : ν ∈ S) (a : A) :
    liftPoint S ν hν (Ideal.Quotient.mk (vanishingIdealOfPoints S) a) = ν a := rfl

noncomputable def evalPair (S : Set (A →ₐ[F] L)) (ν ν' : A →ₐ[F] L) (hν : ν ∈ S) (hν' : ν' ∈ S) :
    (A ⧸ vanishingIdealOfPoints S) ⊗[F] (A ⧸ vanishingIdealOfPoints S) →ₐ[F] L :=
  (Algebra.TensorProduct.lmul' F (S := L)).comp
    (Algebra.TensorProduct.map (liftPoint S ν hν) (liftPoint S ν' hν'))

/--
@isnad1 id=eq.2h8v.s11.a82ef91683af from=translated src=- shape=5382b1c5 vocab=21c042e3
-/
theorem evalPair_tmul (S : Set (A →ₐ[F] L)) (ν ν' : A →ₐ[F] L) (hν : ν ∈ S) (hν' : ν' ∈ S) (a b : A) :
    evalPair S ν ν' hν hν' (Ideal.Quotient.mk _ a ⊗ₜ[F] Ideal.Quotient.mk _ b) = ν a * ν' b := by
  simp only [evalPair, AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.map_tmul, liftPoint_mk,
    Algebra.TensorProduct.lmul'_apply_tmul]

end FieldLevel

section PointMonoid

variable {F : Type*} [CommRing F] {A : Type*} [CommRing A] [Bialgebra F A]
variable {L : Type*} [CommRing L] [Algebra F L]

def ptSet (S : Submonoid (WithConv (A →ₐ[F] L))) : Set (A →ₐ[F] L) := {ν | WithConv.toConv ν ∈ S}

/--
@isnad1 id=iff.0h5v.s9.3e414eaaea86 from=translated src=- shape=3b921e5d vocab=435603a5
-/
@[simp] theorem mem_ptSet_iff (S : Submonoid (WithConv (A →ₐ[F] L))) (ν : A →ₐ[F] L) :
    ν ∈ ptSet S ↔ WithConv.toConv ν ∈ S := Iff.rfl

/--
@isnad1 id=mem.0h5v.s9.89ee69444ba8 from=translated src=- shape=cd19ecb2 vocab=63bc8390
-/
theorem ofConv_mem_ptSet {S : Submonoid (WithConv (A →ₐ[F] L))} (ν : ↥S) : WithConv.ofConv ν.1 ∈ ptSet S := by
  show WithConv.toConv (WithConv.ofConv ν.1) ∈ S
  exact ν.2

/--
@isnad1 id=le.1h5v.s9.b3a9fdbccf10 from=translated src=- shape=92342ec9 vocab=94d0cfa5
-/
theorem ptSet_mono {S T : Submonoid (WithConv (A →ₐ[F] L))} (h : S ≤ T) : ptSet S ⊆ ptSet T :=
  fun _ hν => h hν

abbrev pointQuot (S : Submonoid (WithConv (A →ₐ[F] L))) : Type _ := A ⧸ vanishingIdealOfPoints (ptSet S)

end PointMonoid

end HopfAlgebra

namespace Tengoku.FltAnthropic.CartierDual

section BaseChange

universe u v w

variable (O : Type u) [CommRing O] (F : Type v) [CommRing F] [Algebra O F]
variable (A : Type w) [CommRing A] [Bialgebra O A]

/--
@isnad1 id=eq.0h5v.s7.01060f410501 from=translated src=- shape=9be34059 vocab=9a98515f
-/
theorem add_apply_pt {R : Type*} [CommRing R] {X : Type*} [CommRing X] [Bialgebra R X]
    (φ ψ : CartierDual R X) (x : X) : (φ + ψ) x = φ x + ψ x := by
  rw [← CartierDual.toDual_apply (φ + ψ), map_add, LinearMap.add_apply, CartierDual.toDual_apply,
    CartierDual.toDual_apply]

/--
@isnad1 id=eq.0h3v.s6.314aa7b87043 from=translated src=- shape=70d24d67 vocab=8edd7a44
-/
theorem zero_apply_pt {R : Type*} [CommRing R] {X : Type*} [CommRing X] [Bialgebra R X]
    (x : X) : (0 : CartierDual R X) x = 0 := by
  rw [← CartierDual.toDual_apply (0 : CartierDual R X), map_zero, LinearMap.zero_apply]

/--
@isnad1 id=eq.0h5v.s7.bd3ad23f642e from=translated src=- shape=5e4b1b62 vocab=914fbead
-/
theorem smul_apply_pt {R : Type*} [CommRing R] {X : Type*} [CommRing X] [Bialgebra R X]
    (c : R) (φ : CartierDual R X) (x : X) : (c • φ) x = c * φ x := by
  rw [← CartierDual.toDual_apply (c • φ), LinearEquiv.map_smul, LinearMap.smul_apply, smul_eq_mul,
    CartierDual.toDual_apply]

noncomputable instance instModuleRestrictBaseChange : Module O (CartierDual F (F ⊗[O] A)) :=
  Module.compHom (CartierDual F (F ⊗[O] A)) (algebraMap O F)

/--
@isnad1 id=isscalar.0h3v.s11.46422185f22b from=translated src=- shape=c64ddfde vocab=02e7ace6
-/
instance instIsScalarTowerRestrictBaseChange : IsScalarTower O F (CartierDual F (F ⊗[O] A)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

noncomputable instance instRingBaseChangeDual : Ring (F ⊗[O] CartierDual O A) := Algebra.TensorProduct.instRing

noncomputable instance instAlgebraBaseChangeDual : Algebra F (F ⊗[O] CartierDual O A) :=
  Algebra.TensorProduct.leftAlgebra

variable {O F A}

noncomputable def dualBaseChange (φ : CartierDual O A) : CartierDual F (F ⊗[O] A) :=
  CartierDual.ofDual F (F ⊗[O] A)
    ((TensorProduct.AlgebraTensorModule.rid O F F).toLinearMap ∘ₗ LinearMap.baseChange F (CartierDual.toDual O A φ))

/--
@isnad1 id=eq.0h6v.s9.fb89bb2adbf9 from=translated src=- shape=a449f4f8 vocab=104a386b
-/
@[simp] theorem dualBaseChange_tmul (φ : CartierDual O A) (c : F) (a : A) :
    dualBaseChange (F := F) φ (c ⊗ₜ[O] a) = c * algebraMap O F (φ a) := by
  show (TensorProduct.AlgebraTensorModule.rid O F F) ((LinearMap.baseChange F (CartierDual.toDual O A φ)) (c ⊗ₜ[O] a)) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.rid_tmul, CartierDual.toDual_apply, Algebra.smul_def,
    mul_comm]

variable (O F A) in

noncomputable def dualBaseChangeHom : CartierDual O A →ₗ[O] CartierDual F (F ⊗[O] A) where
  toFun := dualBaseChange
  map_add' φ ψ := by
    refine CartierDual.ext fun x => ?_
    rw [add_apply_pt]
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, add_zero]
    | tmul c a =>
      rw [dualBaseChange_tmul, dualBaseChange_tmul, dualBaseChange_tmul, add_apply_pt, map_add, mul_add]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; abel
  map_smul' r φ := by
    refine CartierDual.ext fun x => ?_
    rw [RingHom.id_apply]
    show dualBaseChange (r • φ) x = ((algebraMap O F r) • dualBaseChange φ) x
    rw [smul_apply_pt]
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, mul_zero]
    | tmul c a => rw [dualBaseChange_tmul, dualBaseChange_tmul, smul_apply_pt, map_mul]; ring
    | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add]

variable (O F A) in

noncomputable def dualBaseChangeLin : F ⊗[O] CartierDual O A →ₗ[F] CartierDual F (F ⊗[O] A) :=
  LinearMap.liftBaseChange F (dualBaseChangeHom O F A)

/--
@isnad1 id=eq.0h5v.s11.34b4c964be96 from=translated src=- shape=b07889b2 vocab=3b6fcb5d
-/
@[simp] theorem dualBaseChangeLin_tmul (c : F) (φ : CartierDual O A) :
    dualBaseChangeLin O F A (c ⊗ₜ[O] φ) = c • dualBaseChange φ :=
  LinearMap.liftBaseChange_tmul F _ c φ

/--
@isnad1 id=eq.0h7v.s11.dc026a5d5210 from=translated src=- shape=0df95eb2 vocab=f03c1d21
-/
theorem dualBaseChangeLin_tmul_tmul (c : F) (φ : CartierDual O A) (c' : F) (a : A) :
    dualBaseChangeLin O F A (c ⊗ₜ[O] φ) (c' ⊗ₜ[O] a) = c * c' * algebraMap O F (φ a) := by
  rw [dualBaseChangeLin_tmul, smul_apply_pt, dualBaseChange_tmul, mul_assoc]

end BaseChange

end Tengoku.FltAnthropic.CartierDual

namespace HopfAlgebra

section Character

universe u v w

variable (O : Type u) [CommRing O] (F : Type v) [CommRing F] [Algebra O F]
variable (A : Type w) [CommRing A] [Bialgebra O A]
variable (L : Type*) [CommRing L] [Algebra F L]

noncomputable def characterGenericFibre (S : Set (F ⊗[O] A →ₐ[F] L)) : Subalgebra F (F ⊗[O] CartierDual O A) :=
  Algebra.adjoin F {w | ∀ x ∈ vanishingIdealOfPoints S, CartierDual.dualBaseChangeLin O F A w x = 0}

/--
@isnad1 id=le.1h6v.s10.001db743d43f from=translated src=- shape=e59365f3 vocab=c0df6874
-/
theorem characterGenericFibre_mono {S T : Set (F ⊗[O] A →ₐ[F] L)} (h : S ⊆ T) :
    characterGenericFibre O F A L S ≤ characterGenericFibre O F A L T := by
  apply Algebra.adjoin_mono
  intro w hw x hx
  exact hw x (vanishingIdealOfPoints_antitone h hx)

/--
@isnad1 id=le.0h5v.s12.204a7dde6903 from=translated src=- shape=df337bd2 vocab=d044687e
-/
theorem subset_characterGenericFibre (S : Set (F ⊗[O] A →ₐ[F] L)) :
    {w | ∀ x ∈ vanishingIdealOfPoints S, CartierDual.dualBaseChangeLin O F A w x = 0}
      ⊆ (characterGenericFibre O F A L S : Set (F ⊗[O] CartierDual O A)) :=
  Algebra.subset_adjoin

end Character

section Closure

universe u v w

variable (O : Type u) [CommRing O] (F : Type v) [Field F] [Algebra O F]
variable (A : Type w) [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A]
variable (L : Type*) [CommRing L] [Algebra F L]

noncomputable abbrev characterClosure (S : Set (F ⊗[O] A →ₐ[F] L)) : Subalgebra O (CartierDual O A) :=
  flatClosure (characterGenericFibre O F A L S)

/--
@isnad1 id=iff.0h6v.s9.5c56fbab8701 from=translated src=- shape=7b6f6cf5 vocab=4b572b4e
-/
theorem mem_characterClosure_iff (S : Set (F ⊗[O] A →ₐ[F] L)) (g : CartierDual O A) :
    g ∈ characterClosure O F A L S ↔ (1 : F) ⊗ₜ[O] g ∈ characterGenericFibre O F A L S := Iff.rfl

/--
@isnad1 id=le.1h6v.s9.c2a4e1e7c0ee from=translated src=- shape=115eda6c vocab=bd95c44d
-/
theorem characterClosure_mono {S T : Set (F ⊗[O] A →ₐ[F] L)} (h : S ⊆ T) :
    characterClosure O F A L S ≤ characterClosure O F A L T :=
  flatClosure_mono (characterGenericFibre_mono O F A L h)

end Closure

end HopfAlgebra
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)

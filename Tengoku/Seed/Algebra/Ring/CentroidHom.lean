/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christopher Hoskin
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Algebra.Defs  -- shake: keep (`example` dependency)
public import Tengoku.Seed.Algebra.Group.Action.Pi
public import Tengoku.Seed.Algebra.Module.Hom
public import Tengoku.Seed.GroupTheory.GroupAction.Ring
public import Tengoku.Seed.RingTheory.NonUnitalSubsemiring.Basic
public import Tengoku.Seed.Algebra.Ring.Subsemiring.Basic

/-!
# Centroid homomorphisms

Let `A` be a (nonunital, non-associative) algebra. The centroid of `A` is the set of linear maps
`T` on `A` such that `T` commutes with left and right multiplication, that is to say, for all `a`
and `b` in `A`,
$$
T(ab) = (Ta)b, T(ab) = a(Tb).
$$
In mathlib we call elements of the centroid "centroid homomorphisms" (`CentroidHom`) in keeping
with `AddMonoidHom` etc.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `CentroidHom`: Maps which preserve left and right multiplication.

## Typeclasses

* `CentroidHomClass`

## References

* [Jacobson, Structure of Rings][Jacobson1956]
* [McCrimmon, A taste of Jordan algebras][mccrimmon2004]

## Tags

centroid
-/

@[expose] public section

assert_not_exists Field

open Function

variable {F M N R α : Type*}

/-- The type of centroid homomorphisms from `α` to `α`. -/
structure CentroidHom (α : Type*) [NonUnitalNonAssocSemiring α] extends α →+ α where
  /-- Commutativity of centroid homomorphisms with left multiplication. -/
  map_mul_left' (a b : α) : toFun (a * b) = a * toFun b
  /-- Commutativity of centroid homomorphisms with right multiplication. -/
  map_mul_right' (a b : α) : toFun (a * b) = toFun a * b

attribute [nolint docBlame] CentroidHom.toAddMonoidHom

/-- `CentroidHomClass F α` states that `F` is a type of centroid homomorphisms.

You should extend this class when you extend `CentroidHom`. -/
class CentroidHomClass (F : Type*) (α : outParam Type*)
    [NonUnitalNonAssocSemiring α] [FunLike F α α] : Prop extends AddMonoidHomClass F α α where
  /-- Commutativity of centroid homomorphisms with left multiplication. -/
  map_mul_left (f : F) (a b : α) : f (a * b) = a * f b
  /-- Commutativity of centroid homomorphisms with right multiplication. -/
  map_mul_right (f : F) (a b : α) : f (a * b) = f a * b


export CentroidHomClass (map_mul_left map_mul_right)

instance [NonUnitalNonAssocSemiring α] [FunLike F α α] [CentroidHomClass F α] :
    CoeTC F (CentroidHom α) :=
  ⟨fun f ↦
    { (f : α →+ α) with
      toFun := f
      map_mul_left' := map_mul_left f
      map_mul_right' := map_mul_right f }⟩

/-! ### Centroid homomorphisms -/

namespace CentroidHom

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α]

instance : FunLike (CentroidHom α) α α where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr with x
    exact congrFun h x

instance : CentroidHomClass (CentroidHom α) α where
  map_zero f := f.map_zero'
  map_add f := f.map_add'
  map_mul_left f := f.map_mul_left'
  map_mul_right f := f.map_mul_right'

/--
@isnad1 id=eq.0h2v.s6.fe6e6f3dae22 from=seed src=0 shape=5f77607d vocab=e2459510
-/
theorem toFun_eq_coe {f : CentroidHom α} : f.toFun = f := rfl

/--
@isnad1 id=eq.1h3v.s5.daa97db1e3fe from=seed src=0 shape=b15bb5b9 vocab=485a14e7
-/
@[ext]
theorem ext {f g : CentroidHom α} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/--
@isnad1 id=eq.0h2v.s6.5d5ba7641819 from=seed src=0 shape=d0c4e1d4 vocab=419db6f4
-/
@[simp, norm_cast]
theorem coe_toAddMonoidHom (f : CentroidHom α) : ⇑(f : α →+ α) = f :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.225b9e5b2d62 from=seed src=0 shape=57b8750b vocab=39f4a618
-/
@[simp]
theorem toAddMonoidHom_eq_coe (f : CentroidHom α) : f.toAddMonoidHom = f :=
  rfl

/--
@isnad1 id=injectiv.0h1v.s5.59a715c65052 from=seed src=0 shape=42a75067 vocab=8bcc0eb5
-/
theorem coe_toAddMonoidHom_injective : Injective ((↑) : CentroidHom α → α →+ α) :=
  fun _f _g h => ext fun a ↦
    haveI := DFunLike.congr_fun h a
    this

/-- Turn a centroid homomorphism into an additive monoid endomorphism. -/
def toEnd (f : CentroidHom α) : AddMonoid.End α :=
  (f : α →+ α)

/--
@isnad1 id=injectiv.0h1v.s4.5d78fea677c4 from=seed src=0 shape=e716c754 vocab=d43d4ff5
-/
theorem toEnd_injective : Injective (CentroidHom.toEnd : CentroidHom α → AddMonoid.End α) :=
  coe_toAddMonoidHom_injective

/-- Copy of a `CentroidHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : CentroidHom α) (f' : α → α) (h : f' = f) : CentroidHom α :=
  { f.toAddMonoidHom.copy f' <| h with
    toFun := f'
    map_mul_left' := fun a b ↦ by simp_rw [h, map_mul_left]
    map_mul_right' := fun a b ↦ by simp_rw [h, map_mul_right] }

/--
@isnad1 id=eq.1h3v.s5.ba65f4ea282f from=seed src=0 shape=28690eb2 vocab=ce8eb266
-/
@[simp]
theorem coe_copy (f : CentroidHom α) (f' : α → α) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
@isnad1 id=eq.1h3v.s5.73f0928d03c5 from=seed src=0 shape=ca119242 vocab=ce8eb266
-/
theorem copy_eq (f : CentroidHom α) (f' : α → α) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `CentroidHom`. -/
protected def id : CentroidHom α :=
  { AddMonoidHom.id α with
    map_mul_left' := fun _ _ ↦ rfl
    map_mul_right' := fun _ _ ↦ rfl }

instance : Inhabited (CentroidHom α) :=
  ⟨CentroidHom.id α⟩

/--
@isnad1 id=eq.0h1v.s4.616934eeb9d5 from=seed src=0 shape=676f2ab7 vocab=46b29241
-/
@[simp, norm_cast]
theorem coe_id : ⇑(CentroidHom.id α) = id :=
  rfl

/--
@isnad1 id=eq.0h1v.s6.aece03db4170 from=seed src=0 shape=8c76b44f vocab=b4451dc2
-/
@[simp, norm_cast]
theorem toAddMonoidHom_id : (CentroidHom.id α : α →+ α) = AddMonoidHom.id α :=
  rfl

variable {α}

/--
@isnad1 id=eq.0h2v.s4.262e4676e7cd from=seed src=0 shape=674d8978 vocab=0399bf9f
-/
@[simp]
theorem id_apply (a : α) : CentroidHom.id α a = a :=
  rfl

/-- Composition of `CentroidHom`s as a `CentroidHom`. -/
def comp (g f : CentroidHom α) : CentroidHom α :=
  { g.toAddMonoidHom.comp f.toAddMonoidHom with
    map_mul_left' := fun _a _b ↦ (congr_arg g <| f.map_mul_left' _ _).trans <| g.map_mul_left' _ _
    map_mul_right' := fun _a _b ↦
      (congr_arg g <| f.map_mul_right' _ _).trans <| g.map_mul_right' _ _ }

/--
@isnad1 id=eq.0h3v.s5.229fa9da8855 from=seed src=0 shape=357637a3 vocab=92cf5f0e
-/
@[simp, norm_cast]
theorem coe_comp (g f : CentroidHom α) : ⇑(g.comp f) = g ∘ f :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.213a9ee74100 from=seed src=0 shape=169a8db9 vocab=1aed102b
-/
@[simp]
theorem comp_apply (g f : CentroidHom α) (a : α) : g.comp f a = g (f a) :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.53426fd03e96 from=seed src=0 shape=84bb8975 vocab=b27d1c65
-/
@[simp, norm_cast]
theorem coe_comp_addMonoidHom (g f : CentroidHom α) : (g.comp f : α →+ α) = (g : α →+ α).comp f :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.1e410a055262 from=seed src=0 shape=ee02721c vocab=6a35c4e9
-/
@[simp]
theorem comp_assoc (h g f : CentroidHom α) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.2383c5f7a197 from=seed src=0 shape=807c4d20 vocab=81d5e845
-/
@[simp]
theorem comp_id (f : CentroidHom α) : f.comp (CentroidHom.id α) = f :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.6c127d33d9a8 from=seed src=0 shape=2c343361 vocab=81d5e845
-/
@[simp]
theorem id_comp (f : CentroidHom α) : (CentroidHom.id α).comp f = f :=
  rfl

/--
@isnad1 id=iff.1h4v.s5.4da0bb4eb64e from=seed src=0 shape=bffe5be7 vocab=dcbd6705
-/
@[simp]
theorem cancel_right {g₁ g₂ f : CentroidHom α} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h ↦ ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun a ↦ congrFun (congrArg comp a) f⟩

/--
@isnad1 id=iff.1h4v.s5.9e278b34cc0e from=seed src=0 shape=df66c057 vocab=a506e6f4
-/
@[simp]
theorem cancel_left {g f₁ f₂ : CentroidHom α} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h ↦ ext fun a ↦ hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

instance : Zero (CentroidHom α) :=
  ⟨{ (0 : α →+ α) with
      map_mul_left' := fun _a _b ↦ (mul_zero _).symm
      map_mul_right' := fun _a _b ↦ (zero_mul _).symm }⟩

instance : One (CentroidHom α) :=
  ⟨CentroidHom.id α⟩

instance : Add (CentroidHom α) :=
  ⟨fun f g ↦
    { (f + g : α →+ α) with
      map_mul_left' := fun a b ↦ by
        simp [map_mul_left, mul_add]
      map_mul_right' := fun a b ↦ by
        simp [map_mul_right, add_mul] }⟩

instance : Mul (CentroidHom α) :=
  ⟨comp⟩

variable [Monoid M] [Monoid N] [Semiring R]
variable [DistribMulAction M α] [SMulCommClass M α α] [IsScalarTower M α α]
variable [DistribMulAction N α] [SMulCommClass N α α] [IsScalarTower N α α]
variable [Module R α] [SMulCommClass R α α] [IsScalarTower R α α]

instance instSMul : SMul M (CentroidHom α) where
  smul n f :=
    { (n • f : α →+ α) with
      map_mul_left' := fun a b ↦ by
        change n • f (a * b) = a * n • f b
        rw [map_mul_left f, ← mul_smul_comm]
      map_mul_right' := fun a b ↦ by
        change n • f (a * b) = n • f a * b
        rw [map_mul_right f, ← smul_mul_assoc] }

instance [SMul M N] [IsScalarTower M N α] : IsScalarTower M N (CentroidHom α) where
  smul_assoc _ _ _ := ext fun _ => smul_assoc _ _ _

instance [SMulCommClass M N α] : SMulCommClass M N (CentroidHom α) where
  smul_comm _ _ _ := ext fun _ => smul_comm _ _ _

instance [DistribMulAction Mᵐᵒᵖ α] [IsCentralScalar M α] : IsCentralScalar M (CentroidHom α) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

/--
@isnad1 id=isscalar.0h2v.s7.1a393c324aca from=seed src=0 shape=c550112f vocab=fc9694d8
-/
instance isScalarTowerRight : IsScalarTower M (CentroidHom α) (CentroidHom α) where
  smul_assoc _ _ _ := rfl

instance hasNPowNat : Pow (CentroidHom α) ℕ :=
  ⟨fun f n ↦
    { toAddMonoidHom := (f.toEnd ^ n : AddMonoid.End α)
      map_mul_left' := fun a b ↦ by
        induction n with
        | zero => rfl
        | succ n ih =>
          rw [pow_succ']
          exact (congr_arg f.toEnd ih).trans (f.map_mul_left' _ _)
      map_mul_right' := fun a b ↦ by
        induction n with
        | zero => rfl
        | succ n ih =>
          rw [pow_succ']
          exact (congr_arg f.toEnd ih).trans (f.map_mul_right' _ _)}⟩

/--
@isnad1 id=eq.0h1v.s5.bf37a2c08a10 from=seed src=0 shape=c47991b3 vocab=485a14e7
-/
@[simp, norm_cast]
theorem coe_zero : ⇑(0 : CentroidHom α) = 0 :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.07928907aa08 from=seed src=0 shape=0fbb7209 vocab=c7c615e2
-/
@[simp, norm_cast]
theorem coe_one : ⇑(1 : CentroidHom α) = id :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.9715be5133a9 from=seed src=0 shape=1138b575 vocab=fb7a8e07
-/
@[simp, norm_cast]
theorem coe_add (f g : CentroidHom α) : ⇑(f + g) = f + g :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.44ae965b96a7 from=seed src=0 shape=80c81f5f vocab=248a8aad
-/
@[simp, norm_cast]
theorem coe_mul (f g : CentroidHom α) : ⇑(f * g) = f ∘ g :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.3a5f58701967 from=seed src=0 shape=c4f7a222 vocab=732dd24f
-/
@[simp, norm_cast]
theorem coe_smul (n : M) (f : CentroidHom α) : ⇑(n • f) = n • ⇑f :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.660b96e544a7 from=seed src=0 shape=39a216a7 vocab=485a14e7
-/
@[simp]
theorem zero_apply (a : α) : (0 : CentroidHom α) a = 0 :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.a8048b04b2aa from=seed src=0 shape=8da7778c vocab=485a14e7
-/
@[simp]
theorem one_apply (a : α) : (1 : CentroidHom α) a = a :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.91747833f00d from=seed src=0 shape=608433c8 vocab=fb7a8e07
-/
@[simp]
theorem add_apply (f g : CentroidHom α) (a : α) : (f + g) a = f a + g a :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.fef31ce28ee1 from=seed src=0 shape=2f029104 vocab=b4a6623d
-/
@[simp]
theorem mul_apply (f g : CentroidHom α) (a : α) : (f * g) a = f (g a) :=
  rfl

/--
@isnad1 id=eq.0h5v.s7.7022aae7627e from=seed src=0 shape=1f6b3fb2 vocab=732dd24f
-/
@[simp]
theorem smul_apply (n : M) (f : CentroidHom α) (a : α) : (n • f) a = n • f a :=
  rfl

example : SMul ℕ (CentroidHom α) := instSMul

/--
@isnad1 id=eq.0h1v.s6.34026b0c5beb from=seed src=0 shape=7b5bff60 vocab=09088345
-/
@[simp]
theorem toEnd_zero : (0 : CentroidHom α).toEnd = 0 :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.bf0610bba2ab from=seed src=0 shape=e69ef69b vocab=6ee142bb
-/
@[simp]
theorem toEnd_add (x y : CentroidHom α) : (x + y).toEnd = x.toEnd + y.toEnd :=
  rfl

/--
@isnad1 id=eq.0h4v.s8.2c10903ffdcb from=seed src=0 shape=b37c3764 vocab=6cff0d41
-/
theorem toEnd_smul (m : M) (x : CentroidHom α) : (m • x).toEnd = m • x.toEnd :=
  rfl

instance : AddCommMonoid (CentroidHom α) :=
  coe_toAddMonoidHom_injective.addCommMonoid _ toEnd_zero toEnd_add (swap toEnd_smul)

instance : NatCast (CentroidHom α) where natCast n := n • (1 : CentroidHom α)

/--
@isnad1 id=eq.0h2v.s6.96691d933296 from=seed src=0 shape=806ceb03 vocab=7742bb1a
-/
@[simp, norm_cast]
theorem coe_natCast (n : ℕ) : ⇑(n : CentroidHom α) = n • (CentroidHom.id α) :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.8e0a511885c3 from=seed src=0 shape=e92106e2 vocab=abee1746
-/
theorem natCast_apply (n : ℕ) (m : α) : (n : CentroidHom α) m = n • m :=
  rfl

/--
@isnad1 id=eq.0h1v.s6.32cd238d9a97 from=seed src=0 shape=7b5bff60 vocab=09088345
-/
@[simp]
theorem toEnd_one : (1 : CentroidHom α).toEnd = 1 :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.d28c81f0561b from=seed src=0 shape=e69ef69b vocab=94c12616
-/
@[simp]
theorem toEnd_mul (x y : CentroidHom α) : (x * y).toEnd = x.toEnd * y.toEnd :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.8a27835c8dd6 from=seed src=0 shape=72e56f97 vocab=3b58789e
-/
@[simp]
theorem toEnd_pow (x : CentroidHom α) (n : ℕ) : (x ^ n).toEnd = x.toEnd ^ n :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.cd056d8da603 from=seed src=0 shape=7fb3ccf0 vocab=27feed63
-/
@[simp, norm_cast]
theorem toEnd_natCast (n : ℕ) : (n : CentroidHom α).toEnd = ↑n :=
  rfl

-- cf `add_monoid.End.semiring`
instance : Semiring (CentroidHom α) :=
  toEnd_injective.semiring _ toEnd_zero toEnd_one toEnd_add toEnd_mul toEnd_smul toEnd_pow
    toEnd_natCast

variable (α) in
/-- `CentroidHom.toEnd` as a `RingHom`. -/
@[simps]
def toEndRingHom : CentroidHom α →+* AddMonoid.End α where
  toFun := toEnd
  map_zero' := toEnd_zero
  map_one' := toEnd_one
  map_add' := toEnd_add
  map_mul' := toEnd_mul

/--
@isnad1 id=eq.0h5v.s6.8396377cc223 from=seed src=0 shape=3bf86cde vocab=248a8aad
-/
theorem comp_mul_comm (T S : CentroidHom α) (a b : α) : (T ∘ S) (a * b) = (S ∘ T) (a * b) := by
  simp only [Function.comp_apply]
  rw [map_mul_right, map_mul_left, ← map_mul_right, ← map_mul_left]

instance : DistribMulAction M (CentroidHom α) :=
  toEnd_injective.distribMulAction (toEndRingHom α).toAddMonoidHom toEnd_smul

instance : Module R (CentroidHom α) :=
  toEnd_injective.module R (toEndRingHom α).toAddMonoidHom toEnd_smul

/-!
The following instances show that `α` is a non-unital and non-associative algebra over
`CentroidHom α`.
-/

/-- The tautological action by `CentroidHom α` on `α`.

This generalizes `Function.End.applyMulAction`. -/
instance applyModule : Module (CentroidHom α) α where
  smul T a := T a
  add_smul _ _ _ := rfl
  zero_smul _ := rfl
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero := map_zero
  smul_add := map_add

/--
@isnad1 id=eq.0h3v.s6.2e8cf744f7f5 from=seed src=0 shape=f044405b vocab=9591304e
-/
@[simp]
lemma smul_def (T : CentroidHom α) (a : α) : T • a = T a := rfl

instance : SMulCommClass (CentroidHom α) α α where
  smul_comm _ _ _ := map_mul_left _ _ _

instance : SMulCommClass α (CentroidHom α) α := SMulCommClass.symm _ _ _

instance : IsScalarTower (CentroidHom α) α α where
  smul_assoc _ _ _ := (map_mul_right _ _ _).symm

/-!
Let `α` be an algebra over `R`, such that the canonical ring homomorphism of `R` into
`CentroidHom α` lies in the center of `CentroidHom α`. Then `CentroidHom α` is an algebra over `R`
-/

variable {R : Type*}
variable [CommSemiring R]
variable [Module R α] [SMulCommClass R α α] [IsScalarTower R α α]

/-- The natural ring homomorphism from `R` into `CentroidHom α`.

This is a stronger version of `Module.toAddMonoidEnd`. -/
@[simps! apply_toFun]
def _root_.Module.toCentroidHom : R →+* CentroidHom α := RingHom.smulOneHom

open Module in
/-- `CentroidHom α` as an algebra over `R`. -/
example (h : ∀ (r : R) (T : CentroidHom α), toCentroidHom r * T = T * toCentroidHom r) :
    Algebra R (CentroidHom α) := toCentroidHom.toAlgebra' h

local notation "L" => AddMonoid.End.mulLeft
local notation "R" => AddMonoid.End.mulRight

/--
@isnad1 id=eq.0h1v.s8.cb57b7a3c073 from=seed src=0 shape=2bdf744e vocab=a53fb8b4
-/
lemma centroid_eq_centralizer_mulLeftRight :
    RingHom.rangeS (toEndRingHom α) = Subsemiring.centralizer (Set.range L ∪ Set.range R) := by
  ext T
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨f, rfl⟩ S (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact AddMonoidHom.ext fun b ↦ (map_mul_left f a b).symm
    · exact AddMonoidHom.ext fun a ↦ (map_mul_right f a b).symm
  · rw [Subsemiring.mem_centralizer_iff] at h
    refine ⟨⟨T, fun a b ↦ ?_, fun a b ↦ ?_⟩, rfl⟩
    · exact congr($(h (L a) (.inl ⟨a, rfl⟩)) b).symm
    · exact congr($(h (R b) (.inr ⟨b, rfl⟩)) a).symm

/-- The canonical homomorphism from the center into the center of the centroid -/
def centerToCentroidCenter :
    NonUnitalSubsemiring.center α →ₙ+* Subsemiring.center (CentroidHom α) where
  toFun z :=
    { L (z : α) with
      val := ⟨L z, z.prop.left_comm, z.prop.left_assoc ⟩
      property := by
        rw [Subsemiring.mem_center_iff]
        intro g
        ext a
        exact map_mul_left g (↑z) a }
  map_zero' := by
    simp only [ZeroMemClass.coe_zero, map_zero]
    exact rfl
  map_add' := fun _ _ => by
    dsimp
    simp only [map_add]
    rfl
  map_mul' z₁ z₂ := by ext a; exact (z₁.prop.left_assoc z₂ a).symm

instance : FunLike (Subsemiring.center (CentroidHom α)) α α where
  coe f := f.val.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr with x
    exact congrFun h x

/--
@isnad1 id=eq.0h3v.s9.bebb138d1d29 from=seed src=0 shape=34e3226a vocab=b05a3c7c
-/
lemma centerToCentroidCenter_apply (z : NonUnitalSubsemiring.center α) (a : α) :
    (centerToCentroidCenter z) a = z * a := rfl

/-- The canonical homomorphism from the center into the centroid -/
def centerToCentroid : NonUnitalSubsemiring.center α →ₙ+* CentroidHom α :=
  NonUnitalRingHom.comp
    (SubsemiringClass.subtype (Subsemiring.center (CentroidHom α))).toNonUnitalRingHom
    centerToCentroidCenter

/--
@isnad1 id=eq.0h3v.s8.b0ca2315acc7 from=seed src=0 shape=a18586a7 vocab=15517545
-/
lemma centerToCentroid_apply (z : NonUnitalSubsemiring.center α) (a : α) :
    (centerToCentroid z) a = z * a := rfl

lemma _root_.NonUnitalNonAssocSemiring.mem_center_iff (a : α) :
    a ∈ NonUnitalSubsemiring.center α ↔ R a = L a ∧ (L a) ∈ RingHom.rangeS (toEndRingHom α) := by
  constructor
  · exact fun ha ↦ ⟨AddMonoidHom.ext <| fun _ => (IsMulCentral.comm ha _).symm,
      ⟨centerToCentroid ⟨a, ha⟩, rfl⟩⟩
  · rintro ⟨hc, ⟨T, hT⟩⟩
    have e1 (d : α) : T d = a * d := congr($hT d)
    have e2 (d : α) : T d = d * a := congr($(hT.trans hc.symm) d)
    constructor
    case comm => exact (congr($hc.symm ·))
    case left_assoc => simpa [e1] using (map_mul_right T · ·)
    case right_assoc => simpa [e2] using (map_mul_left T · ·)

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocCommSemiring

variable [NonUnitalNonAssocCommSemiring α]

/-
Left and right multiplication coincide as α is commutative
-/
local notation "L" => AddMonoid.End.mulLeft

lemma _root_.NonUnitalNonAssocCommSemiring.mem_center_iff (a : α) :
    a ∈ NonUnitalSubsemiring.center α ↔ ∀ b : α, Commute (L b) (L a) := by
  rw [NonUnitalNonAssocSemiring.mem_center_iff, CentroidHom.centroid_eq_centralizer_mulLeftRight,
    Subsemiring.mem_centralizer_iff, AddMonoid.End.mulRight_eq_mulLeft, Set.union_self]
  aesop

end NonUnitalNonAssocCommSemiring

section NonAssocSemiring

variable [NonAssocSemiring α]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism from the center of a (non-associative) semiring onto its centroid. -/
def centerIsoCentroid : Subsemiring.center α ≃+* CentroidHom α :=
  { centerToCentroid with
    invFun := fun T ↦
      ⟨T 1, by constructor <;> simp [commute_iff_eq, ← map_mul_left, ← map_mul_right]⟩
    left_inv := fun z ↦ Subtype.ext <| by simp only [MulHom.toFun_eq_coe,
      NonUnitalRingHom.coe_toMulHom, centerToCentroid_apply, mul_one]
    right_inv := fun T ↦ CentroidHom.ext <| fun _ => by rw [MulHom.toFun_eq_coe,
      NonUnitalRingHom.coe_toMulHom, centerToCentroid_apply, ← map_mul_right, one_mul] }

end NonAssocSemiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α]

/-- Negation of `CentroidHom`s as a `CentroidHom`. -/
instance : Neg (CentroidHom α) :=
  ⟨fun f ↦
    { (-f : α →+ α) with
      map_mul_left' := fun a b ↦ by
        simp [map_mul_left]
      map_mul_right' := fun a b ↦ by
        simp [map_mul_right] }⟩

instance : Sub (CentroidHom α) :=
  ⟨fun f g ↦
    { (f - g : α →+ α) with
      map_mul_left' := fun a b ↦ by
        simp [map_mul_left, mul_sub]
      map_mul_right' := fun a b ↦ by
        simp [map_mul_right, sub_mul] }⟩

instance : IntCast (CentroidHom α) where intCast z := z • (1 : CentroidHom α)

/--
@isnad1 id=eq.0h2v.s6.18591bcf003d from=seed src=0 shape=806ceb03 vocab=0ccb69f5
-/
@[simp, norm_cast]
theorem coe_intCast (z : ℤ) : ⇑(z : CentroidHom α) = z • (CentroidHom.id α) :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.9b3400e0acdd from=seed src=0 shape=e92106e2 vocab=41c8a93c
-/
theorem intCast_apply (z : ℤ) (m : α) : (z : CentroidHom α) m = z • m :=
  rfl

/--
@isnad1 id=eq.0h2v.s7.d68163be6b7c from=seed src=0 shape=5c68212b vocab=d644f07e
-/
@[simp]
theorem toEnd_neg (x : CentroidHom α) : (-x).toEnd = -x.toEnd :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.50d3d40f6dc4 from=seed src=0 shape=e69ef69b vocab=1d1af010
-/
@[simp]
theorem toEnd_sub (x y : CentroidHom α) : (x - y).toEnd = x.toEnd - y.toEnd :=
  rfl

instance : AddCommGroup (CentroidHom α) :=
  toEnd_injective.addCommGroup _
    toEnd_zero toEnd_add toEnd_neg toEnd_sub (swap toEnd_smul) (swap toEnd_smul)

/--
@isnad1 id=eq.0h2v.s6.dea1a74e65c5 from=seed src=0 shape=269ae013 vocab=e10c8406
-/
@[simp, norm_cast]
theorem coe_neg (f : CentroidHom α) : ⇑(-f) = -f :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.04c717fe612e from=seed src=0 shape=1138b575 vocab=a4a5ab0b
-/
@[simp, norm_cast]
theorem coe_sub (f g : CentroidHom α) : ⇑(f - g) = f - g :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.3a218235fb33 from=seed src=0 shape=5d62883c vocab=e10c8406
-/
@[simp]
theorem neg_apply (f : CentroidHom α) (a : α) : (-f) a = -f a :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.79797ae7f8d4 from=seed src=0 shape=608433c8 vocab=a4a5ab0b
-/
@[simp]
theorem sub_apply (f g : CentroidHom α) (a : α) : (f - g) a = f a - g a :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.1df5d866bd72 from=seed src=0 shape=7fb3ccf0 vocab=58c4e35d
-/
@[simp, norm_cast]
theorem toEnd_intCast (z : ℤ) : (z : CentroidHom α).toEnd = ↑z :=
  rfl

instance instRing : Ring (CentroidHom α) :=
  toEnd_injective.ring _ toEnd_zero toEnd_one toEnd_add toEnd_mul toEnd_neg toEnd_sub
    toEnd_smul toEnd_smul toEnd_pow toEnd_natCast toEnd_intCast

end NonUnitalNonAssocRing

section NonUnitalRing

variable [NonUnitalRing α]

-- See note [reducible non-instances]
/-- A prime associative ring has commutative centroid. -/
abbrev commRing
    (h : ∀ a b : α, (∀ r : α, a * r * b = 0) → a = 0 ∨ b = 0) : CommRing (CentroidHom α) :=
  { CentroidHom.instRing with
    mul_comm := fun f g ↦ by
      ext
      refine sub_eq_zero.1 (or_self_iff.1 <| (h _ _) fun r ↦ ?_)
      rw [mul_assoc, sub_mul, sub_eq_zero, ← map_mul_right, ← map_mul_right, coe_mul, coe_mul,
        comp_mul_comm] }

end NonUnitalRing

end CentroidHom

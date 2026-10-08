/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.CStarAlgebra.Module.Constructions
public import Tengoku.Seed.Analysis.Matrix.Normed
public import Tengoku.Seed.Topology.UniformSpace.Matrix
public import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# Matrices with entries in a C⋆-algebra

This file creates a type copy of `Matrix m n A` called `CStarMatrix m n A` meant for matrices with
entries in a C⋆-algebra `A`. Its action on `C⋆ᵐᵒᵈ (n → A)` (via `Matrix.mulVec`) gives
it the operator norm, and this norm makes `CStarMatrix n n A` a C⋆-algebra.

## Main declarations

+ `CStarMatrix m n A`: the type copy
+ `CStarMatrix.instNonUnitalCStarAlgebra`: square matrices with entries in a non-unital C⋆-algebra
    form a non-unital C⋆-algebra
+ `CStarMatrix.instCStarAlgebra`: square matrices with entries in a unital C⋆-algebra form a
    unital C⋆-algebra

## Implementation notes

The norm on this type induces the product uniformity and bornology, but these are not defeq to
`Pi.uniformSpace` and `Pi.instBornology`. Hence, we prove the equality to the Pi instances and
replace the uniformity and bornology by the Pi ones when registering the
`NormedAddCommGroup (CStarMatrix m n A)` instance. See the docstring of the `TopologyAux` section
below for more details.
-/

@[expose] public section

open scoped ComplexOrder Topology Uniformity Bornology Matrix NNReal InnerProductSpace
  WithCStarModule

/-- Type copy `Matrix m n A` meant for matrices with entries in a C⋆-algebra. This is
a C⋆-algebra when `m = n`. -/
def CStarMatrix (m : Type*) (n : Type*) (A : Type*) := Matrix m n A

namespace CStarMatrix

variable {m n R S A B : Type*}

section basic

variable (m n A) in
/-- The equivalence between `Matrix m n A` and `CStarMatrix m n A`. -/
def ofMatrix {m n A : Type*} : Matrix m n A ≃ CStarMatrix m n A := Equiv.refl _

/--
@isnad1 id=eq.0h5v.s6.85a901803cf3 from=seed src=0 shape=09451636 vocab=988b53c3
-/
@[simp]
lemma ofMatrix_apply {M : Matrix m n A} {i : m} : (ofMatrix M) i = M i := rfl

/--
@isnad1 id=eq.0h5v.s6.02da00edb212 from=seed src=0 shape=7f5cc0a4 vocab=a45f99cd
-/
@[simp]
lemma ofMatrix_symm_apply {M : CStarMatrix m n A} {i : m} : (ofMatrix.symm M) i = M i := rfl

/--
@isnad1 id=iff.0h5v.s5.e7d72b5b9d4a from=seed src=0 shape=d0b5c4db vocab=6d962552
-/
theorem ext_iff {M N : CStarMatrix m n A} : (∀ i j, M i j = N i j) ↔ M = N :=
  ⟨fun h => funext fun i => funext <| h i, fun h => by simp [h]⟩

/--
@isnad1 id=eq.1h5v.s5.f7746894bdf1 from=seed src=0 shape=b03a4f73 vocab=6d962552
-/
@[ext]
lemma ext {M₁ M₂ : CStarMatrix m n A} (h : ∀ i j, M₁ i j = M₂ i j) : M₁ = M₂ := ext_iff.mp h

/-- `M.map f` is the matrix obtained by applying `f` to each entry of the matrix `M`. -/
def map (M : CStarMatrix m n A) (f : A → B) : CStarMatrix m n B :=
  ofMatrix fun i j => f (M i j)

/--
@isnad1 id=eq.0h8v.s5.94f557219ce1 from=seed src=0 shape=2bab732e vocab=b3e465a7
-/
@[simp]
theorem map_apply {M : CStarMatrix m n A} {f : A → B} {i : m} {j : n} : M.map f i j = f (M i j) :=
  rfl

/--
@isnad1 id=eq.0h4v.s4.ea02e53294b5 from=seed src=0 shape=f91df0f6 vocab=08080922
-/
@[simp]
theorem map_id (M : CStarMatrix m n A) : M.map id = M := by
  ext
  rfl

/--
@isnad1 id=eq.0h4v.s4.c2ac900a8b39 from=seed src=0 shape=d9928176 vocab=b3e465a7
-/
@[simp]
theorem map_id' (M : CStarMatrix m n A) : M.map (·) = M := map_id M

/--
@isnad1 id=eq.0h8v.s5.eb17150f47a2 from=seed src=0 shape=d089eba1 vocab=607ed338
-/
theorem map_map {C : Type*} {M : Matrix m n A} {f : A → B} {g : B → C} :
    (M.map f).map g = M.map (g ∘ f) := by ext; rfl

/--
@isnad1 id=injectiv.1h5v.s5.136bee1d5575 from=seed src=0 shape=7c6922f1 vocab=5a9d8fae
-/
theorem map_injective {f : A → B} (hf : Function.Injective f) :
    Function.Injective fun M : CStarMatrix m n A => M.map f := fun _ _ h =>
  ext fun i j => hf <| ext_iff.mpr h i j

/-- The transpose of a matrix. -/
def transpose (M : CStarMatrix m n A) : CStarMatrix n m A :=
  ofMatrix fun x y => M y x

/--
@isnad1 id=eq.0h6v.s4.896e457773a7 from=seed src=0 shape=d6f1bb49 vocab=ff45fb8b
-/
@[simp]
theorem transpose_apply (M : CStarMatrix m n A) (i j) : transpose M i j = M j i :=
  rfl

/-- The conjugate transpose of a matrix defined in term of `star`. -/
def conjTranspose [Star A] (M : CStarMatrix m n A) : CStarMatrix n m A :=
  M.transpose.map star

/--
@isnad1 id=eq.0h6v.s5.02279d4fd5e4 from=seed src=0 shape=d2f1b18a vocab=d7f1a592
-/
@[simp]
theorem conjTranspose_apply [Star A] (M : CStarMatrix m n A) (i j) :
    conjTranspose M i j = star (M j i) := rfl

instance instStar [Star A] : Star (CStarMatrix n n A) where
  star M := M.conjTranspose

/--
@isnad1 id=eq.0h3v.s5.5f8d7ae8d2c6 from=seed src=0 shape=b8d8d7c6 vocab=d7f1a592
-/
lemma star_eq_conjTranspose [Star A] {M : CStarMatrix n n A} : star M = M.conjTranspose := rfl

instance instInvolutiveStar [InvolutiveStar A] : InvolutiveStar (CStarMatrix n n A) where
  star_involutive := star_involutive (R := Matrix n n A)

instance instInhabited [Inhabited A] : Inhabited (CStarMatrix m n A) :=
  inferInstanceAs <| Inhabited (Matrix m n A)

instance instDecidableEq [DecidableEq A] [Fintype m] [Fintype n] :
    DecidableEq (CStarMatrix m n A) :=
  inferInstanceAs <| DecidableEq (Matrix m n A)

instance {n m} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (α) [Fintype α] :
    Fintype (CStarMatrix m n α) :=
  inferInstanceAs <| Fintype (Matrix m n α)

instance {n m} [Finite m] [Finite n] (α) [Finite α] : Finite (CStarMatrix m n α) :=
  inferInstanceAs <| Finite (Matrix m n α)

instance instAdd [Add A] : Add (CStarMatrix m n A) :=
  inferInstanceAs <| Add (Matrix m n A)

instance instAddSemigroup [AddSemigroup A] : AddSemigroup (CStarMatrix m n A) :=
  inferInstanceAs <| AddSemigroup (Matrix m n A)

instance instAddCommSemigroup [AddCommSemigroup A] : AddCommSemigroup (CStarMatrix m n A) :=
  inferInstanceAs <| AddCommSemigroup (Matrix m n A)

instance instZero [Zero A] : Zero (CStarMatrix m n A) :=
  inferInstanceAs <| Zero (Matrix m n A)

instance instAddZeroClass [AddZeroClass A] : AddZeroClass (CStarMatrix m n A) :=
  inferInstanceAs <| AddZeroClass (Matrix m n A)

instance instSMul [SMul R A] : SMul R (CStarMatrix m n A) :=
  inferInstanceAs <| SMul R (Matrix m n A)

instance instAddMonoid [AddMonoid A] : AddMonoid (CStarMatrix m n A) where
  nsmul := letI := instSMul (R := ℕ) (A := A) (m := m) (n := n); (· • · )
  __ : AddMonoid (CStarMatrix m n A) := inferInstanceAs <| AddMonoid (Matrix m n A)

instance instAddCommMonoid [AddCommMonoid A] : AddCommMonoid (CStarMatrix m n A) :=
  inferInstanceAs <| AddCommMonoid (Matrix m n A)

instance instNeg [Neg A] : Neg (CStarMatrix m n A) :=
  inferInstanceAs <| Neg (Matrix m n A)

instance instSub [Sub A] : Sub (CStarMatrix m n A) :=
  inferInstanceAs <| Sub (Matrix m n A)

instance instAddGroup [AddGroup A] : AddGroup (CStarMatrix m n A) where
  zsmul := letI := instSMul (R := ℤ) (A := A) (m := m) (n := n); (· • · )
  __ : AddGroup (CStarMatrix m n A) := inferInstanceAs <| AddGroup (Matrix m n A)

instance instAddCommGroup [AddCommGroup A] : AddCommGroup (CStarMatrix m n A) :=
  inferInstanceAs <| AddCommGroup (Matrix m n A)

instance instUnique [Unique A] : Unique (CStarMatrix m n A) :=
  inferInstanceAs <| Unique (Matrix m n A)

/--
@isnad1 id=subsingl.0h3v.s3.15907a5fa0ca from=seed src=0 shape=d78238af vocab=ee91c170
-/
instance instSubsingleton [Subsingleton A] : Subsingleton (CStarMatrix m n A) :=
  inferInstanceAs <| Subsingleton (Matrix m n A)

/--
@isnad1 id=nontrivi.0h3v.s4.32a8c55db344 from=seed src=0 shape=733cba13 vocab=48108d9a
-/
instance instNontrivial [Nonempty m] [Nonempty n] [Nontrivial A] : Nontrivial (CStarMatrix m n A) :=
  inferInstanceAs <| Nontrivial (Matrix m n A)

/--
@isnad1 id=smulcomm.0h5v.s5.7dd6f4fa9120 from=seed src=0 shape=f1ce0f8f vocab=af38a062
-/
instance instSMulCommClass [SMul R A] [SMul S A] [SMulCommClass R S A] :
    SMulCommClass R S (CStarMatrix m n A) :=
  inferInstanceAs <| SMulCommClass R S (Matrix m n A)

/--
@isnad1 id=isscalar.0h5v.s5.61475cfda65f from=seed src=0 shape=fdaac2c8 vocab=bb32e5fa
-/
instance instIsScalarTower [SMul R S] [SMul R A] [SMul S A] [IsScalarTower R S A] :
    IsScalarTower R S (CStarMatrix m n A) :=
  inferInstanceAs <| IsScalarTower R S (Matrix m n A)

/--
@isnad1 id=iscentra.0h4v.s5.f4c26018d4d9 from=seed src=0 shape=26aecf15 vocab=fc8c7327
-/
instance instIsCentralScalar [SMul R A] [SMul Rᵐᵒᵖ A] [IsCentralScalar R A] :
    IsCentralScalar R (CStarMatrix m n A) :=
  inferInstanceAs <| IsCentralScalar R (Matrix m n A)

instance instMulAction [Monoid R] [MulAction R A] : MulAction R (CStarMatrix m n A) :=
  inferInstanceAs <| MulAction R (Matrix m n A)

instance instDistribMulAction [Monoid R] [AddMonoid A] [DistribMulAction R A] :
    DistribMulAction R (CStarMatrix m n A) :=
  inferInstanceAs <| DistribMulAction R (Matrix m n A)

instance instModule [Semiring R] [AddCommMonoid A] [Module R A] : Module R (CStarMatrix m n A) :=
  inferInstanceAs <| Module R (Matrix m n A)

/--
@isnad1 id=eq.0h5v.s5.464b1ff5bbbd from=seed src=0 shape=d1741aab vocab=e769bc7e
-/
@[simp]
theorem zero_apply [Zero A] (i : m) (j : n) : (0 : CStarMatrix m n A) i j = 0 := rfl

/--
@isnad1 id=eq.0h7v.s6.8b9b6ee88e94 from=seed src=0 shape=443cc35b vocab=2695bf34
-/
@[simp] theorem add_apply [Add A] (M N : CStarMatrix m n A) (i : m) (j : n) :
    (M + N) i j = (M i j) + (N i j) := rfl

/--
@isnad1 id=eq.0h8v.s6.8efcc879f479 from=seed src=0 shape=ed7de553 vocab=c6909d28
-/
@[simp] theorem smul_apply [SMul B A] (r : B) (M : CStarMatrix m n A) (i : m) (j : n) :
    (r • M) i j = r • (M i j) := rfl

/--
@isnad1 id=eq.0h7v.s6.5dd5a5cef0d9 from=seed src=0 shape=443cc35b vocab=9cc2397d
-/
@[simp] theorem sub_apply [Sub A] (M N : CStarMatrix m n A) (i : m) (j : n) :
    (M - N) i j = (M i j) - (N i j) := rfl

/--
@isnad1 id=eq.0h6v.s5.6a7f6d91e2da from=seed src=0 shape=0d95355b vocab=dcb69412
-/
@[simp] theorem neg_apply [Neg A] (M : CStarMatrix m n A) (i : m) (j : n) :
    (-M) i j = -(M i j) := rfl

/--
@isnad1 id=eq.0h3v.s6.a19fe13829d5 from=seed src=0 shape=1da546a9 vocab=bbb36ab3
-/
@[simp]
theorem conjTranspose_zero [AddMonoid A] [StarAddMonoid A] :
    conjTranspose (0 : CStarMatrix m n A) = 0 := by ext; simp

/-! simp-normal form pulls `of` to the outside, to match the `Matrix` API. -/

/--
@isnad1 id=eq.0h3v.s6.8dc3e2225359 from=seed src=0 shape=48f998dd vocab=b3ef8862
-/
@[simp] theorem of_zero [Zero A] : ofMatrix (0 : Matrix m n A) = 0 := rfl

/--
@isnad1 id=eq.0h5v.s7.d32bd3f63d62 from=seed src=0 shape=e2c86046 vocab=05c2465e
-/
@[simp] theorem of_add_of [Add A] (f g : Matrix m n A) :
    ofMatrix f + ofMatrix g = ofMatrix (f + g) := rfl

/--
@isnad1 id=eq.0h5v.s7.9ae8007ea81f from=seed src=0 shape=e2c86046 vocab=5f818c8f
-/
@[simp]
theorem of_sub_of [Sub A] (f g : Matrix m n A) : ofMatrix f - ofMatrix g = ofMatrix (f - g) :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.c389c58e40c3 from=seed src=0 shape=394f764a vocab=9f30f3bb
-/
@[simp] theorem neg_of [Neg A] (f : Matrix m n A) : -ofMatrix f = ofMatrix (-f) := rfl

/--
@isnad1 id=eq.0h6v.s7.0f97ba00e87e from=seed src=0 shape=daea124d vocab=c0040834
-/
@[simp] theorem smul_of [SMul R A] (r : R) (f : Matrix m n A) :
    r • ofMatrix f = ofMatrix (r • f) := rfl

/--
@isnad1 id=eq.0h5v.s5.3d5389585ee0 from=seed src=0 shape=ff5ee53a vocab=84c95da5
-/
theorem star_apply [Star A] {f : CStarMatrix n n A} {i j : n} :
    (star f) i j = star (f j i) := by
  rw [star_eq_conjTranspose, conjTranspose_apply]

/--
@isnad1 id=eq.1h5v.s5.615a883428e8 from=seed src=0 shape=4053577c vocab=de319c6f
-/
theorem star_apply_of_isSelfAdjoint [Star A] {f : CStarMatrix n n A} (hf : IsSelfAdjoint f)
    {i j : n} : star (f i j) = f j i := by
  rw [← star_apply, IsSelfAdjoint.star_eq hf]

instance instStarAddMonoid [AddMonoid A] [StarAddMonoid A] : StarAddMonoid (CStarMatrix n n A) where
  star_add := star_add (R := Matrix n n A)

/--
@isnad1 id=starmodu.0h3v.s5.606c92d2fca5 from=seed src=0 shape=0650a5c4 vocab=4f5acd5b
-/
instance instStarModule [Star R] [Star A] [SMul R A] [StarModule R A] :
    StarModule R (CStarMatrix n n A) where
  star_smul r a := star_smul r (ofMatrix.symm a)

/-- The equivalence to matrices, bundled as a linear equivalence. -/
def ofMatrixₗ [AddCommMonoid A] [Semiring R] [Module R A] :
    (Matrix m n A) ≃ₗ[R] CStarMatrix m n A := LinearEquiv.refl _ _

/-- The semilinear map constructed by applying a semilinear map to all the entries of the matrix. -/
@[simps]
def mapₗ [Semiring R] [Semiring S] {σ : R →+* S} [AddCommMonoid A] [AddCommMonoid B]
    [Module R A] [Module S B] (f : A →ₛₗ[σ] B) : CStarMatrix m n A →ₛₗ[σ] CStarMatrix m n B where
  toFun := fun M => M.map f
  map_add' M N := by ext; simp
  map_smul' r M := by ext; simp

section decidable

variable [DecidableEq n]

section zero_one

variable [Zero A] [One A]

instance instOne : One (CStarMatrix n n A) := inferInstanceAs <| One (Matrix n n A)

/--
@isnad1 id=eq.0h4v.s5.4c3004b924c9 from=seed src=0 shape=736fde13 vocab=1c519cd8
-/
theorem one_apply {i j} : (1 : CStarMatrix n n A) i j = if i = j then 1 else 0 := rfl

/--
@isnad1 id=eq.0h3v.s5.82c7a7e79a0a from=seed src=0 shape=13682b24 vocab=c0b8ce98
-/
@[simp]
theorem one_apply_eq (i) : (1 : CStarMatrix n n A) i i = 1 := Matrix.one_apply_eq _

/--
@isnad1 id=eq.1h4v.s5.1eb393d2388e from=seed src=0 shape=6f87d77b vocab=c0b8ce98
-/
@[simp] theorem one_apply_ne {i j} : i ≠ j → (1 : CStarMatrix n n A) i j = 0 := Matrix.one_apply_ne

/--
@isnad1 id=eq.1h4v.s5.d19e11bf9811 from=seed src=0 shape=639ed7d9 vocab=c0b8ce98
-/
theorem one_apply_ne' {i j} : j ≠ i → (1 : CStarMatrix n n A) i j = 0 := Matrix.one_apply_ne'

end zero_one

instance instAddMonoidWithOne [AddMonoidWithOne A] : AddMonoidWithOne (CStarMatrix n n A) :=
  inferInstanceAs <| AddMonoidWithOne (Matrix n n A)

instance instAddGroupWithOne [AddGroupWithOne A] : AddGroupWithOne (CStarMatrix n n A) :=
  inferInstanceAs <| AddGroupWithOne (Matrix n n A)

instance instAddCommMonoidWithOne [AddCommMonoidWithOne A] :
    AddCommMonoidWithOne (CStarMatrix n n A) :=
  inferInstanceAs <| AddCommMonoidWithOne (Matrix n n A)

instance instAddCommGroupWithOne [AddCommGroupWithOne A] :
    AddCommGroupWithOne (CStarMatrix n n A) :=
  inferInstanceAs <| AddCommGroupWithOne (Matrix n n A)

-- We want to be lower priority than `instHMul`, but without this we can't have operands with
-- implicit dimensions.
@[default_instance 100]
instance {l : Type*} [Fintype m] [Mul A] [AddCommMonoid A] :
    HMul (CStarMatrix l m A) (CStarMatrix m n A) (CStarMatrix l n A) where
  hMul M N := ofMatrix (ofMatrix.symm M * ofMatrix.symm N)

instance [Fintype n] [Mul A] [AddCommMonoid A] : Mul (CStarMatrix n n A) where mul M N := M * N

end decidable

/--
@isnad1 id=eq.0h8v.s6.7fc954ecce97 from=seed src=0 shape=1d36133f vocab=966f16ba
-/
theorem mul_apply {l : Type*} [Fintype m] [Mul A] [AddCommMonoid A] {M : CStarMatrix l m A}
    {N : CStarMatrix m n A} {i k} : (M * N) i k = ∑ j, M i j * N j k := rfl

/--
@isnad1 id=eq.0h8v.s6.3113a5d00c82 from=seed src=0 shape=b14e72e1 vocab=b0673787
-/
theorem mul_apply' {l : Type*} [Fintype m] [Mul A] [AddCommMonoid A] {M : CStarMatrix l m A}
    {N : CStarMatrix m n A} {i k} : (M * N) i k = (fun j => M i j) ⬝ᵥ fun j => N j k := rfl

/--
@isnad1 id=eq.0h8v.s8.e68fc3aac9c1 from=seed src=0 shape=9733e1f0 vocab=ef07a791
-/
@[simp]
theorem smul_mul {l : Type*} [Fintype n] [Monoid R] [AddCommMonoid A] [Mul A] [DistribMulAction R A]
    [IsScalarTower R A A] (a : R) (M : CStarMatrix m n A) (N : CStarMatrix n l A) :
    (a • M) * N = a • (M * N) := Matrix.smul_mul a M N

/--
@isnad1 id=eq.0h8v.s7.4d3de8c87111 from=seed src=0 shape=f6958614 vocab=5e34c1d6
-/
theorem mul_smul {l : Type*} [Fintype n] [Monoid R] [AddCommMonoid A] [Mul A] [DistribMulAction R A]
    [SMulCommClass R A A] (M : CStarMatrix m n A) (a : R) (N : CStarMatrix n l A) :
    M * (a • N) = a • (M * N) := Matrix.mul_smul M a N

/--
@isnad1 id=eq.0h5v.s6.d44ac9510925 from=seed src=0 shape=ffcaa952 vocab=32e08c1b
-/
@[simp]
protected theorem mul_zero {o : Type*} [Fintype n] [NonUnitalNonAssocSemiring A]
    (M : CStarMatrix m n A) : M * (0 : CStarMatrix n o A) = 0 := Matrix.mul_zero _

/--
@isnad1 id=eq.0h5v.s6.48442c1d73e0 from=seed src=0 shape=76bd0397 vocab=32e08c1b
-/
@[simp]
protected theorem zero_mul {l : Type*} [Fintype m] [NonUnitalNonAssocSemiring A]
    (M : CStarMatrix m n A) : (0 : CStarMatrix l m A) * M = 0 := Matrix.zero_mul _

/--
@isnad1 id=eq.0h7v.s7.fc68ba756f15 from=seed src=0 shape=fb2216a3 vocab=efdfa62f
-/
protected theorem mul_add {o : Type*} [Fintype n] [NonUnitalNonAssocSemiring A]
    (L : CStarMatrix m n A) (M N : CStarMatrix n o A) :
    L * (M + N) = L * M + L * N := Matrix.mul_add _ _ _

/--
@isnad1 id=eq.0h7v.s7.b5ab1f6acbae from=seed src=0 shape=04d77bef vocab=efdfa62f
-/
protected theorem add_mul {l : Type*} [Fintype m] [NonUnitalNonAssocSemiring A]
    (L M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (L + M) * N = L * N + M * N := Matrix.add_mul _ _ _

instance instNonUnitalNonAssocSemiring [Fintype n] [NonUnitalNonAssocSemiring A] :
    NonUnitalNonAssocSemiring (CStarMatrix n n A) :=
  inferInstanceAs <| NonUnitalNonAssocSemiring (Matrix n n A)

instance instNonUnitalNonAssocRing [Fintype n] [NonUnitalNonAssocRing A] :
    NonUnitalNonAssocRing (CStarMatrix n n A) :=
  inferInstanceAs <| NonUnitalNonAssocRing (Matrix n n A)

instance instNonUnitalSemiring [Fintype n] [NonUnitalSemiring A] :
    NonUnitalSemiring (CStarMatrix n n A) :=
  inferInstanceAs <| NonUnitalSemiring (Matrix n n A)

instance instNonAssocSemiring [Fintype n] [DecidableEq n] [NonAssocSemiring A] :
    NonAssocSemiring (CStarMatrix n n A) :=
  inferInstanceAs <| NonAssocSemiring (Matrix n n A)

instance instNonUnitalRing [Fintype n] [NonUnitalRing A] :
    NonUnitalRing (CStarMatrix n n A) :=
  inferInstanceAs <| NonUnitalRing (Matrix n n A)

instance instNonAssocRing [Fintype n] [DecidableEq n] [NonAssocRing A] :
    NonAssocRing (CStarMatrix n n A) :=
  inferInstanceAs <| NonAssocRing (Matrix n n A)

instance instSemiring [Fintype n] [DecidableEq n] [Semiring A] :
    Semiring (CStarMatrix n n A) :=
  inferInstanceAs <| Semiring (Matrix n n A)

instance instRing [Fintype n] [DecidableEq n] [Ring A] : Ring (CStarMatrix n n A) :=
  inferInstanceAs <| Ring (Matrix n n A)

/-- `ofMatrix` bundled as a ring equivalence. -/
def ofMatrixRingEquiv [Fintype n] [Semiring A] :
    Matrix n n A ≃+* CStarMatrix n n A :=
  { ofMatrix with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

instance instStarRing [Fintype n] [NonUnitalSemiring A] [StarRing A] :
    StarRing (CStarMatrix n n A) := inferInstanceAs <| StarRing (Matrix n n A)

instance instAlgebra [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [Algebra R A] :
    Algebra R (CStarMatrix n n A) := inferInstanceAs <| Algebra R (Matrix n n A)

/-- `ofMatrix` bundled as a star algebra equivalence. -/
def ofMatrixStarAlgEquiv [Fintype n] [SMul ℂ A] [Semiring A] [StarRing A] :
    Matrix n n A ≃⋆ₐ[ℂ] CStarMatrix n n A :=
  { ofMatrixRingEquiv with
    map_star' := fun _ => rfl
    map_smul' := fun _ _ => rfl }

/--
@isnad1 id=eq.0h2v.s8.7c80002e861f from=seed src=0 shape=7b69f8bd vocab=1bc3ceed
-/
lemma ofMatrix_eq_ofMatrixStarAlgEquiv [Fintype n] [SMul ℂ A] [Semiring A] [StarRing A] :
    (ofMatrix : Matrix n n A → CStarMatrix n n A)
      = (ofMatrixStarAlgEquiv : Matrix n n A → CStarMatrix n n A) := rfl

set_option backward.isDefEq.respectTransparency.types false in
variable (R) (A) in
/-- The natural map that reindexes a matrix's rows and columns with equivalent types is an
equivalence. -/
def reindexₗ {l o : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    (eₘ : m ≃ l) (eₙ : n ≃ o) : CStarMatrix m n A ≃ₗ[R] CStarMatrix l o A :=
  { Matrix.reindex eₘ eₙ with
    map_add' M N := by ext; simp
    map_smul' r M := by ext; simp }

/--
@isnad1 id=eq.0h11v.s8.b3d0b4d77cbc from=seed src=0 shape=0d6100ff vocab=07bc22eb
-/
@[simp]
lemma reindexₗ_apply {l o : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    {eₘ : m ≃ l} {eₙ : n ≃ o} {M : CStarMatrix m n A} {i : l} {j : o} :
    reindexₗ R A eₘ eₙ M i j = Matrix.reindex eₘ eₙ M i j := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The natural map that reindexes a matrix's rows and columns with equivalent types is an
equivalence. -/
def reindexₐ (R) (A) [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A] [Module R A]
    [Star A] (e : m ≃ n) : CStarMatrix m m A ≃⋆ₐ[R] CStarMatrix n n A :=
  { reindexₗ R A e e with
    map_mul' M N := by
      ext i j
      simp only [mul_apply]
      refine Fintype.sum_equiv e _ _ ?_
      intro k
      simp
    map_star' M := by
      ext
      unfold reindexₗ
      dsimp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe, Matrix.reindex_symm, AddHom.toFun_eq_coe,
        AddHom.coe_mk, Matrix.reindex_apply, Matrix.submatrix_apply]
      rw [star_apply, star_apply]
      simp [Matrix.submatrix_apply] }

/--
@isnad1 id=eq.0h8v.s8.6a1dbd2cc37b from=seed src=0 shape=98905699 vocab=af91de63
-/
@[simp]
lemma reindexₐ_apply [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A] [Star A]
    [Module R A] {e : m ≃ n} {M : CStarMatrix m m A}
    {i : n} {j : n} : reindexₐ R A e M i j = Matrix.reindex e e M i j := rfl

/--
@isnad1 id=eq.0h8v.s9.cac2c02bc9e0 from=seed src=0 shape=af38b940 vocab=12f2ebca
-/
lemma mapₗ_reindexₐ [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A] [Module R A]
    [Star A] [AddCommMonoid B] [Mul B] [Module R B] [Star B] {e : m ≃ n} {M : CStarMatrix m m A}
    (φ : A →ₗ[R] B) : reindexₐ R B e (M.mapₗ φ) = ((reindexₐ R A e M).mapₗ φ) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h5v.s8.e047cd7ab810 from=seed src=0 shape=deff6f91 vocab=b5a79476
-/
@[simp]
lemma reindexₐ_symm [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A] [Module R A]
    [Star A] {e : m ≃ n} : reindexₐ R A e.symm = (reindexₐ R A e).symm := by
  simp [reindexₐ, reindexₗ]

set_option backward.isDefEq.respectTransparency.types false in
/-- Applying a non-unital ⋆-algebra homomorphism to every entry of a matrix is itself a
⋆-algebra homomorphism on matrices. -/
@[simps]
def mapₙₐ [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [Star A] [NonUnitalNonAssocSemiring B] [Module R B] [Star B] (f : A →⋆ₙₐ[R] B) :
    CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix n n B where
  toFun := fun M => M.mapₗ (f : A →ₗ[R] B)
  map_smul' := by simp
  map_zero' := by simp [map_zero]
  map_add' := by simp [map_add]
  map_mul' M N := by
    ext
    -- Un-squeezing this `simp` seems to add about half a second elaboration time.
    simp only [mapₗ_apply, map, LinearMap.coe_coe, ofMatrix_apply, mul_apply, map_sum, map_mul,
      ofMatrix_apply]
  map_star' M := by ext; simp [map, star_apply, map_star]

/--
@isnad1 id=eq.0h6v.s7.731d368bb73c from=seed src=0 shape=ab98c64e vocab=650b8cff
-/
theorem algebraMap_apply [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A]
    [Algebra R A] {r : R} {i j : n} :
    (algebraMap R (CStarMatrix n n A) r) i j = if i = j then algebraMap R A r else 0 := rfl

set_option backward.isDefEq.respectTransparency.types false in
variable (n) (R) (A) in
/-- The ⋆-algebra equivalence between `A` and 1×1 matrices with its entry in `A`. -/
def toOneByOne [Unique n] [Semiring R] [AddCommMonoid A] [Mul A] [Star A] [Module R A] :
    A ≃⋆ₐ[R] CStarMatrix n n A where
  toFun a := fun x y => a
  invFun M := M default default
  left_inv := by intro; simp
  right_inv := by
    intro
    ext i j
    simp [Subsingleton.elim i default, Subsingleton.elim j default]
  map_mul' _ _ := by ext; simp [mul_apply]
  map_add' _ _ := by ext; simp
  map_star' _ := by ext; simp [star_eq_conjTranspose]
  map_smul' _ _ := by ext; simp

end basic

variable [Fintype m] [NonUnitalCStarAlgebra A]

set_option backward.isDefEq.respectTransparency false in
/-- Interpret a `CStarMatrix m n A` as a continuous linear map acting on `C⋆ᵐᵒᵈ (n → A)`. -/
noncomputable def toCLM : CStarMatrix m n A →ₗ[ℂ] C⋆ᵐᵒᵈ(A, m → A) →L[ℂ] C⋆ᵐᵒᵈ(A, n → A) where
  toFun M := { toFun := (WithCStarModule.equivL ℂ).symm ∘ M.vecMul ∘ WithCStarModule.equivL ℂ
               map_add' := M.add_vecMul
               map_smul' := M.smul_vecMul }
  map_add' M₁ M₂ := by
    ext
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      WithCStarModule.equivL_apply, WithCStarModule.equivL_symm_apply,
      WithCStarModule.equiv_symm_pi_apply, _root_.add_apply, WithCStarModule.add_apply]
    rw [Matrix.vecMul_add, Pi.add_apply]
  map_smul' c M := by
    ext x i
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      WithCStarModule.equivL_apply, WithCStarModule.equivL_symm_apply,
      WithCStarModule.equiv_symm_pi_apply, _root_.smul_apply,
      WithCStarModule.smul_apply, RingHom.id_apply]
    rw [Matrix.vecMul_smul, Pi.smul_apply]

/--
@isnad1 id=eq.0h5v.s11.c1f0f2b08c3b from=seed src=0 shape=e77604bc vocab=8232e4b6
-/
lemma toCLM_apply {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, m → A)} :
    toCLM M v = (WithCStarModule.equiv _ _).symm (M.vecMul v) := rfl

/--
@isnad1 id=eq.0h5v.s11.74dd1f848001 from=seed src=0 shape=034070ee vocab=ca231413
-/
lemma toCLM_apply_eq_sum {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, m → A)} :
    toCLM M v = (WithCStarModule.equiv _ _).symm (fun j => ∑ i, v i * M i j) := by
  ext i
  simp [toCLM_apply, Matrix.vecMul, dotProduct]



set_option backward.isDefEq.respectTransparency false in
/-- Interpret a `CStarMatrix m n A` as a continuous linear map acting on `C⋆ᵐᵒᵈ (n → A)`. This
version is specialized to the case `m = n` and is bundled as a non-unital algebra homomorphism. -/
noncomputable def toCLMNonUnitalAlgHom [Fintype n] :
    CStarMatrix n n A →ₙₐ[ℂ] (C⋆ᵐᵒᵈ(A, n → A) →L[ℂ] C⋆ᵐᵒᵈ(A, n → A))ᵐᵒᵖ :=
  { (MulOpposite.opLinearEquiv ℂ).toLinearMap ∘ₗ (toCLM (n := n) (m := n)) with
    map_zero' := by simp
    map_mul' := by
      intros
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp,
        LinearEquiv.coe_coe, MulOpposite.coe_opLinearEquiv, Function.comp_apply,
        ← MulOpposite.op_mul, MulOpposite.op_inj]
      ext
      simp [toCLM] }

/--
@isnad1 id=eq.0h3v.s13.3041a6259ccb from=seed src=0 shape=a5bb4093 vocab=a724c514
-/
lemma toCLMNonUnitalAlgHom_eq_toCLM [Fintype n] {M : CStarMatrix n n A} :
    toCLMNonUnitalAlgHom (A := A) M = MulOpposite.op (toCLM M) := rfl

set_option backward.isDefEq.respectTransparency false in
open WithCStarModule in
/--
@isnad1 id=eq.0h6v.s11.0abdf718fb8c from=seed src=0 shape=9bdd4501 vocab=04a1fa8d
-/
@[simp high]
lemma toCLM_apply_single [DecidableEq m] {M : CStarMatrix m n A} {i : m} (a : A) :
    (toCLM M) (equiv _ _ |>.symm <| Pi.single i a) = (equiv _ _).symm (fun j => a * M i j) := by
  ext
  simp [toCLM_apply, equiv, Equiv.refl]

open WithCStarModule in
/--
@isnad1 id=eq.0h7v.s11.1589027da3e7 from=seed src=0 shape=107cd9f8 vocab=04a1fa8d
-/
lemma toCLM_apply_single_apply [DecidableEq m] {M : CStarMatrix m n A} {i : m} {j : n} (a : A) :
    (toCLM M) (equiv _ _ |>.symm <| Pi.single i a) j = a * M i j := by simp

/--
@isnad1 id=injectiv.0h3v.s11.6ce2cfad1608 from=seed src=0 shape=404b764c vocab=d7fd795c
-/
lemma toCLM_injective : Function.Injective (toCLM (A := A) (m := m) (n := n)) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro M h
  ext i j
  rw [zero_apply, ← norm_eq_zero, ← sq_eq_zero_iff, sq, ← CStarRing.norm_star_mul_self,
    ← toCLM_apply_single_apply]
  simp [h]

variable [PartialOrder A] [StarOrderedRing A]

open WithCStarModule in
/--
@isnad1 id=eq.0h8v.s11.bc66331dbd09 from=seed src=0 shape=0a7a7a93 vocab=3a9b22ad
-/
lemma mul_entry_mul_eq_inner_toCLM [Fintype n] [DecidableEq m] [DecidableEq n]
    {M : CStarMatrix m n A} {i : m} {j : n} (a b : A) :
    a * M i j * star b
      = ⟪equiv _ _ |>.symm (Pi.single j b), toCLM M (equiv _ _ |>.symm <| Pi.single i a)⟫_A := by
  simp [mul_assoc, inner_def]

variable [Fintype n]

set_option backward.isDefEq.respectTransparency.types false in
open WithCStarModule in
/--
@isnad1 id=eq.0h6v.s12.67e31bc21a32 from=seed src=0 shape=4a7b4393 vocab=c4a09805
-/
lemma inner_toCLM_conjTranspose_left {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, n → A)}
    {w : C⋆ᵐᵒᵈ(A, m → A)} : ⟪toCLM Mᴴ v, w⟫_A = ⟪v, toCLM M w⟫_A := by
  simp only [toCLM_apply_eq_sum, pi_inner, equiv_symm_pi_apply, inner_def, Finset.mul_sum,
    Matrix.conjTranspose_apply, star_sum, star_mul, star_star, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h6v.s12.610356f56f30 from=seed src=0 shape=088dd154 vocab=c4a09805
-/
lemma inner_toCLM_conjTranspose_right {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, m → A)}
    {w : C⋆ᵐᵒᵈ(A, n → A)} : ⟪v, toCLM Mᴴ w⟫_A = ⟪toCLM M v, w⟫_A := by
  apply Eq.symm
  simpa using inner_toCLM_conjTranspose_left (M := Mᴴ) (v := v) (w := w)

/-- The operator norm on `CStarMatrix m n A`. -/
noncomputable instance instNorm : Norm (CStarMatrix m n A) where
  norm M := ‖toCLM M‖

/--
@isnad1 id=eq.0h4v.s11.6a6da1fc9769 from=seed src=0 shape=7a3cf085 vocab=1762ca8c
-/
lemma norm_def {M : CStarMatrix m n A} : ‖M‖ = ‖toCLM M‖ := rfl

/--
@isnad1 id=eq.0h3v.s12.8065028b1cd7 from=seed src=0 shape=32bff863 vocab=6b18de5e
-/
lemma norm_def' {M : CStarMatrix n n A} : ‖M‖ = ‖toCLMNonUnitalAlgHom (A := A) M‖ := rfl

/--
@isnad1 id=core.0h3v.s6.0d254e442e81 from=seed src=0 shape=ca9ed410 vocab=37c7c9af
-/
lemma normedSpaceCore : NormedSpace.Core ℂ (CStarMatrix m n A) where
  norm_nonneg M := (toCLM M).opNorm_nonneg
  norm_smul c M := by rw [norm_def, norm_def, map_smul, norm_smul _ (toCLM M)]
  norm_triangle M₁ M₂ := by simpa [← map_add] using! norm_add_le (toCLM M₁) (toCLM M₂)
  norm_eq_zero_iff := by
    simpa only [norm_def, norm_eq_zero, ← injective_iff_map_eq_zero'] using! toCLM_injective

open WithCStarModule in
/--
@isnad1 id=le.0h6v.s6.48a6c2d82a2d from=seed src=0 shape=155c5ea9 vocab=5686321f
-/
lemma norm_entry_le_norm {M : CStarMatrix m n A} {i : m} {j : n} :
    ‖M i j‖ ≤ ‖M‖ := by
  classical
  suffices ‖M i j‖ * ‖M i j‖ ≤ ‖M‖ * ‖M i j‖ by
    obtain (h | h) := eq_zero_or_norm_pos (M i j)
    · simp [h, norm_def]
    · exact le_of_mul_le_mul_right this h
  rw [← CStarRing.norm_star_mul_self, ← toCLM_apply_single_apply]
  apply norm_apply_le_norm _ _ |>.trans
  apply (toCLM M).le_opNorm _ |>.trans
  simp [norm_def]

open CStarModule in
/--
@isnad1 id=le.1h5v.s11.106d8a9bffc3 from=seed src=0 shape=c81a9bfb vocab=d09b602c
-/
lemma norm_le_of_forall_inner_le {M : CStarMatrix m n A} {C : ℝ≥0}
    (h : ∀ v w, ‖⟪w, toCLM M v⟫_A‖ ≤ C * ‖v‖ * ‖w‖) : ‖M‖ ≤ C := by
  refine (toCLM M).opNorm_le_bound (by simp) fun v ↦ ?_
  obtain (h₀ | h₀) := (norm_nonneg (toCLM M v)).eq_or_lt
  · rw [← h₀]
    positivity
  · refine le_of_mul_le_mul_right ?_ h₀
    simpa [← sq, norm_sq_eq A] using h ..

end CStarMatrix

section TopologyAux
/-
## Replacing the uniformity and bornology

Note that while the norm that we have defined on `CStarMatrix m n A` induces the product uniformity,
it is not defeq to `Pi.uniformSpace`. In this section, we show that the norm indeed does induce
the product topology and use this fact to properly set up the
`NormedAddCommGroup (CStarMatrix m n A)` instance such that the uniformity is still
`Pi.uniformSpace` and the bornology is `Pi.instBornology`.

To do this, we locally register a `NormedAddCommGroup` instance on `CStarMatrix` which registers
the "bad" topology, and we also locally use the matrix norm `Matrix.normedAddCommGroup`
(which takes the norm of the biggest entry as the norm of the matrix)
in order to show that the map `ofMatrix` is bilipschitz. We then finally register the
`NormedAddCommGroup (C⋆ᵐᵒᵈ (n → A))` instance via `NormedAddCommGroup.ofCoreReplaceAll`.
-/

namespace CStarMatrix

variable {m n A : Type*} [Fintype m] [Fintype n]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private noncomputable local instance normedAddCommGroupAux :
    NormedAddCommGroup (CStarMatrix m n A) :=
  .ofCore CStarMatrix.normedSpaceCore

@[instance_reducible]
private noncomputable def normedSpaceAux : NormedSpace ℂ (CStarMatrix m n A) :=
  .ofCore CStarMatrix.normedSpaceCore

/- In this `Aux` section, we locally activate the following instances: a norm on `CStarMatrix`
which induces a topology that is not defeq with the matrix one, and the elementwise norm on
matrices, in order to show that the two topologies are in fact equal -/
open scoped Matrix.Norms.Elementwise

private lemma nnnorm_le_of_forall_inner_le {M : CStarMatrix m n A} {C : ℝ≥0}
    (h : ∀ v w, ‖⟪w, CStarMatrix.toCLM M v⟫_A‖₊ ≤ C * ‖v‖₊ * ‖w‖₊) : ‖M‖₊ ≤ C :=
  CStarMatrix.norm_le_of_forall_inner_le fun v w => h v w

open Finset in
private lemma lipschitzWith_toMatrixAux :
    LipschitzWith 1 (ofMatrixₗ.symm (R := ℂ) : CStarMatrix m n A → Matrix m n A) := by
  refine AddMonoidHomClass.lipschitz_of_bound_nnnorm _ _ fun M => ?_
  rw [one_mul, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Matrix.norm_le_iff (norm_nonneg _)]
  exact fun _ _ ↦ CStarMatrix.norm_entry_le_norm

open CStarMatrix WithCStarModule in
private lemma antilipschitzWith_toMatrixAux :
    AntilipschitzWith (Fintype.card n * Fintype.card m)
      (ofMatrixₗ.symm (R := ℂ) : CStarMatrix m n A → Matrix m n A) := by
  refine AddMonoidHomClass.antilipschitz_of_bound _ fun M => ?_
  calc
    ‖M‖ ≤ ∑ j, ∑ i, ‖M i j‖ := by
      rw [norm_def]
      refine (toCLM M).opNorm_le_bound (by positivity) fun v => ?_
      simp only [toCLM_apply_eq_sum, Finset.sum_mul]
      apply pi_norm_le_sum_norm _ |>.trans
      gcongr with i _
      apply norm_sum_le _ _ |>.trans
      gcongr with j _
      apply norm_mul_le _ _ |>.trans
      rw [mul_comm]
      gcongr
      exact norm_apply_le_norm v j
    _ ≤ ∑ _ : n, ∑ _ : m, ‖ofMatrixₗ.symm (R := ℂ) M‖ := by
      gcongr with j _ i _
      exact ofMatrixₗ.symm (R := ℂ) M |>.norm_entry_le_entrywise_sup_norm
    _ = _ := by simp [mul_assoc]

private lemma uniformInducing_toMatrixAux :
    IsUniformInducing (ofMatrix.symm : CStarMatrix m n A → Matrix m n A) :=
  AntilipschitzWith.isUniformInducing antilipschitzWith_toMatrixAux
    lipschitzWith_toMatrixAux.uniformContinuous

set_option backward.isDefEq.respectTransparency false in
private lemma uniformity_eq_aux :
    𝓤 (CStarMatrix m n A) = (𝓤[Pi.uniformSpace _] :
      Filter (CStarMatrix m n A × CStarMatrix m n A)) := by
  have :
    (fun x : CStarMatrix m n A × CStarMatrix m n A => ⟨ofMatrix.symm x.1, ofMatrix.symm x.2⟩)
      = id := by
    ext i <;> rfl
  rw [← uniformInducing_toMatrixAux.comap_uniformity, this, Filter.comap_id]
  rfl

open Bornology in
private lemma cobounded_eq_aux :
    cobounded (CStarMatrix m n A) = @cobounded _ Pi.instBornology := by
  have : cobounded (CStarMatrix m n A) = Filter.comap ofMatrix.symm (cobounded _) := by
    refine le_antisymm ?_ ?_
    · exact antilipschitzWith_toMatrixAux.tendsto_cobounded.le_comap
    · exact lipschitzWith_toMatrixAux.comap_cobounded_le
  exact this.trans Filter.comap_id

end CStarMatrix

end TopologyAux

namespace CStarMatrix

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m n : Type*} [Fintype m] [Fintype n]

instance instTopologicalSpace : TopologicalSpace (CStarMatrix m n A) :=
  inferInstanceAs <| TopologicalSpace (Matrix m n A)

instance instUniformSpace : UniformSpace (CStarMatrix m n A) :=
  inferInstanceAs <| UniformSpace (Matrix m n A)

-- TODO: we are missing `Bornology (Matrix m n A)`
instance instBornology : Bornology (CStarMatrix m n A) :=
  inferInstanceAs <| Bornology (m → n → A)

/--
@isnad1 id=complete.0h3v.s4.ef2b4728df96 from=seed src=0 shape=556cd1ae vocab=f7540e80
-/
instance instCompleteSpace : CompleteSpace (CStarMatrix m n A) :=
  inferInstanceAs <| CompleteSpace (Matrix m n A)

/--
@isnad1 id=t2space.0h3v.s4.2c2b1dd065c1 from=seed src=0 shape=556cd1ae vocab=22f676d0
-/
instance instT2Space : T2Space (CStarMatrix m n A) := inferInstanceAs <| T2Space (Matrix m n A)
/--
@isnad1 id=t3space.0h3v.s4.301759be9b25 from=seed src=0 shape=556cd1ae vocab=61b8e5e1
-/
instance instT3Space : T3Space (CStarMatrix m n A) := inferInstanceAs <| T3Space (Matrix m n A)


/--
@isnad1 id=istopolo.0h3v.s5.3e022e67d5fb from=seed src=0 shape=556cd1ae vocab=56a82e8f
-/
instance instIsTopologicalAddGroup : IsTopologicalAddGroup (CStarMatrix m n A) :=
  inferInstanceAs <| IsTopologicalAddGroup (Matrix m n A)

/--
@isnad1 id=isunifor.0h3v.s5.aa64265244aa from=seed src=0 shape=556cd1ae vocab=9b7ae4fc
-/
instance instIsUniformAddGroup : IsUniformAddGroup (CStarMatrix m n A) :=
  inferInstanceAs <| IsUniformAddGroup (Matrix m n A)

/--
@isnad1 id=continuo.0h4v.s5.57cfe0f86dd4 from=seed src=0 shape=ddb0c666 vocab=16def681
-/
instance instContinuousSMul {R : Type*} [SMul R A] [TopologicalSpace R] [ContinuousSMul R A] :
    ContinuousSMul R (CStarMatrix m n A) :=
  inferInstanceAs <| ContinuousSMul R (Matrix m n A)

noncomputable instance instNormedAddCommGroup :
    NormedAddCommGroup (CStarMatrix m n A) :=
  fast_instance% .ofCoreReplaceAll CStarMatrix.normedSpaceCore ?_ (fun _ ↦ ?_)
where finally
  exacts [CStarMatrix.uniformity_eq_aux.symm, Filter.ext_iff.1 CStarMatrix.cobounded_eq_aux.symm _]

noncomputable instance instNormedSpace : NormedSpace ℂ (CStarMatrix m n A) :=
  .ofCore CStarMatrix.normedSpaceCore

noncomputable instance instNonUnitalNormedRing :
    NonUnitalNormedRing (CStarMatrix n n A) where
  __ : NonUnitalRing (CStarMatrix n n A) := inferInstance
  __ : NormedAddCommGroup (CStarMatrix n n A) := inferInstance
  norm_mul_le _ _ := by simpa only [norm_def', map_mul] using norm_mul_le _ _

open ContinuousLinearMap CStarModule in
/-- Matrices with entries in a C⋆-algebra form a C⋆-algebra.
@isnad1 id=cstarrin.0h2v.s5.f797a34c0926 from=seed src=0 shape=14d46d25 vocab=63c3e367
-/
instance instCStarRing : CStarRing (CStarMatrix n n A) :=
  .of_le_norm_mul_star_self fun M ↦ by
    have hmain : ‖M‖ ≤ √‖M * star M‖ := by
      change ‖toCLM M‖ ≤ √‖M * star M‖
      rw [opNorm_le_iff (by positivity)]
      intro v
      rw [norm_eq_sqrt_norm_inner_self (A := A), ← inner_toCLM_conjTranspose_right]
      have h₁ : ‖⟪v, (toCLM Mᴴ) ((toCLM M) v)⟫_A‖ ≤ ‖M * star M‖ * ‖v‖ ^ 2 := calc
          _ ≤ ‖v‖ * ‖(toCLM Mᴴ) (toCLM M v)‖ := norm_inner_le (C⋆ᵐᵒᵈ(A, n → A))
          _ ≤ ‖v‖ * ‖(toCLM Mᴴ).comp (toCLM M)‖ * ‖v‖ := by
                    rw [mul_assoc]
                    gcongr
                    rw [← ContinuousLinearMap.comp_apply]
                    exact le_opNorm ((toCLM Mᴴ).comp (toCLM M)) v
          _ = ‖(toCLM Mᴴ).comp (toCLM M)‖ * ‖v‖ ^ 2 := by ring
          _ = ‖M * star M‖ * ‖v‖ ^ 2 := by
                    congr
                    apply MulOpposite.op_injective
                    simp only [← toCLMNonUnitalAlgHom_eq_toCLM, map_mul]
                    rfl
      have h₂ : ‖v‖ = √(‖v‖ ^ 2) := by simp
      rw [h₂, ← Real.sqrt_mul]
      · gcongr
      positivity
    rw [← Real.sqrt_le_sqrt_iff (by positivity)]
    simp [hmain]

/-- Matrices with entries in a non-unital C⋆-algebra form a non-unital C⋆-algebra. -/
noncomputable instance instNonUnitalCStarAlgebra :
    NonUnitalCStarAlgebra (CStarMatrix n n A) where
  smul_assoc x y z := by simp
  smul_comm m a b := (Matrix.mul_smul _ _ _).symm

noncomputable instance instPartialOrder :
    PartialOrder (CStarMatrix n n A) := CStarAlgebra.spectralOrder _
/--
@isnad1 id=starorde.0h2v.s6.36f4cbc4cdb3 from=seed src=0 shape=c1dbf869 vocab=5afe5442
-/
instance instStarOrderedRing :
    StarOrderedRing (CStarMatrix n n A) := CStarAlgebra.spectralOrderedRing _

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable instance instNormedRing : NormedRing (CStarMatrix n n A) where
  dist_eq _ _ := rfl
  norm_mul_le := norm_mul_le

noncomputable instance instNormedAlgebra : NormedAlgebra ℂ (CStarMatrix n n A) where
  norm_smul_le r M := by simpa only [norm_def, map_smul] using (toCLM M).opNorm_smul_le r

/-- Matrices with entries in a unital C⋆-algebra form a unital C⋆-algebra. -/
noncomputable instance instCStarAlgebra : CStarAlgebra (CStarMatrix n n A) where

end Unital

section

variable {m n A : Type*} [NonUnitalCStarAlgebra A]

/--
@isnad1 id=isunifor.0h3v.s6.86a5b7552ef2 from=seed src=0 shape=b69f0c69 vocab=4660345e
-/
lemma uniformEmbedding_ofMatrix :
    IsUniformEmbedding (ofMatrix : Matrix m n A → CStarMatrix m n A) where
  comap_uniformity := Filter.comap_id'
  injective := fun ⦃_ _⦄ a ↦ a

/-- `ofMatrix` bundled as a continuous linear equivalence. -/
def ofMatrixL : Matrix m n A ≃L[ℂ] CStarMatrix m n A :=
  { ofMatrixₗ with
    continuous_toFun := continuous_id
    continuous_invFun := continuous_id }

/--
@isnad1 id=eq.0h3v.s9.820867a6e958 from=seed src=0 shape=3f8ac861 vocab=1794f001
-/
lemma ofMatrix_eq_ofMatrixL :
    (ofMatrix : Matrix m n A → CStarMatrix m n A)
      = (ofMatrixL : Matrix m n A → CStarMatrix m n A) := rfl

end

end CStarMatrix

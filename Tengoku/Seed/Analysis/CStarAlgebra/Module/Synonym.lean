/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.RingTheory.Finiteness.Defs
public import Tengoku.Seed.Topology.Bornology.Constructions
public import Tengoku.Seed.Topology.UniformSpace.Equiv
public import Tengoku.Seed.Topology.Algebra.Module.Equiv
public import Tengoku.Seed.Topology.Algebra.IsUniformGroup.Constructions

/-! # Type synonym for types with a `CStarModule` structure

It is often the case that we want to construct a `CStarModule` instance on a type that is already
endowed with a norm, but this norm is not the one associated to its `CStarModule` structure. For
this reason, we create a type synonym `WithCStarModule` which is endowed with the requisite
`CStarModule` instance. We also introduce the scoped notation `C⋆ᵐᵒᵈ` for this type synonym.

The common use cases are, when `A` is a C⋆-algebra:

+ `E × F` where `E` and `F` are `CStarModule`s over `A`
+ `Π i, E i` where `E i` is a `CStarModule` over `A` and `i : ι` with `ι` a `Fintype`

In this way, the set up is very similar to the `WithLp` type synonym, although there is no way to
reuse `WithLp` because the norms *do not* coincide in general.

The `WithCStarModule` synonym is of vital importance, especially because the `CStarModule` class
marks `A` as an `outParam`. Indeed, we want to infer `A` from the type of `E`, but, as with modules,
a type `E` can be a `CStarModule` over different C⋆-algebras. For example, note that if `A` is a
C⋆-algebra, then so is `A × A`, and therefore we may consider both `A` and `A × A` as `CStarModule`s
over themselves, respectively. However, we may *also* consider `A × A` as a `CStarModule` over `A`.
However, by utilizing the type synonym, these actually correspond to *different types*, namely:

+ `A` as a `CStarModule` over `A` corresponds to `A`
+ `A × A` as a `CStarModule` over `A × A` corresponds to `A × A`
+ `A × A` as a `CStarModule` over `A` corresponds to `C⋆ᵐᵒᵈ (A × A)`

## Main definitions

* `WithCStarModule A E`: a copy of `E` to be equipped with a `CStarModule A` structure.
* `WithCStarModule.equiv A E`: the canonical equivalence between `WithCStarModule A E` and `E`.
* `WithCStarModule.linearEquiv ℂ A E`: the canonical `ℂ`-module isomorphism between
  `WithCStarModule A E` and `E`.

## Implementation notes

The pattern here is the same one as is used by `Lex` for order structures; it avoids having a
separate synonym for each type, and allows all the structure-copying code to be shared.
-/

@[expose] public section

set_option linter.unusedVariables false in
/-- A type synonym for endowing a given type with a `CStarModule` structure. This has the scoped
notation `C⋆ᵐᵒᵈ`. -/
@[nolint unusedArguments]
def WithCStarModule (A E : Type*) := E

namespace WithCStarModule

@[inherit_doc]
scoped notation "C⋆ᵐᵒᵈ(" A ", " E ")" => WithCStarModule A E

section Basic

variable (R R' A E : Type*)

/-- The canonical equivalence between `C⋆ᵐᵒᵈ(A, E)` and `E`. This should always be used to
convert back and forth between the representations. -/
def equiv : WithCStarModule A E ≃ E := Equiv.refl _

/--
@isnad1 id=nontrivi.0h2v.s3.a3dfc0c2bf8d from=seed src=0 shape=1b04a93b vocab=463e4545
-/
instance instNontrivial [Nontrivial E] : Nontrivial C⋆ᵐᵒᵈ(A, E) := ‹Nontrivial E›
instance instInhabited [Inhabited E] : Inhabited C⋆ᵐᵒᵈ(A, E) := ‹Inhabited E›
/--
@isnad1 id=nonempty.0h2v.s3.76b1a24a2ecb from=seed src=0 shape=1b04a93b vocab=0186e74e
-/
instance instNonempty [Nonempty E] : Nonempty C⋆ᵐᵒᵈ(A, E) := ‹Nonempty E›
instance instUnique [Unique E] : Unique C⋆ᵐᵒᵈ(A, E) := ‹Unique E›

/-! ## `C⋆ᵐᵒᵈ(A, E)` inherits various module-adjacent structures from `E`. -/

instance instZero [Zero E] : Zero C⋆ᵐᵒᵈ(A, E) := ‹Zero E›
instance instAdd [Add E] : Add C⋆ᵐᵒᵈ(A, E) := ‹Add E›
instance instSub [Sub E] : Sub C⋆ᵐᵒᵈ(A, E) := ‹Sub E›
instance instNeg [Neg E] : Neg C⋆ᵐᵒᵈ(A, E) := ‹Neg E›
instance instAddMonoid [AddMonoid E] : AddMonoid C⋆ᵐᵒᵈ(A, E) := ‹AddMonoid E›
instance instSubNegMonoid [SubNegMonoid E] : SubNegMonoid C⋆ᵐᵒᵈ(A, E) := ‹SubNegMonoid E›
instance instSubNegZeroMonoid [SubNegZeroMonoid E] : SubNegZeroMonoid C⋆ᵐᵒᵈ(A, E) :=
  ‹SubNegZeroMonoid E›

instance instAddCommGroup [AddCommGroup E] : AddCommGroup C⋆ᵐᵒᵈ(A, E) := ‹AddCommGroup E›

instance instSMul {R : Type*} [SMul R E] : SMul R C⋆ᵐᵒᵈ(A, E) := ‹SMul R E›

instance instModule {R : Type*} [Semiring R] [AddCommGroup E] [Module R E] :
    Module R C⋆ᵐᵒᵈ(A, E) :=
  ‹Module R E›

/--
@isnad1 id=isscalar.0h4v.s5.7e3024681e98 from=seed src=0 shape=22382e3b vocab=a357c56a
-/
instance instIsScalarTower [SMul R R'] [SMul R E] [SMul R' E]
    [IsScalarTower R R' E] : IsScalarTower R R' C⋆ᵐᵒᵈ(A, E) :=
  ‹IsScalarTower R R' E›

/--
@isnad1 id=smulcomm.0h4v.s5.7207b78d6652 from=seed src=0 shape=f6dab5de vocab=b11c0cdb
-/
instance instSMulCommClass [SMul R E] [SMul R' E] [SMulCommClass R R' E] :
    SMulCommClass R R' C⋆ᵐᵒᵈ(A, E) :=
  ‹SMulCommClass R R' E›

section Equiv

variable {R A E}
variable [SMul R E] (c : R) (x y : C⋆ᵐᵒᵈ(A, E)) (x' y' : E)

/-! `WithCStarModule.equiv` preserves the module structure. -/

section AddCommGroup

variable [AddCommGroup E]

/--
@isnad1 id=eq.0h2v.s6.fe22f0a55007 from=seed src=0 shape=846e3a90 vocab=0f15cd21
-/
@[simp]
theorem equiv_zero : equiv A E 0 = 0 :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.0965c2a1b783 from=seed src=0 shape=a38afcd5 vocab=dec18d5e
-/
@[simp]
theorem equiv_symm_zero : (equiv A E).symm 0 = 0 :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.d42f4ca8541f from=seed src=0 shape=a01a8fb4 vocab=832d711c
-/
@[simp]
theorem equiv_add : equiv A E (x + y) = equiv A E x + equiv A E y :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.4e12bfdbebe8 from=seed src=0 shape=8a769d0e vocab=edd184c6
-/
@[simp]
theorem equiv_symm_add :
    (equiv A E).symm (x' + y') = (equiv A E).symm x' + (equiv A E).symm y' :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.4e95ae8e762d from=seed src=0 shape=a01a8fb4 vocab=dcc433c1
-/
@[simp]
theorem equiv_sub : equiv A E (x - y) = equiv A E x - equiv A E y :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.7884d04a2163 from=seed src=0 shape=8a769d0e vocab=e0f5099e
-/
@[simp]
theorem equiv_symm_sub :
    (equiv A E).symm (x' - y') = (equiv A E).symm x' - (equiv A E).symm y' :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.e85d22d50dea from=seed src=0 shape=867824b5 vocab=af61ab05
-/
@[simp]
theorem equiv_neg : equiv A E (-x) = -equiv A E x :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.6e806569725d from=seed src=0 shape=51828862 vocab=a4e67596
-/
@[simp]
theorem equiv_symm_neg : (equiv A E).symm (-x') = -(equiv A E).symm x' :=
  rfl

end AddCommGroup

/--
@isnad1 id=eq.0h5v.s6.07874f95a673 from=seed src=0 shape=4db1d99d vocab=ae4438a0
-/
@[simp]
theorem equiv_smul : equiv A E (c • x) = c • equiv A E x :=
  rfl

/--
@isnad1 id=eq.0h5v.s6.be0084b1bf98 from=seed src=0 shape=f28434a1 vocab=74d2c5fa
-/
@[simp]
theorem equiv_symm_smul : (equiv A E).symm (c • x') = c • (equiv A E).symm x' :=
  rfl

end Equiv

/-- `WithCStarModule.equiv` as an additive equivalence. -/
def addEquiv [AddCommGroup E] : C⋆ᵐᵒᵈ(A, E) ≃+ E :=
  { AddEquiv.refl _ with
    toFun := equiv _ _
    invFun := (equiv _ _).symm }

/-- `WithCStarModule.equiv` as a linear equivalence. -/
@[simps -fullyApplied]
def linearEquiv [Semiring R] [AddCommGroup E] [Module R E] : C⋆ᵐᵒᵈ(A, E) ≃ₗ[R] E :=
  { LinearEquiv.refl _ _ with
    toFun := equiv _ _
    invFun := (equiv _ _).symm }

/--
@isnad1 id=eq.0h3v.s7.b61758d68788 from=seed src=0 shape=f84f4e6e vocab=5b32ab18
-/
lemma map_top_submodule {R : Type*} [Semiring R] [AddCommGroup E] [Module R E] :
    (⊤ : Submodule R E).map (linearEquiv R A E).symm.toLinearMap = ⊤ :=
  Submodule.map_eq_top_iff.mpr rfl

/--
@isnad1 id=finite.0h3v.s5.fe3db693b542 from=seed src=0 shape=75ad1c08 vocab=d57282d7
-/
instance instModuleFinite [Semiring R] [AddCommGroup E] [Module R E] [Module.Finite R E] :
    Module.Finite R C⋆ᵐᵒᵈ(A, E) := ‹Module.Finite R E›

/-! ## `C⋆ᵐᵒᵈ(A, E)` inherits the uniformity and bornology from `E`. -/

variable {A E}

instance [u : UniformSpace E] : UniformSpace C⋆ᵐᵒᵈ(A, E) := u.comap <| equiv A E

instance [Bornology E] : Bornology C⋆ᵐᵒᵈ(A, E) := Bornology.induced <| equiv A E


/-- `WithCStarModule.equiv` as a uniform equivalence between `C⋆ᵐᵒᵈ(A, E)` and `E`. -/
def uniformEquiv [UniformSpace E] : C⋆ᵐᵒᵈ(A, E) ≃ᵤ E :=
  equiv A E |>.toUniformEquivOfIsUniformInducing ⟨rfl⟩

/-- `WithCStarModule.equiv` as a continuous linear equivalence between `C⋆ᵐᵒᵈ E` and `E`. -/
@[simps! apply symm_apply]
def equivL [Semiring R] [AddCommGroup E] [UniformSpace E] [Module R E] : C⋆ᵐᵒᵈ(A, E) ≃L[R] E :=
  { linearEquiv R A E with
    continuous_toFun := UniformEquiv.continuous uniformEquiv
    continuous_invFun := UniformEquiv.continuous uniformEquiv.symm }

instance [UniformSpace E] [CompleteSpace E] : CompleteSpace C⋆ᵐᵒᵈ(A, E) :=
  uniformEquiv.completeSpace_iff.mpr inferInstance

instance [AddCommGroup E] [UniformSpace E] [ContinuousAdd E] : ContinuousAdd C⋆ᵐᵒᵈ(A, E) :=
  ContinuousAdd.induced (addEquiv A E)

instance [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] : IsUniformAddGroup C⋆ᵐᵒᵈ(A, E) :=
  IsUniformAddGroup.comap (addEquiv A E)

instance [Semiring R] [TopologicalSpace R] [AddCommGroup E] [UniformSpace E] [Module R E]
    [ContinuousSMul R E] : ContinuousSMul R C⋆ᵐᵒᵈ(A, E) :=
  ContinuousSMul.induced (linearEquiv R A E)

end Basic

/-! ## Prod

Register simplification lemmas for the applications of `WithCStarModule (E × F)` elements, as
the usual lemmas for `Prod` will not trigger. -/

section Prod

variable {R A E F : Type*}
variable [SMul R E] [SMul R F]
variable (x y : C⋆ᵐᵒᵈ(A, E × F)) (c : R)

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F]

/--
@isnad1 id=eq.0h3v.s6.56ab20c48b86 from=seed src=0 shape=47a8b5b5 vocab=d425270c
-/
@[simp]
theorem zero_fst : (0 : C⋆ᵐᵒᵈ(A, E × F)).fst = 0 :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.d6be843f0033 from=seed src=0 shape=19efc848 vocab=d4ba2be1
-/
@[simp]
theorem zero_snd : (0 : C⋆ᵐᵒᵈ(A, E × F)).snd = 0 :=
  rfl

/--
@isnad1 id=eq.0h5v.s6.65c3ae2ff9a4 from=seed src=0 shape=00a0d81f vocab=79e17ae7
-/
@[simp]
theorem add_fst : (x + y).fst = x.fst + y.fst :=
  rfl

/--
@isnad1 id=eq.0h5v.s6.72f1aea5f564 from=seed src=0 shape=17ccc725 vocab=b6201358
-/
@[simp]
theorem add_snd : (x + y).snd = x.snd + y.snd :=
  rfl

/--
@isnad1 id=eq.0h5v.s6.4e5c1a0f52df from=seed src=0 shape=00a0d81f vocab=90985987
-/
@[simp]
theorem sub_fst : (x - y).fst = x.fst - y.fst :=
  rfl

/--
@isnad1 id=eq.0h5v.s6.75df728bd0a4 from=seed src=0 shape=17ccc725 vocab=df06cabe
-/
@[simp]
theorem sub_snd : (x - y).snd = x.snd - y.snd :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.1a8191c0cd89 from=seed src=0 shape=fafcc7ba vocab=c5d13560
-/
@[simp]
theorem neg_fst : (-x).fst = -x.fst :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.3c37ba96c6f1 from=seed src=0 shape=f644c2db vocab=6f278275
-/
@[simp]
theorem neg_snd : (-x).snd = -x.snd :=
  rfl

end AddCommGroup

/--
@isnad1 id=eq.0h6v.s6.8be9ecb29514 from=seed src=0 shape=55f798b9 vocab=e10e7ebe
-/
@[simp]
theorem smul_fst : (c • x).fst = c • x.fst :=
  rfl

/--
@isnad1 id=eq.0h6v.s6.4862b684282f from=seed src=0 shape=54168014 vocab=0ab6d4bd
-/
@[simp]
theorem smul_snd : (c • x).snd = c • x.snd :=
  rfl

/-! Note that the unapplied versions of these lemmas are deliberately omitted, as they break
the use of the type synonym. -/

/--
@isnad1 id=eq.0h4v.s6.934e548c63ef from=seed src=0 shape=a428dde4 vocab=13228b0d
-/
@[simp]
theorem equiv_fst (x : C⋆ᵐᵒᵈ(A, E × F)) : (equiv A (E × F) x).fst = x.fst :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.65c5901f1c32 from=seed src=0 shape=1dde185d vocab=8a2d3c8f
-/
@[simp]
theorem equiv_snd (x : C⋆ᵐᵒᵈ(A, E × F)) : (equiv A (E × F) x).snd = x.snd :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.dfbf30b7f2ef from=seed src=0 shape=f4baa5df vocab=dc278f50
-/
@[simp]
theorem equiv_symm_fst (x : E × F) : ((equiv A (E × F)).symm x).fst = x.fst :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.b55f493f954f from=seed src=0 shape=74054d7a vocab=943c1aca
-/
@[simp]
theorem equiv_symm_snd (x : E × F) : ((equiv A (E × F)).symm x).snd = x.snd :=
  rfl

end Prod

/-! ## Pi

Register simplification lemmas for the applications of `WithCStarModule (Π i, E i)` elements, as
the usual lemmas for `Pi` will not trigger.

We also provide a `CoeFun` instance for `WithCStarModule (Π i, E i)`. -/

section Pi

/-- The following should not be a `FunLike` instance because then the coercion `⇑` would get
unfolded to `FunLike.coe` instead of `WithCStarModule.equiv`. -/
instance {A ι : Type*} (E : ι → Type*) : CoeFun (C⋆ᵐᵒᵈ(A, Π i, E i)) (fun _ ↦ Π i, E i) where
  coe := equiv _ _

/--
@isnad1 id=eq.1h5v.s5.6b9672b777d8 from=seed src=0 shape=a6e04081 vocab=7f69c984
-/
@[ext]
protected theorem ext {A ι : Type*} {E : ι → Type*} {x y : C⋆ᵐᵒᵈ(A, Π i, E i)}
    (h : ∀ i, x i = y i) : x = y :=
  funext h

variable {R A ι : Type*} {E : ι → Type*}
variable [∀ i, SMul R (E i)]
variable (c : R) (x y : C⋆ᵐᵒᵈ(A, Π i, E i)) (i : ι)

section AddCommGroup

variable [∀ i, AddCommGroup (E i)]

/--
@isnad1 id=eq.0h4v.s6.30e5282743a2 from=seed src=0 shape=d8e3e9ff vocab=67158994
-/
@[simp]
theorem zero_apply : (0 : C⋆ᵐᵒᵈ(A, Π i, E i)) i = 0 :=
  rfl

/--
@isnad1 id=eq.0h6v.s7.0c2566661341 from=seed src=0 shape=fc6a2faf vocab=c771adc9
-/
@[simp]
theorem add_apply : (x + y) i = x i + y i :=
  rfl

/--
@isnad1 id=eq.0h6v.s7.a4e21b0a2b66 from=seed src=0 shape=fc6a2faf vocab=6b24cbfa
-/
@[simp]
theorem sub_apply : (x - y) i = x i - y i :=
  rfl

/--
@isnad1 id=eq.0h5v.s6.6bd7d7fbb604 from=seed src=0 shape=dba87af7 vocab=de684a04
-/
@[simp]
theorem neg_apply : (-x) i = -x i :=
  rfl

end AddCommGroup

/--
@isnad1 id=eq.0h7v.s6.f7f06a2835cf from=seed src=0 shape=86748bb5 vocab=fca5dacd
-/
@[simp]
theorem smul_apply : (c • x) i = c • x i :=
  rfl

/-! Note that the unapplied versions of these lemmas are deliberately omitted, as they break
the use of the type synonym. -/

/--
@isnad1 id=eq.0h5v.s6.38a5d93e9d09 from=seed src=0 shape=853935f3 vocab=d2c04596
-/
@[simp]
theorem equiv_pi_apply (i : ι) : equiv _ _ x i = x i :=
  rfl

/--
@isnad1 id=eq.0h5v.s6.2d2bfb2ad2e9 from=seed src=0 shape=e918092d vocab=9089241f
-/
@[simp]
theorem equiv_symm_pi_apply (x : ∀ i, E i) (i : ι) :
    (equiv A _).symm x i = x i :=
  rfl

end Pi

end WithCStarModule

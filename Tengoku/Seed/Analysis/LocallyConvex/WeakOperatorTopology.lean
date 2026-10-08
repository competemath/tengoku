/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Algebra.TransferInstance
public import Tengoku.Seed.Analysis.LocallyConvex.WithSeminorms
public import Tengoku.Seed.Analysis.LocallyConvex.SeparatingDual
public import Tengoku.Seed.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# The weak operator topology

This file defines a type copy of `E →L[𝕜] F` (where `E` and `F` are topological vector spaces)
which is endowed with the weak operator topology (WOT) rather than the topology of bounded
convergence (which is the usual one induced by the operator norm in the normed setting).
The WOT is defined as the coarsest topology such that the functional `fun A => y (A x)` is
continuous for any `x : E` and `y : StrongDual 𝕜 F`. Equivalently, a function `f` tends to
`A : E →WOT[𝕜] F` along filter `l` iff `y (f a x)` tends to `y (A x)` along the same filter.

Basic non-topological properties of `E →L[𝕜] F` (such as the module structure) are copied over to
the type copy.

We also prove that the WOT is induced by the family of seminorms `‖y (A x)‖` for `x : E` and
`y : StrongDual 𝕜 F`.

## Main declarations

* `ContinuousLinearMapWOT σ E F`: The type copy of `E →SL[σ] F` endowed with the weak operator
  topology.
* `ContinuousLinearMapWOT.tendsto_iff_forall_dual_apply_tendsto`: a function `f` tends to
  `A : E →WOT[𝕜] F` along filter `l` iff `y ((f a) x)` tends to `y (A x)` along the same filter.
* `ContinuousLinearMap.toWOT`: the inclusion map from `E →SL[σ] F` to the type copy
* `ContinuousLinearMap.continuous_toWOT`: the inclusion map is continuous, i.e. the WOT is coarser
  than the norm topology.
* `ContinuousLinearMapWOT.withSeminorms`: the WOT is induced by the family of seminorms
  `‖y (A x)‖` for `x : E` and `y : StrongDual 𝕜 F`.

## Notation

* The type copy of `E →L[𝕜] F` endowed with the weak operator topology is denoted by
  `E →WOT[𝕜] F` and the copy of `E →SL[σ] F` is denoted by `E →SWOT[σ] F`.
* We locally use the notation `F⋆` for `StrongDual 𝕜 F`.

## Implementation notes

In most of the literature, the WOT is defined on maps between Banach spaces. Here, we only assume
that the domain and codomains are topological vector spaces over a normed field.
-/

@[expose] public section

open Topology

/-- The type copy of `E →SL[σ] F` endowed with the weak operator topology, denoted as
`E →SWOT[σ] F`. Likewise, when `σ := RingHom.id 𝕜`, the notation `E →WOT[𝕜] F` is available. -/
structure ContinuousLinearMapWOT {𝕜₁ 𝕜₂ : Type*} [Semiring 𝕜₁] [Semiring 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂)
    (E F : Type*) [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E] [AddCommGroup F]
    [TopologicalSpace F] [Module 𝕜₂ F] where
  /-- Construct an element of `E →SWOT[σ] F` from a continuous linear map. -/
  ofCLM ::
  /-- The continuous linear map underlying an element of `E →SWOT[σ] F`. -/
  toCLM : E →SL[σ] F


namespace ContinuousLinearMapWOT

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `ofCLM A` being printed as `{ toCLM := x }` by `delabStructureInstance`. -/
@[app_delab ContinuousLinearMapWOT.ofCLM]
meta def delabOfCLM : Delab := delabApp

@[inherit_doc]
notation:25 E " →SWOT[" σ "] " F => ContinuousLinearMapWOT σ E F

@[inherit_doc]
notation:25 E " →WOT[" 𝕜 "] " F => ContinuousLinearMapWOT (RingHom.id 𝕜) E F

end Notation

variable {𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂]
  {σ : 𝕜₁ →+* 𝕜₂}
  {E F : Type*}
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜₂ F]

local notation X "⋆" => StrongDual 𝕜₂ X

/-!
### Basic properties common with `E →L[𝕜] F`

The section copies basic non-topological properties of `E →L[𝕜] F` over to `E →WOT[𝕜] F`, such as
the module structure, `FunLike`, etc.
-/
section Basic

/-- The equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap`. -/
@[simps]
def equiv : (E →SWOT[σ] F) ≃ (E →SL[σ] F) where
  toFun := toCLM
  invFun := ofCLM
  left_inv _ := rfl
  right_inv _ := rfl

/--
@isnad1 id=injectiv.0h5v.s7.d8421f381962 from=seed src=0 shape=c0e4053b vocab=23a8537c
-/
@[simp]
lemma toCLM_injective : Function.Injective (toCLM : (E →SWOT[σ] F) → E →SL[σ] F) :=
  equiv.injective

/--
@isnad1 id=surjecti.0h5v.s7.f8d4a0c24a59 from=seed src=0 shape=c0e4053b vocab=fbb4e8e1
-/
@[simp]
lemma toCLM_surjective : Function.Surjective (toCLM : (E →SWOT[σ] F) → E →SL[σ] F) :=
  equiv.surjective

/--
@isnad1 id=bijectiv.0h5v.s7.0127c047c39b from=seed src=0 shape=c0e4053b vocab=0734b1a1
-/
lemma toCLM_bijective : Function.Bijective (toCLM : (E →SWOT[σ] F) → E →SL[σ] F) :=
  equiv.bijective

/--
@isnad1 id=injectiv.0h5v.s7.f51b0921d5c3 from=seed src=0 shape=c0e4053b vocab=05473229
-/
@[simp]
lemma ofCLM_injective : Function.Injective (ofCLM : (E →SL[σ] F) → E →SWOT[σ] F) :=
  equiv.symm.injective

/--
@isnad1 id=surjecti.0h5v.s7.32eb54b1f29f from=seed src=0 shape=c0e4053b vocab=c967e711
-/
@[simp]
lemma ofCLM_surjective : Function.Surjective (ofCLM : (E →SL[σ] F) → E →SWOT[σ] F) :=
  equiv.symm.surjective

/--
@isnad1 id=bijectiv.0h5v.s7.24c7a6a248cb from=seed src=0 shape=c0e4053b vocab=a07297f4
-/
lemma ofCLM_bijective : Function.Bijective (ofCLM : (E →SL[σ] F) → E →SWOT[σ] F) :=
  equiv.symm.bijective

instance instAddCommGroup [IsTopologicalAddGroup F] :
    AddCommGroup (E →SWOT[σ] F) :=
  equiv.addCommGroup

/-- The additive group equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap`. -/
@[implicit_reducible, simps!]
def addEquiv [IsTopologicalAddGroup F] : (E →SWOT[σ] F) ≃+ (E →SL[σ] F) where
  __ := equiv
  map_add' _ _ := rfl

instance instSMul {S : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F] [ContinuousConstSMul S F] :
    SMul S (E →SWOT[σ] F) :=
  equiv.smul S

instance instModule {S : Type*} [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F]
    [ContinuousConstSMul S F] [IsTopologicalAddGroup F] :
    Module S (E →SWOT[σ] F) :=
  addEquiv.module S

/--
@isnad1 id=isscalar.0h7v.s9.fca6af135bc8 from=seed src=0 shape=1afad6a8 vocab=dcf75a94
-/
instance instIsScalarTower {S T : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F]
    [ContinuousConstSMul S F] [DistribSMul T F] [SMulCommClass 𝕜₂ T F]
    [ContinuousConstSMul T F] [SMul S T] [IsScalarTower S T F] :
    IsScalarTower S T (E →SWOT[σ] F) :=
  equiv.isScalarTower S T

/--
@isnad1 id=smulcomm.0h7v.s9.45633092f24e from=seed src=0 shape=cc7dc134 vocab=c8859a6a
-/
instance instSMulCommClass {S T : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F]
    [ContinuousConstSMul S F] [DistribSMul T F] [SMulCommClass 𝕜₂ T F]
    [ContinuousConstSMul T F] [SMulCommClass S T F] :
    SMulCommClass S T (E →SWOT[σ] F) :=
  equiv.smulCommClass S T

/--
@isnad1 id=iscentra.0h6v.s8.bb2e1d1b563a from=seed src=0 shape=0974136b vocab=ce9b4337
-/
instance instIsCentralScalar {S : Type*} [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F]
    [ContinuousConstSMul S F] [Module Sᵐᵒᵖ F] [IsCentralScalar S F] :
    IsCentralScalar S (E →SWOT[σ] F) :=
  equiv.isCentralScalar S

instance instRing [IsTopologicalAddGroup E] : Ring (E →WOT[𝕜₁] E) :=
  equiv.ring

instance instAlgebra {S : Type*} [CommSemiring S] [Module S E] [SMulCommClass 𝕜₁ S E] [SMul S 𝕜₁]
    [IsScalarTower S 𝕜₁ E] [ContinuousConstSMul S E] [IsTopologicalAddGroup E] :
    Algebra S (E →WOT[𝕜₁] E) :=
  equiv.algebra S

/-- The linear equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap`. -/
@[simps!]
def linearEquiv (S : Type*) [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F]
    [ContinuousConstSMul S F] [IsTopologicalAddGroup F] :
    (E →SWOT[σ] F) ≃ₗ[S] (E →SL[σ] F) :=
  (addEquiv (F := F)).linearEquiv S

/-- The ring equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap`. -/
@[simps!]
def ringEquiv [IsTopologicalAddGroup E] : (E →WOT[𝕜₁] E) ≃+* (E →L[𝕜₁] E) :=
  equiv.ringEquiv

/-- The algebra equivalence between `ContinuousLinearMapWOT` and `ContinuousLinearMap`. -/
@[simps!]
def algEquiv (S : Type*) [CommSemiring S] [Module S E] [SMulCommClass 𝕜₁ S E] [SMul S 𝕜₁]
    [IsScalarTower S 𝕜₁ E] [ContinuousConstSMul S E] [IsTopologicalAddGroup E] :
    (E →WOT[𝕜₁] E) ≃ₐ[S] (E →L[𝕜₁] E) :=
  equiv.algEquiv S

instance instFunLike : FunLike (E →SWOT[σ] F) E F where
  coe f := toCLM f
  coe_injective := DFunLike.coe_injective.comp toCLM_injective

/--
@isnad1 id=eq.0h6v.s8.629d699da334 from=seed src=0 shape=4bb8ba5c vocab=e67fdbd0
-/
@[simp]
lemma coe_toCLM (A : E →SWOT[σ] F) : ⇑(toCLM A : E →SL[σ] F) = A := rfl

/--
@isnad1 id=eq.0h6v.s8.7568893ebd96 from=seed src=0 shape=4bb8ba5c vocab=cb39e8d5
-/
@[simp]
lemma coe_ofCLM (A : E →SL[σ] F) : ⇑(ofCLM A : E →SWOT[σ] F) = A := rfl

/--
@isnad1 id=continuo.0h5v.s7.f0098141bfe0 from=seed src=0 shape=3db0e756 vocab=1d3fbb0c
-/
instance instContinuousLinearMapClass : ContinuousSemilinearMapClass (E →SWOT[σ] F) σ E F where
  map_add f x y := by simp [← coe_toCLM]
  map_smulₛₗ f r x := by simp [← coe_toCLM]
  map_continuous f := f.toCLM.continuous

/--
@isnad1 id=eq.0h6v.s7.d1a835015863 from=seed src=0 shape=dfd5feaa vocab=e8c1efbf
-/
@[simp]
lemma ofCLM_toCLM (A : E →SWOT[σ] F) : ofCLM (toCLM A) = A := rfl

-- not marked `simp` because Lean just sees `A` on the left-hand side
/--
@isnad1 id=eq.0h6v.s7.cca002074ab7 from=seed src=0 shape=dfd5feaa vocab=2802d763
-/
lemma toCLM_ofCLM (A : E →SL[σ] F) : toCLM (ofCLM A) = A := rfl

/--
@isnad1 id=eq.0h7v.s8.9837a373c0b6 from=seed src=0 shape=f709a91f vocab=e67fdbd0
-/
@[simp]
lemma toCLM_apply {A : E →SWOT[σ] F} {x : E} : toCLM A x = A x := rfl

/--
@isnad1 id=eq.0h7v.s8.b1ee1e73a577 from=seed src=0 shape=f709a91f vocab=cb39e8d5
-/
@[simp]
lemma ofCLM_apply {A : E →SL[σ] F} {x : E} : ofCLM A x = A x := rfl

@[deprecated (since := "2026-04-10")] alias _root_.ContinuousLinearMap.toWOT_apply := ofCLM_apply

/--
@isnad1 id=eq.1h7v.s8.0bf9da10f842 from=seed src=0 shape=02622d4d vocab=d4a005e1
-/
@[ext]
lemma ext {A B : E →SWOT[σ] F} (h : ∀ x, A x = B x) : A = B :=
  toCLM_injective <| ContinuousLinearMap.ext h

-- This `ext` lemma is set at a lower priority than the default of 1000, so that the
-- version with an inner product (`ContinuousLinearMapWOT.ext_inner`) takes precedence
-- in the case of Hilbert spaces.
/--
@isnad1 id=eq.1h7v.s9.82aa565ad9b1 from=seed src=0 shape=016a714e vocab=ebb0eccf
-/
@[ext 900]
lemma ext_dual [H : SeparatingDual 𝕜₂ F] {A B : E →SWOT[σ] F}
    (h : ∀ x (y : F⋆), y (A x) = y (B x)) : A = B := by
  simp_rw [ContinuousLinearMapWOT.ext_iff, ← (separatingDual_iff_injective.mp H).eq_iff,
    LinearMap.ext_iff]
  exact h

section SMul

variable {S : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F] [ContinuousConstSMul S F]

/--
@isnad1 id=eq.0h8v.s9.9bb815a62c30 from=seed src=0 shape=11903a2f vocab=3ce25229
-/
@[simp] lemma ofCLM_smul {c : S} {f : E →SL[σ] F} : ofCLM (c • f) = c • ofCLM f := rfl
/--
@isnad1 id=eq.0h8v.s9.522e2ad837ef from=seed src=0 shape=11903a2f vocab=c21e9353
-/
@[simp] lemma toCLM_smul {c : S} {f : E →SWOT[σ] F} : toCLM (c • f) = c • toCLM f := rfl
/--
@isnad1 id=eq.0h9v.s9.ae76ce27062d from=seed src=0 shape=18d986f1 vocab=b7d728f4
-/
@[simp] lemma smul_apply {f : E →SWOT[σ] F} (c : S) (x : E) : (c • f) x = c • (f x) := rfl

end SMul

section Algebra

variable {S : Type*} [CommSemiring S] [Module S E] [SMulCommClass 𝕜₁ S E] [SMul S 𝕜₁]
    [IsScalarTower S 𝕜₁ E] [ContinuousConstSMul S E] [IsTopologicalAddGroup E]

/--
@isnad1 id=eq.0h4v.s10.407bcacca3da from=seed src=0 shape=4abe00b5 vocab=5212831f
-/
@[simp] lemma toCLM_algebraMap (c : S) :
    toCLM (algebraMap S (E →WOT[𝕜₁] E) c) = algebraMap S (E →L[𝕜₁] E) c :=
  rfl

/--
@isnad1 id=eq.0h4v.s10.64c7d7fdd950 from=seed src=0 shape=82466703 vocab=2977c4d8
-/
@[simp] lemma ofCLM_algebraMap (c : S) :
    ofCLM (algebraMap S (E →L[𝕜₁] E) c) = algebraMap S (E →WOT[𝕜₁] E) c :=
  rfl

/--
@isnad1 id=eq.0h5v.s9.c543b06378a2 from=seed src=0 shape=854aec8e vocab=dc0796ce
-/
@[simp] lemma algebraMapCLM_apply (c : S) (x : E) :
    (algebraMap S (E →WOT[𝕜₁] E) c) x = c • x :=
  rfl

end Algebra

variable [IsTopologicalAddGroup F]

/--
@isnad1 id=eq.0h5v.s8.c52d62650d3a from=seed src=0 shape=25831a8b vocab=b4f0dc50
-/
@[simp] lemma ofCLM_zero : ofCLM (0 : E →SL[σ] F) = 0 := rfl
/--
@isnad1 id=eq.0h7v.s9.2a51525076e4 from=seed src=0 shape=41e41a69 vocab=52433747
-/
@[simp] lemma ofCLM_add {f g : E →SL[σ] F} : ofCLM (f + g) = ofCLM f + ofCLM g := rfl
/--
@isnad1 id=eq.0h7v.s9.84ea900e2fd3 from=seed src=0 shape=41e41a69 vocab=65720c51
-/
@[simp] lemma ofCLM_sub {f g : E →SL[σ] F} : ofCLM (f - g) = ofCLM f - ofCLM g := rfl
/--
@isnad1 id=eq.0h6v.s8.e949b43fbcdb from=seed src=0 shape=8b730524 vocab=97e72f2e
-/
@[simp] lemma ofCLM_neg {f : E →SL[σ] F} : ofCLM (-f) = -ofCLM f := rfl
/--
@isnad1 id=eq.0h4v.s9.be691b1a1b60 from=seed src=0 shape=62506e74 vocab=d17f3471
-/
@[simp] lemma ofCLM_mul (f g : F →L[𝕜₂] F) : ofCLM (f * g) = ofCLM f * ofCLM g := rfl
/--
@isnad1 id=eq.0h2v.s8.8a0248c521a0 from=seed src=0 shape=c98b44fc vocab=498fc53c
-/
@[simp] lemma ofCLM_one : ofCLM (1 : F →L[𝕜₂] F) = 1 := rfl
/--
@isnad1 id=eq.0h4v.s9.55b3c11fa94a from=seed src=0 shape=93dd1921 vocab=128e3644
-/
@[simp] lemma ofCLM_pow (f : F →L[𝕜₂] F) (n : ℕ) : ofCLM (f ^ n) = ofCLM f ^ n := rfl
/--
@isnad1 id=eq.0h3v.s8.b88168221ec0 from=seed src=0 shape=ffe96cb2 vocab=26115ad3
-/
@[simp] lemma ofCLM_natCast (n : ℕ) : ofCLM (n : F →L[𝕜₂] F) = n := rfl
/--
@isnad1 id=eq.0h3v.s8.f2f86f89f24b from=seed src=0 shape=ffe96cb2 vocab=ee51fbe6
-/
@[simp] lemma ofCLM_intCast (n : ℤ) : ofCLM (n : F →L[𝕜₂] F) = n := rfl

/--
@isnad1 id=eq.0h5v.s8.65c2e545b3fd from=seed src=0 shape=25831a8b vocab=eb577616
-/
@[simp] lemma toCLM_zero : toCLM (0 : E →SWOT[σ] F) = 0 := rfl
/--
@isnad1 id=eq.0h7v.s9.8fc8c5565998 from=seed src=0 shape=41e41a69 vocab=a96d7253
-/
@[simp] lemma toCLM_add {f g : E →SWOT[σ] F} : toCLM (f + g) = toCLM f + toCLM g := rfl
/--
@isnad1 id=eq.0h7v.s9.97aaaf7741a7 from=seed src=0 shape=41e41a69 vocab=54617237
-/
@[simp] lemma toCLM_sub {f g : E →SWOT[σ] F} : toCLM (f - g) = toCLM f - toCLM g := rfl
/--
@isnad1 id=eq.0h6v.s8.96e7276f3dfb from=seed src=0 shape=8b730524 vocab=53fb8ae9
-/
@[simp] lemma toCLM_neg {f : E →SWOT[σ] F} : toCLM (-f) = -toCLM f := rfl
/--
@isnad1 id=eq.0h4v.s9.2c020987183c from=seed src=0 shape=62506e74 vocab=59a89246
-/
@[simp] lemma toCLM_mul (f g : F →WOT[𝕜₂] F) : toCLM (f * g) = toCLM f * toCLM g := rfl
/--
@isnad1 id=eq.0h2v.s8.b170e02cd9e5 from=seed src=0 shape=c98b44fc vocab=a418941f
-/
@[simp] lemma toCLM_one : toCLM (1 : F →WOT[𝕜₂] F) = 1 := rfl
/--
@isnad1 id=eq.0h4v.s9.286fb2f2d9cf from=seed src=0 shape=93dd1921 vocab=5b6569c1
-/
@[simp] lemma toCLM_pow (f : F →WOT[𝕜₂] F) (n : ℕ) : (f ^ n).toCLM = f.toCLM ^ n := rfl
/--
@isnad1 id=eq.0h3v.s8.421e37e70db9 from=seed src=0 shape=ffe96cb2 vocab=ae3a39bc
-/
@[simp] lemma toCLM_natCast (n : ℕ) : (n : F →WOT[𝕜₂] F).toCLM = n := rfl
/--
@isnad1 id=eq.0h3v.s8.173b9245273a from=seed src=0 shape=ffe96cb2 vocab=c0547dad
-/
@[simp] lemma toCLM_intCast (n : ℤ) : (n : F →WOT[𝕜₂] F).toCLM = n := rfl

/--
@isnad1 id=eq.0h6v.s8.06cf21d4859f from=seed src=0 shape=3efa3913 vocab=fa15f1b1
-/
@[simp] lemma zero_apply (x : E) : (0 : E →SWOT[σ] F) x = 0 := rfl
/--
@isnad1 id=eq.0h8v.s9.2359d1547447 from=seed src=0 shape=4320471a vocab=19caf325
-/
@[simp] lemma add_apply {f g : E →SWOT[σ] F} (x : E) : (f + g) x = f x + g x := rfl
/--
@isnad1 id=eq.0h8v.s9.a92aa58d5fe7 from=seed src=0 shape=4320471a vocab=7eb34caa
-/
@[simp] lemma sub_apply {f g : E →SWOT[σ] F} (x : E) : (f - g) x = f x - g x := rfl
/--
@isnad1 id=eq.0h7v.s8.2d20ea604fcf from=seed src=0 shape=1b61ab40 vocab=1a044ba2
-/
@[simp] lemma neg_apply {f : E →SWOT[σ] F} (x : E) : (-f) x = -(f x) := rfl
/--
@isnad1 id=eq.0h5v.s9.11aae6d1b0cc from=seed src=0 shape=b778df45 vocab=8aef141b
-/
@[simp] lemma mul_apply (f g : F →WOT[𝕜₂] F) (x : F) : (f * g) x = f (g x) := rfl
/--
@isnad1 id=eq.0h3v.s8.d09b0b9763ea from=seed src=0 shape=0ff63925 vocab=54b0b67b
-/
@[simp] lemma one_apply (x : F) : (1 : F →WOT[𝕜₂] F) x = x := rfl
/--
@isnad1 id=eq.0h4v.s8.889cbcd1575f from=seed src=0 shape=6a9cda83 vocab=046aa123
-/
@[simp] lemma natCast_apply (n : ℕ) (x : F) : (n : F →WOT[𝕜₂] F) x = n • x := rfl
/--
@isnad1 id=eq.0h4v.s8.e7971e381201 from=seed src=0 shape=6a9cda83 vocab=fc472da0
-/
@[simp] lemma intCast_apply (n : ℤ) (x : F) : (n : F →WOT[𝕜₂] F) x = n • x := rfl

end Basic

/-!
### The topology of `E →WOT[𝕜] F`

The section endows `E →WOT[𝕜] F` with the weak operator topology and shows the basic properties
of this topology. In particular, we show that it is a topological vector space.
-/
section Topology

variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]

variable (σ E F) in
/-- The function that induces the topology on `E →WOT[𝕜] F`, namely the function that takes
an `A` and maps it to `fun ⟨x, y⟩ => y (A x)` in `E × F⋆ → 𝕜`, bundled as a linear map to make
it easier to prove that it is a TVS. -/
def inducingFn : (E →SWOT[σ] F) →ₗ[𝕜₂] (E × F⋆ → 𝕜₂) where
  toFun := fun A ⟨x, y⟩ => y (A x)
  map_add' := fun x y => by ext; simp
  map_smul' := fun x y => by ext; simp

/--
@isnad1 id=eq.0h8v.s10.bc4275a97c8b from=seed src=0 shape=d8006021 vocab=73fbcba7
-/
@[simp]
lemma inducingFn_apply {f : E →SWOT[σ] F} {x : E} {y : F⋆} :
    inducingFn σ E F f (x, y) = y (f x) :=
  rfl

/-- The weak operator topology is the coarsest topology such that `fun A => y (A x)` is
continuous for all `x, y`. -/
instance instTopologicalSpace : TopologicalSpace (E →SWOT[σ] F) :=
  .induced (inducingFn _ _ _) Pi.topologicalSpace

/--
@isnad1 id=continuo.0h5v.s10.f48754f8a23b from=seed src=0 shape=1ddb3975 vocab=f6ef514b
-/
@[fun_prop]
lemma continuous_inducingFn : Continuous (inducingFn σ E F) :=
  continuous_induced_dom

/--
@isnad1 id=continuo.0h7v.s8.cb3aa7c346c3 from=seed src=0 shape=85a9ad64 vocab=466c7214
-/
lemma continuous_dual_apply (x : E) (y : F⋆) : Continuous fun (A : E →SWOT[σ] F) => y (A x) := by
  refine (continuous_pi_iff.mp continuous_inducingFn) ⟨x, y⟩

/--
@isnad1 id=continuo.1h7v.s8.12ac5b477906 from=seed src=0 shape=a2b08788 vocab=466c7214
-/
@[fun_prop]
lemma continuous_of_dual_apply_continuous {α : Type*} [TopologicalSpace α] {g : α → E →SWOT[σ] F}
    (h : ∀ x (y : F⋆), Continuous fun a => y (g a x)) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr fun p => h p.1 p.2)

/--
@isnad1 id=isinduci.0h5v.s10.de0936f6864d from=seed src=0 shape=1ddb3975 vocab=505193e2
-/
@[fun_prop]
lemma isInducing_inducingFn : IsInducing (inducingFn σ E F) := ⟨rfl⟩

/--
@isnad1 id=isembedd.0h5v.s10.dfe536c24802 from=seed src=0 shape=423a36e6 vocab=2c569621
-/
@[fun_prop]
lemma isEmbedding_inducingFn [SeparatingDual 𝕜₂ F] : IsEmbedding (inducingFn σ E F) := by
  refine Function.Injective.isEmbedding_induced fun A B hAB => ?_
  rw [ContinuousLinearMapWOT.ext_dual_iff]
  simpa [funext_iff] using hAB

open Filter in
/-- The defining property of the weak operator topology: a function `f` tends to
`A : E →WOT[𝕜] F` along filter `l` iff `y (f a x)` tends to `y (A x)` along the same filter.
@isnad1 id=iff.0h9v.s9.403f7868056c from=seed src=0 shape=42b35dc8 vocab=5c4edfd1
-/
lemma tendsto_iff_forall_dual_apply_tendsto {α : Type*} {l : Filter α} {f : α → E →SWOT[σ] F}
    {A : E →SWOT[σ] F} :
    Tendsto f l (𝓝 A) ↔ ∀ x (y : F⋆), Tendsto (fun a => y (f a x)) l (𝓝 (y (A x))) := by
  simp [isInducing_inducingFn.tendsto_nhds_iff, tendsto_pi_nhds]

/--
@isnad1 id=iff.0h7v.s9.f5e674c07c8d from=seed src=0 shape=17154c38 vocab=dd6b85af
-/
lemma le_nhds_iff_forall_dual_apply_le_nhds {l : Filter (E →SWOT[σ] F)} {A : E →SWOT[σ] F} :
    l ≤ 𝓝 A ↔ ∀ x (y : F⋆), l.map (fun T => y (T x)) ≤ 𝓝 (y (A x)) :=
  tendsto_iff_forall_dual_apply_tendsto (f := id)

/--
@isnad1 id=t3space.0h5v.s7.c663c97f7030 from=seed src=0 shape=03323e15 vocab=50835d3d
-/
instance instT3Space [SeparatingDual 𝕜₂ F] : T3Space (E →SWOT[σ] F) :=
  isEmbedding_inducingFn.t3Space

instance {S : Type*} [DistribSMul S F] [SMulCommClass 𝕜₂ S F] [ContinuousConstSMul S F]
    [SMul S 𝕜₂] [IsScalarTower S 𝕜₂ 𝕜₂] [IsScalarTower S 𝕜₂ F] :
    ContinuousConstSMul S (F →WOT[𝕜₂] F) where
  continuous_const_smul c := by
    apply continuous_of_dual_apply_continuous fun _ _ ↦ ?_
    simp only [smul_apply, ContinuousLinearMap.map_smul_of_tower]
    exact continuous_const_smul c |>.comp <| continuous_dual_apply ..

/--
@isnad1 id=continuo.0h6v.s9.ef2ea8fff5dc from=seed src=0 shape=28eeae78 vocab=609a38fd
-/
instance instContinuousSMul {S : Type*} [Semiring S] [Module S F] [SMulCommClass 𝕜₂ S F]
    [Module S 𝕜₂] [IsScalarTower S 𝕜₂ F] [IsScalarTower S 𝕜₂ 𝕜₂] [ContinuousConstSMul S F]
    [TopologicalSpace S] [ContinuousSMul S 𝕜₂] :
  ContinuousSMul S (E →SWOT[σ] F) := .induced <| (inducingFn σ E F).restrictScalars S

/--
@isnad1 id=istopolo.0h5v.s7.91e0e592cd61 from=seed src=0 shape=07a7d307 vocab=62fed286
-/
instance instIsTopologicalAddGroup : IsTopologicalAddGroup (E →SWOT[σ] F) where
  toContinuousAdd := .induced (inducingFn σ E F)
  toContinuousNeg := .induced (inducingFn σ E F)

instance instUniformSpace : UniformSpace (E →SWOT[σ] F) := .comap (inducingFn σ E F) inferInstance

/--
@isnad1 id=isunifor.0h5v.s7.5816748b3f17 from=seed src=0 shape=08627734 vocab=62f3a39a
-/
instance instIsUniformAddGroup : IsUniformAddGroup (E →SWOT[σ] F) := .comap (inducingFn σ E F)

end Topology

/-! ### The WOT is induced by a family of seminorms -/
section Seminorms

variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]

/-- The family of seminorms that induce the weak operator topology, namely `‖y (A x)‖` for
all `x` and `y`. -/
def seminorm (x : E) (y : F⋆) : Seminorm 𝕜₂ (E →SWOT[σ] F) where
  toFun A := ‖y (A x)‖
  map_zero' := by simp
  add_le' A B := by simpa using norm_add_le _ _
  neg' A := by simp
  smul' r A := by simp

variable (σ E F) in
/-- The family of seminorms that induce the weak operator topology, namely `‖y (A x)‖` for
all `x` and `y`. -/
def seminormFamily : SeminormFamily 𝕜₂ (E →SWOT[σ] F) (E × F⋆) :=
  fun ⟨x, y⟩ => seminorm x y

/--
@isnad1 id=withsemi.0h5v.s8.9c626350db64 from=seed src=0 shape=06d0e4a2 vocab=7d53df64
-/
lemma withSeminorms : WithSeminorms (seminormFamily σ E F) :=
  let e : E × F⋆ ≃ (Σ _ : E × F⋆, Fin 1) := .symm <| .sigmaUnique _ _
  isInducing_inducingFn.withSeminorms <| withSeminorms_pi (fun _ ↦ norm_withSeminorms 𝕜₂ 𝕜₂)
    |>.congr_equiv e

/--
@isnad1 id=hasbasis.0h5v.s9.57aef6bc8c21 from=seed src=0 shape=69f54056 vocab=ac75ec69
-/
lemma hasBasis_seminorms :
    (𝓝 (0 : E →SWOT[σ] F)).HasBasis (· ∈ (seminormFamily σ E F).basisSets) id :=
  withSeminorms.hasBasis

/--
@isnad1 id=locallyc.0h5v.s10.ebabbc73f5e9 from=seed src=0 shape=c3e47172 vocab=a1a20b4b
-/
instance instLocallyConvexSpace [NormedSpace ℝ 𝕜₂] [Module ℝ (E →SWOT[σ] F)]
    [IsScalarTower ℝ 𝕜₂ (E →SWOT[σ] F)] :
    LocallyConvexSpace ℝ (E →SWOT[σ] F) :=
  withSeminorms.toLocallyConvexSpace

end Seminorms

section toWOT_continuous

variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F] [ContinuousSMul 𝕜₁ E]

/-- The weak operator topology is coarser than the bounded convergence topology, i.e. the inclusion
map is continuous.
@isnad1 id=continuo.0h5v.s8.4a880973636e from=seed src=0 shape=ede575e9 vocab=79432e5f
-/
@[continuity, fun_prop]
lemma continuous_ofCLM :
    Continuous (ofCLM : (E →SL[σ] F) → (E →SWOT[σ] F)) :=
  ContinuousLinearMapWOT.continuous_of_dual_apply_continuous fun x y ↦
    y.cont.comp <| continuous_eval_const x

/--
@isnad1 id=continuo.0h5v.s8.4a880973636e from=seed src=0 shape=ede575e9 vocab=79432e5f
-/
@[deprecated (since := "2026-04-10")] alias ContinuousLinearMap.continuous_toWOT := continuous_ofCLM

/-- The inclusion map from `E →[𝕜] F` to `E →WOT[𝕜] F`, bundled as a continuous linear map. -/
def _root_.ContinuousLinearMap.WOTofCLM : (E →SL[σ] F) →L[𝕜₂] (E →SWOT[σ] F) where
  toLinearMap := linearEquiv 𝕜₂ |>.symm.toLinearMap
  cont := continuous_ofCLM

@[deprecated (since := "2026-04-10")]
alias ContinuousLinearMap.toWOTCLM := ContinuousLinearMap.WOTofCLM

end toWOT_continuous


section Comp

variable {𝕜₁ 𝕜₂ 𝕜₃ 𝕜₄ : Type*} {E F G H : Type*}
    [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃] [NormedField 𝕜₄]
    {σ₁₂ : 𝕜₁ →+* 𝕜₂} {σ₁₃ : 𝕜₁ →+* 𝕜₃} {σ₁₄ : 𝕜₁ →+* 𝕜₄}
    {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₂₄ : 𝕜₂ →+* 𝕜₄} {σ₃₄ : 𝕜₃ →+* 𝕜₄}
    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]
    [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄]
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]
    [AddCommGroup F] [TopologicalSpace F] [Module 𝕜₂ F]
    [AddCommGroup G] [TopologicalSpace G] [Module 𝕜₃ G]
    [AddCommGroup H] [TopologicalSpace H] [Module 𝕜₄ H]

variable (𝕜₂ F) in
/-- The identity as a continuous linear map on the type synonym equipped with the weak operator
topology -/
protected def id : F →WOT[𝕜₂] F := ofCLM <| .id 𝕜₂ F

/--
@isnad1 id=eq.0h2v.s7.8b574aed32f2 from=seed src=0 shape=557727c0 vocab=f1af082e
-/
@[simp]
lemma toCLM_id : (.id 𝕜₂ F : F →WOT[𝕜₂] F).toCLM = .id 𝕜₂ F := rfl

/-- Composition of continuous linear maps on the type synonym equipped with the weak operator
topology. -/
def comp (g : F →SWOT[σ₂₃] G) (f : E →SWOT[σ₁₂] F) : E →SWOT[σ₁₃] G :=
  ofCLM <| g.toCLM.comp f.toCLM

/--
@isnad1 id=eq.0h12v.s8.1bba441730e4 from=seed src=0 shape=eedee2ac vocab=77353903
-/
@[simp]
lemma comp_apply (g : F →SWOT[σ₂₃] G) (f : E →SWOT[σ₁₂] F) (x : E) :
    g.comp f x = g (f x) := by
  simp [comp]

/--
@isnad1 id=eq.0h11v.s8.fcef53649c7d from=seed src=0 shape=98770a57 vocab=8738408a
-/
@[simp] lemma toCLM_comp (g : F →SWOT[σ₂₃] G) (f : E →SWOT[σ₁₂] F) :
    (g.comp f).toCLM = g.toCLM.comp f.toCLM :=
  rfl

/--
@isnad1 id=eq.0h6v.s7.9bc4d0700926 from=seed src=0 shape=6d2172c1 vocab=76bf03d6
-/
@[simp] lemma comp_id (f : E →SWOT[σ₁₂] F) : comp (.id 𝕜₂ F) f = f := by simp [comp]
/--
@isnad1 id=eq.0h6v.s7.ec9b99b2e1ab from=seed src=0 shape=e07c65ff vocab=76bf03d6
-/
@[simp] lemma id_comp (g : F →SWOT[σ₂₃] G) : comp g (.id 𝕜₂ F) = g := by simp [comp]

/--
@isnad1 id=eq.0h17v.s9.b6936a5b741e from=seed src=0 shape=f3d30507 vocab=163c18cb
-/
lemma comp_assoc (g₃₄ : G →SWOT[σ₃₄] H) (g₂₃ : F →SWOT[σ₂₃] G) (g₁₂ : E →SWOT[σ₁₂] F) :
    (g₃₄.comp g₂₃).comp g₁₂ = g₃₄.comp (g₂₃.comp g₁₂) := by
  simp only [comp, ContinuousLinearMap.comp_assoc]

/--
@isnad1 id=eq.0h4v.s9.0086a13525da from=seed src=0 shape=10690d0c vocab=17fcc171
-/
lemma mul_eq_comp [IsTopologicalAddGroup F] (f g : F →WOT[𝕜₂] F) : f * g = f.comp g := rfl

/--
@isnad1 id=continuo.0h10v.s8.1604a74f9b04 from=seed src=0 shape=375a00af vocab=a77d6d78
-/
@[fun_prop]
lemma continuous_precomp [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G] (f : E →SWOT[σ₁₂] F) :
    Continuous (fun g : F →SWOT[σ₂₃] G ↦ g.comp f) :=
  continuous_of_dual_apply_continuous fun _ _ ↦ continuous_dual_apply ..

variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]
variable [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]

/-- While `RingHomSurjective σ₂₃` is not a strict requirement, there are obstructions to
this without any assumption on `σ₂₃` (in particular, on the dimension of the extension of `𝕜₃` over
`σ₂₃(𝕜₂)`), and in the only common case, which is when `σ₂₃` is conjugation, this type class is
guaranteed. Likewise, it would suffice if `RingHomIsometric` were replaced with the weaker
`Continuous σ₂₃`, but we opt for this because we have these type classes available.
@isnad1 id=continuo.0h10v.s9.ed7e6fb5c914 from=seed src=0 shape=0de6bd74 vocab=bc8de426
-/
@[fun_prop]
lemma continuous_postcomp [RingHomSurjective σ₂₃] [RingHomIsometric σ₂₃] (g : F →SWOT[σ₂₃] G) :
    Continuous (fun f : E →SWOT[σ₁₂] F ↦ g.comp f) := by
  refine continuous_of_dual_apply_continuous fun x z ↦ ?_
  have σ_bij : Function.Bijective σ₂₃ := ⟨σ₂₃.injective, RingHomSurjective.is_surjective⟩
  let σ_equiv : 𝕜₂ ≃+* 𝕜₃ := RingEquiv.ofBijective σ₂₃ σ_bij
  let invPair : RingHomInvPair σ₂₃ σ_equiv.symm := RingHomInvPair.of_ringEquiv σ_equiv
  let invPair_symm := invPair.symm
  let σ_li : 𝕜₂ ≃ₛₗᵢ[σ₂₃] 𝕜₃ :=
    { toLinearEquiv := .ofBijective σ₂₃.toSemilinearMap σ_bij
      norm_map' _ := RingHomIsometric.norm_map }
  conv => enter [1, a]; rw [← σ_li.apply_symm_apply (z _), comp_apply, ← toCLM_apply]
  apply σ_li.continuous.comp
  exact continuous_dual_apply x <| σ_li.symm.toLinearIsometry.toContinuousLinearMap.comp <|
    z.comp g.toCLM

/-- Precomposition by a fixed continuous linear map, as a continuous linear map when all spaces
of continuous linear maps are equipped with the weak operator topology. -/
@[simps]
def precompCLM (f : E →SWOT[σ₁₂] F) : (F →SWOT[σ₂₃] G) →L[𝕜₃] (E →SWOT[σ₁₃] G) where
  toFun g := g.comp f
  map_add' := by simp [comp]
  map_smul' := by simp [comp]

/-- Precomposition by a fixed continuous linear map, as a continuous linear map when all spaces
of continuous linear maps are equipped with the weak operator topology. -/
@[simps]
def postcompCLM [RingHomSurjective σ₂₃] [RingHomIsometric σ₂₃] (g : F →SWOT[σ₂₃] G) :
    (E →SWOT[σ₁₂] F) →SL[σ₂₃] (E →SWOT[σ₁₃] G) where
  toFun f := g.comp f
  map_add' := by simp [comp]
  map_smul' := by simp [comp]

instance : IsSemitopologicalRing (F →WOT[𝕜₂] F) where
  continuous_const_mul {_} := by simp_rw [mul_eq_comp]; fun_prop
  continuous_mul_const {_} := by simp_rw [mul_eq_comp]; fun_prop

end Comp

end ContinuousLinearMapWOT

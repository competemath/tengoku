/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.Linear.Copairing
public import Tengoku.Seed.LinearAlgebra.Multilinear.Curry
public import Tengoku.Seed.LinearAlgebra.Multilinear.TensorProduct
public import Tengoku.Seed.RingTheory.TensorProduct.Maps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Contraction of named multilinear slots

This file contracts two distinguished inputs of a multilinear map against the
copairing of a symmetric perfect pairing. Remaining inputs are indexed by an
arbitrary type `S`, while the two contracted inputs are indexed by `Fin 2`.

Separating contraction is derived by combining two maps, relabelling their two
node inputs as `Fin 2`, and applying the same self-contraction operation.
-/

@[expose] public section

namespace AxiomaticGW

open TensorProduct

namespace SymmetricPerfectPairing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V]

/-- A two-input multilinear map is canonically a bilinear form.-/
def finTwoToBilin :
    MultilinearMap R (fun _ : Fin 2 ↦ V) R →ₗ[R] LinearMap.BilinForm R V :=
  (LinearMap.compRight R
      (MultilinearMap.ofSubsingletonₗ R R V R (0 : Fin 1)).symm.toLinearMap).comp
    (multilinearCurryLeftEquiv R (fun _ : Fin 2 ↦ V) R).toLinearMap

omit [Module.Free R V] [Module.Finite R V] in
/-- Evaluation of the two-input-to-bilinear-form identification.-/
@[simp]
theorem finTwoToBilin_apply
    (f : MultilinearMap R (fun _ : Fin 2 ↦ V) R) (x y : V) :
    finTwoToBilin f x y = f (Fin.cons x fun _ ↦ y) := by
  simp only [finTwoToBilin, Nat.succ_eq_add_one, Nat.reduceAdd,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    multilinearCurryLeftEquiv_apply, LinearMap.compRight_apply]
  rfl

/-- Contract a two-input multilinear map against the copairing.-/
noncomputable def contractTwo (P : SymmetricPerfectPairing R V) :
    MultilinearMap R (fun _ : Fin 2 ↦ V) R →ₗ[R] R :=
  (LinearMap.applyₗ P.copairing).comp
    ((TensorProduct.uncurry (RingHom.id R) V V R).comp finTwoToBilin)

/-- Contraction is evaluation of the bilinear form on the copairing tensor.-/
theorem contractTwo_apply (P : SymmetricPerfectPairing R V)
    (f : MultilinearMap R (fun _ : Fin 2 ↦ V) R) :
    P.contractTwo f = TensorProduct.lift (finTwoToBilin f) P.copairing := rfl

/-- Contract the two `Fin 2` inputs of a multilinear map, leaving the inputs
labelled by `S`.-/
noncomputable def selfContract (P : SymmetricPerfectPairing R V)
    {S : Type*} (f : MultilinearMap R (fun _ : S ⊕ Fin 2 ↦ V) R) :
    MultilinearMap R (fun _ : S ↦ V) R :=
  P.contractTwo.compMultilinearMap f.currySum

/-- Pointwise evaluation of self-contraction.-/
@[simp]
theorem selfContract_apply (P : SymmetricPerfectPairing R V)
    {S : Type*} (f : MultilinearMap R (fun _ : S ⊕ Fin 2 ↦ V) R)
    (a : S → V) :
    P.selfContract f a = P.contractTwo (f.currySum a) := rfl

/-- Self-contraction is additive in the multilinear map.-/
@[simp]
theorem selfContract_add (P : SymmetricPerfectPairing R V) {S : Type*}
    (f g : MultilinearMap R (fun _ : S ⊕ Fin 2 ↦ V) R) :
    P.selfContract (f + g) = P.selfContract f + P.selfContract g := by
  simp only [selfContract, MultilinearMap.currySum_add,
    LinearMap.compMultilinearMap_add]

/-- Self-contraction is compatible with scalar multiplication.-/
@[simp]
theorem selfContract_smul (P : SymmetricPerfectPairing R V) {S : Type*}
    (r : R) (f : MultilinearMap R (fun _ : S ⊕ Fin 2 ↦ V) R) :
    P.selfContract (r • f) = r • P.selfContract f := by
  simp only [selfContract, MultilinearMap.currySum_smul,
    LinearMap.compMultilinearMap_smul]

section Target

variable {W : Type*} [AddCommGroup W] [Module R W]

/-- A two-input multilinear map with arbitrary target is canonically a
curried bilinear map.-/
def finTwoToLinearTarget :
    MultilinearMap R (fun _ : Fin 2 ↦ V) W →ₗ[R] (V →ₗ[R] V →ₗ[R] W) :=
  (LinearMap.compRight R
      (MultilinearMap.ofSubsingletonₗ R R V W (0 : Fin 1)).symm.toLinearMap).comp
    (multilinearCurryLeftEquiv R (fun _ : Fin 2 ↦ V) W).toLinearMap

omit [Module.Free R V] [Module.Finite R V] in
/-- Evaluation of the target-generic two-input identification.-/
@[simp]
theorem finTwoToLinearTarget_apply
    (f : MultilinearMap R (fun _ : Fin 2 ↦ V) W) (x y : V) :
    finTwoToLinearTarget f x y = f (Fin.cons x fun _ ↦ y) := by
  simp only [finTwoToLinearTarget, Nat.succ_eq_add_one, Nat.reduceAdd,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    multilinearCurryLeftEquiv_apply, LinearMap.compRight_apply]
  rfl

/-- Contract a two-input multilinear map with arbitrary target against the
copairing.-/
noncomputable def contractTwoTarget (P : SymmetricPerfectPairing R V) :
    MultilinearMap R (fun _ : Fin 2 ↦ V) W →ₗ[R] W :=
  (LinearMap.applyₗ P.copairing).comp
    ((TensorProduct.uncurry (RingHom.id R) V V W).comp finTwoToLinearTarget)

/-- Target-generic contraction evaluates the associated bilinear map on the
copairing tensor.-/
theorem contractTwoTarget_apply (P : SymmetricPerfectPairing R V)
    (f : MultilinearMap R (fun _ : Fin 2 ↦ V) W) :
    P.contractTwoTarget f = TensorProduct.lift (finTwoToLinearTarget f) P.copairing := rfl

/-- Contract two distinguished inputs while retaining an arbitrary target.-/
noncomputable def selfContractTarget (P : SymmetricPerfectPairing R V)
    {S : Type*} (f : MultilinearMap R (fun _ : S ⊕ Fin 2 ↦ V) W) :
    MultilinearMap R (fun _ : S ↦ V) W :=
  P.contractTwoTarget.compMultilinearMap f.currySum

/-- Pointwise evaluation of target-generic self-contraction.-/
@[simp]
theorem selfContractTarget_apply (P : SymmetricPerfectPairing R V)
    {S : Type*} (f : MultilinearMap R (fun _ : S ⊕ Fin 2 ↦ V) W)
    (a : S → V) :
    P.selfContractTarget f a = P.contractTwoTarget (f.currySum a) := rfl

/-- For scalar target, target-generic self-contraction is the original
self-contraction.-/
theorem selfContractTarget_eq_selfContract (P : SymmetricPerfectPairing R V)
    {S : Type*} (f : MultilinearMap R (fun _ : S ⊕ Fin 2 ↦ V) R) :
    P.selfContractTarget f = P.selfContract f := by
  rfl

/-- Relabelling the uncontracted inputs commutes with target-valued
self-contraction. The two distinguished `Fin 2` inputs retain their order.-/
theorem selfContractTarget_domDomCongr (P : SymmetricPerfectPairing R V)
    {S T : Type*} (f : MultilinearMap R (fun _ : S ⊕ Fin 2 ↦ V) W)
    (e : S ≃ T) :
    (P.selfContractTarget f).domDomCongr e =
      P.selfContractTarget
        (f.domDomCongr (Equiv.sumCongr e (Equiv.refl (Fin 2)))) := by
  ext a
  rw [MultilinearMap.domDomCongr_apply]
  simp only [selfContractTarget_apply]
  congr 1
  ext b
  simp only [MultilinearMap.currySum_apply', MultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  rcases i with i | i <;> rfl

end Target

/-- Relabelling the uncontracted inputs commutes with scalar-valued
self-contraction. The two distinguished `Fin 2` inputs retain their order.-/
theorem selfContract_domDomCongr (P : SymmetricPerfectPairing R V)
    {S T : Type*} (f : MultilinearMap R (fun _ : S ⊕ Fin 2 ↦ V) R)
    (e : S ≃ T) :
    (P.selfContract f).domDomCongr e =
      P.selfContract
        (f.domDomCongr (Equiv.sumCongr e (Equiv.refl (Fin 2)))) := by
  simpa only [selfContractTarget_eq_selfContract] using
    P.selfContractTarget_domDomCongr (W := R) f e

/-- The transposition of the two distinguished node labels.-/
def swapFinTwo : Equiv.Perm (Fin 2) := Equiv.swap 0 1

omit [Module.Free R V] [Module.Finite R V] in
/-- Relabelling a two-input map by the transposition flips its associated
bilinear form.-/
theorem finTwoToBilin_domDomCongr_swap
    (f : MultilinearMap R (fun _ : Fin 2 ↦ V) R) (x y : V) :
    finTwoToBilin (f.domDomCongr swapFinTwo) x y = finTwoToBilin f y x := by
  simp only [finTwoToBilin_apply, MultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Relabel the inputs of two maps with distinguished `Option` nodes as one
family of ordinary labels and two ordered node labels. The first node is
`0 : Fin 2` and the second node is `1 : Fin 2`.-/
def separatingLabelsEquiv (S T : Type*) :
    Option S ⊕ Option T ≃ (S ⊕ T) ⊕ Fin 2 where
  toFun
    | .inl none => .inr 0
    | .inl (some s) => .inl (.inl s)
    | .inr none => .inr 1
    | .inr (some t) => .inl (.inr t)
  invFun
    | .inl (.inl s) => .inl (some s)
    | .inl (.inr t) => .inr (some t)
    | .inr i => Fin.cases (.inl none) (fun _ ↦ .inr none) i
  left_inv x := by
    rcases x with x | x
    · rcases x with _ | s <;> rfl
    · rcases x with _ | t <;> rfl
  right_inv x := by
    rcases x with (s | t) | i
    · rfl
    · rfl
    · fin_cases i <;> rfl

/-- Contract the distinguished node of each of two multilinear maps, retaining
the tensor product of their targets.-/
noncomputable def pairContractTarget (P : SymmetricPerfectPairing R V)
    {W₁ W₂ : Type*} [AddCommGroup W₁] [Module R W₁]
    [AddCommGroup W₂] [Module R W₂] {S T : Type*}
    (f : MultilinearMap R (fun _ : Option S ↦ V) W₁)
    (g : MultilinearMap R (fun _ : Option T ↦ V) W₂) :
    MultilinearMap R (fun _ : S ⊕ T ↦ V) (W₁ ⊗[R] W₂) :=
  P.selfContractTarget
    ((f.domCoprod g).domDomCongr (separatingLabelsEquiv S T))

/-- Pointwise evaluation of target-generic separating contraction.-/
@[simp]
theorem pairContractTarget_apply (P : SymmetricPerfectPairing R V)
    {W₁ W₂ : Type*} [AddCommGroup W₁] [Module R W₁]
    [AddCommGroup W₂] [Module R W₂] {S T : Type*}
    (f : MultilinearMap R (fun _ : Option S ↦ V) W₁)
    (g : MultilinearMap R (fun _ : Option T ↦ V) W₂) (a : S ⊕ T → V) :
    P.pairContractTarget f g a =
      P.contractTwoTarget
        (((f.domCoprod g).domDomCongr (separatingLabelsEquiv S T)).currySum a) := rfl

/-- Contract the distinguished node of each of two scalar-valued multilinear
maps. The remaining labels are the disjoint union `S ⊕ T`.-/
noncomputable def pairContract (P : SymmetricPerfectPairing R V)
    {S T : Type*} (f : MultilinearMap R (fun _ : Option S ↦ V) R)
    (g : MultilinearMap R (fun _ : Option T ↦ V) R) :
    MultilinearMap R (fun _ : S ⊕ T ↦ V) R :=
  P.selfContract
    (((LinearMap.mul' R R).compMultilinearMap (f.domCoprod g)).domDomCongr
      (separatingLabelsEquiv S T))

/-- Pointwise evaluation of separating contraction through the common
two-slot contraction operation.-/
@[simp]
theorem pairContract_apply (P : SymmetricPerfectPairing R V)
    {S T : Type*} (f : MultilinearMap R (fun _ : Option S ↦ V) R)
    (g : MultilinearMap R (fun _ : Option T ↦ V) R) (a : S ⊕ T → V) :
    P.pairContract f g a =
      P.contractTwo
        ((((LinearMap.mul' R R).compMultilinearMap (f.domCoprod g)).domDomCongr
          (separatingLabelsEquiv S T)).currySum a) := rfl

/-- Applying a linear map after target-valued self-contraction is the same as
applying it to the target before contraction.-/
theorem selfContractTarget_comp {W : Type*} [AddCommGroup W] [Module R W]
    (P : SymmetricPerfectPairing R V) {S : Type*}
    (f : MultilinearMap R (fun _ : S ⊕ Fin 2 ↦ V) W) (φ : W →ₗ[R] R) :
    φ.compMultilinearMap (P.selfContractTarget f) =
      P.selfContract (φ.compMultilinearMap f) := by
  ext a
  simp only [LinearMap.compMultilinearMap_apply, selfContractTarget_apply,
    selfContract_apply, contractTwoTarget_apply, contractTwo_apply]
  induction P.copairing using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
      simp only [lift.tmul, finTwoToLinearTarget_apply,
        MultilinearMap.currySum_apply', finTwoToBilin_apply,
        LinearMap.compMultilinearMap_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Scalarizing both targets after separating contraction agrees with first
scalarizing the two component maps and then using scalar contraction.-/
theorem pairContractTarget_comp_lift
    {W₁ W₂ : Type*} [CommRing W₁] [Algebra R W₁]
    [CommRing W₂] [Algebra R W₂]
    (P : SymmetricPerfectPairing R V) {S T : Type*}
    (f : MultilinearMap R (fun _ : Option S ↦ V) W₁)
    (g : MultilinearMap R (fun _ : Option T ↦ V) W₂)
    (φ : W₁ →ₐ[R] R) (ψ : W₂ →ₐ[R] R) :
    (Algebra.TensorProduct.lift φ ψ (fun _ _ ↦ .all _ _)).toLinearMap.compMultilinearMap
        (P.pairContractTarget f g) =
      P.pairContract (φ.toLinearMap.compMultilinearMap f)
        (ψ.toLinearMap.compMultilinearMap g) := by
  ext a
  simp only [LinearMap.compMultilinearMap_apply, pairContractTarget_apply,
    pairContract_apply, contractTwoTarget_apply, contractTwo_apply]
  induction P.copairing using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.compMultilinearMap_domDomCongr]
  | tmul x y =>
      simp only [lift.tmul, finTwoToLinearTarget_apply,
        MultilinearMap.currySum_apply', MultilinearMap.domDomCongr_apply,
        MultilinearMap.domCoprod_apply, AlgHom.toLinearMap_apply,
        Algebra.TensorProduct.lift_tmul,
        LinearMap.compMultilinearMap_domDomCongr, finTwoToBilin_apply,
        LinearMap.compMultilinearMap_apply, LinearMap.mul'_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Contracting two metric functionals against the copairing recovers the
metric. This is the abstract sewing identity used by separating gluing.-/
theorem contract_toDual_mul_toDual (P : SymmetricPerfectPairing R V)
    (x y : V) :
    TensorProduct.lift
        (((LinearMap.mul R R).comp (P.toDual x)).compl₂ (P.toDual y))
        P.copairing =
      P.form x y := by
  have contraction (t : V ⊗[R] V) :
      TensorProduct.lift
          (((LinearMap.mul R R).comp (P.toDual x)).compl₂ (P.toDual y)) t =
        P.form (P.tensorEndEquiv t x) y := by
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | tmul u v =>
        simp only [lift.tmul, LinearMap.compl₂_apply, LinearMap.coe_comp,
          Function.comp_apply, toDual_apply, LinearMap.mul_apply_apply,
          tensorEndEquiv_tmul, P.isSymm.eq, map_smul, LinearMap.smul_apply,
          smul_eq_mul]
    | add t₁ t₂ h₁ h₂ =>
        simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) h₁ h₂
  rw [contraction, P.tensorEndEquiv_copairing]
  rfl

end SymmetricPerfectPairing

end AxiomaticGW

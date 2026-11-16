/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.CohFT.Basic
public import Tengoku.Axiomaticgw.AxiomaticGW.CohFT.Topological
public import Tengoku.Axiomaticgw.AxiomaticGW.Combinatorics.StableGraph
public import Tengoku.Seed.RingTheory.TensorProduct.Maps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The constant stable-curve cohomology system

The constant system has target `R` in every genus and arity, concentrated in
codimension degree zero. It is the first end-to-end model of the abstract
stable-curve and full CohFT interfaces.
-/

@[expose] public section

namespace AxiomaticGW

open DirectSum TensorProduct

/-- The grading on the constant target: all of `R` lies in degree zero.-/
def constantDegree (R : Type*) [CommRing R] (d : ℕ) : Submodule R R :=
  if d = 0 then ⊤ else ⊥

namespace constantDegree

variable (R : Type*) [CommRing R]

instance gradedMonoid : SetLike.GradedMonoid (constantDegree R) where
  one_mem := by simp only [constantDegree, ↓reduceIte, Submodule.mem_top]
  mul_mem := by
    intro i j x y hx hy
    by_cases hi : i = 0
    · subst i
      by_cases hj : j = 0
      · subst j
        simp only [constantDegree, add_zero, ↓reduceIte, Submodule.mem_top]
      · have hy0 : y = 0 := by
          simpa only [constantDegree, hj, ↓reduceIte, Submodule.mem_bot]
            using hy
        subst y
        simp only [constantDegree, zero_add, mul_zero, zero_mem]
    · have hx0 : x = 0 := by
        simpa only [constantDegree, hi, ↓reduceIte, Submodule.mem_bot]
          using hx
      subst x
      simp only [constantDegree, Nat.add_eq_zero_iff, zero_mul, zero_mem]

/-- The explicit homogeneous decomposition for the constant grading.-/
def decompose : R →+ ⨁ d, constantDegree R d where
  toFun x := (DirectSum.of (fun d ↦ ↥(constantDegree R d)) 0)
    ⟨x, by simp only [constantDegree, ↓reduceIte, Submodule.mem_top]⟩
  map_zero' := by
    exact (DirectSum.of (fun d ↦ ↥(constantDegree R d)) 0).map_zero
  map_add' x y := by
    exact (DirectSum.of (fun d ↦ ↥(constantDegree R d)) 0).map_add
      ⟨x, by simp only [constantDegree, ↓reduceIte, Submodule.mem_top]⟩
      ⟨y, by simp only [constantDegree, ↓reduceIte, Submodule.mem_top]⟩

instance decomposition : DirectSum.Decomposition (constantDegree R) where
  decompose' := decompose R
  left_inv x := by
    simp only [decompose, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      coeAddMonoidHom_of]
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero =>
        change (decompose R) 0 = 0
        exact map_zero (decompose R)
    | of d x =>
        by_cases hd : d = 0
        · subst d
          simp only [decompose, coeAddMonoidHom_of, AddMonoidHom.coe_mk,
            ZeroHom.coe_mk, Subtype.coe_eta]
        · have hx : x = 0 := by
            apply Subtype.ext
            simpa only [constantDegree, hd, ZeroMemClass.coe_zero,
              ZeroMemClass.coe_eq_zero, ↓reduceIte, Submodule.mem_bot]
              using x.property
          subst x
          simp only [map_zero]
    | add x y hx hy =>
        change (decompose R) ((DirectSum.coeAddMonoidHom (constantDegree R)) (x + y)) = x + y
        rw [map_add, map_add, hx, hy]

instance gradedAlgebra : GradedAlgebra (constantDegree R) where
  __ := gradedMonoid R
  __ := decomposition R

end constantDegree

/-- The coefficient ring as an even graded algebra concentrated in degree
zero.-/
abbrev constantEvenGradedAlgebra (R : Type*) [CommRing R] :
    EvenGradedAlgebra R where
  carrier := R
  degree := constantDegree R

private theorem constantSeparatingDegree (R : Type*) [CommRing R]
    (d : ℕ) (x : R) (hx : x ∈ constantDegree R d) :
    (Algebra.TensorProduct.includeLeft : R →ₐ[R] R ⊗[R] R) x ∈
      tensorDegree (constantEvenGradedAlgebra R) (constantEvenGradedAlgebra R) d := by
  by_cases hd : d = 0
  · subst d
    change x ⊗ₜ[R] 1 ∈ tensorDegree (constantEvenGradedAlgebra R)
      (constantEvenGradedAlgebra R) 0
    apply Submodule.subset_span
    exact ⟨0, 0, x, 1, rfl, hx,
      by simp only [constantDegree, ↓reduceIte, Submodule.mem_top], rfl⟩
  · have hx0 : x = 0 := by
      simpa only [constantDegree, hd, ↓reduceIte, Submodule.mem_bot] using hx
    subst x
    rw [map_zero]
    exact (tensorDegree (constantEvenGradedAlgebra R)
      (constantEvenGradedAlgebra R) d).zero_mem

/-- The constant stable-curve cohomology system.-/
abbrev constantStableCurveCohomology (R : Type*) [CommRing R]
    [Algebra ℚ R] : StableCurveCohomology R where
  H := fun _ _ _ ↦ constantEvenGradedAlgebra R
  degree_eq_bot_of_dimension_lt := by
    intro g S _ h d hd
    have hd0 : d ≠ 0 := by
      intro hd0
      subst d
      exact (Nat.not_lt_zero _ hd)
    simp only [constantDegree, hd0, ↓reduceIte]
  rename := fun _ _ _ _ _ _ _ _ ↦ AlgEquiv.refl
  forget := fun _ _ _ _ ↦ AlgHom.id R R
  nonseparating := fun _ _ _ _ ↦ AlgHom.id R R
  separating := fun _ _ _ _ _ _ _ _ ↦ Algebra.TensorProduct.includeLeft
  rename_degree := by
    intros
    assumption
  forget_degree := by
    intros
    assumption
  nonseparating_degree := by
    intros
    assumption
  separating_degree := by
    intro _ _ _ _ _ _ _ _ d x hx
    exact constantSeparatingDegree R d x hx
  rename_refl := by intros; rfl
  rename_trans := by intros; rfl
  forget_natural := by intros; rfl
  nonseparating_natural := by intros; rfl
  separating_natural := by
    intros
    ext
  separating_swap := by
    intros
    ext
  nonseparating_swap := by intros; rfl
  forget_forget := by intros; rfl
  forget_nonseparating := by intros; rfl
  forget_separating_left := by
    intros
    ext

namespace constantStableCurveCohomology

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- The constant system has the expected genus-zero point geometry.-/
def genusZeroGeometry :
    GenusZeroGeometry (constantStableCurveCohomology R) where
  mbarZeroThree := AlgEquiv.refl
  mbarZeroFourBoundary := rfl

/-- The constant system is connected in degree zero.-/
def connectedDegreeZero :
    ConnectedDegreeZero (constantStableCurveCohomology R) where
  degreeZeroEquiv := fun _ _ _ _ ↦ by
    change ↥(constantDegree R 0) ≃ₐ[R] R
    exact
      { toFun := fun x ↦ x.1
        invFun := fun x ↦
          ⟨x, by simp only [constantDegree, ↓reduceIte, Submodule.mem_top]⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_mul' := fun _ _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        commutes' := fun _ ↦ rfl }
  rename_scalar := by intros; rfl
  forget_scalar := by intros; rfl
  nonseparating_scalar := by intros; rfl
  separating_scalar := by
    intros
    simp only [id_eq, EvenGradedAlgebra.projZeroAlgHom,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.lift_tmul,
      AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_mk,
      Equiv.coe_fn_mk, AlgHom.coe_mk, Function.comp_apply,
      GradedRing.coe_projZeroRingHom'_apply, GradedRing.projZeroRingHom_apply,
      map_one, mul_one]

/-- Canonical stable-graph pullbacks for the constant target. Every vertex
factor is the base ring, so graph pullback is the inverse of multiplication
on the finite heterogeneous tensor product and is independent of edge order.-/
noncomputable def stableGraphPullbacks :
    StableGraphPullbacks (constantStableCurveCohomology R) where
  orderedPullback := by
    intro S _ G _order
    change R →ₐ[R] PiTensorProduct R (fun _ : G.Vertex ↦ R)
    exact (PiTensorProduct.constantBaseRingEquiv G.Vertex R).symm.toAlgHom
  orderedPullback_perm := by
    intros
    rfl

end constantStableCurveCohomology

namespace SymmetricPerfectPairing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V]

/-- Over the coefficient ring, tensor-valued separating contraction is the
canonical image of scalar separating contraction.-/
theorem pairContractTarget_eq_includeLeft (P : SymmetricPerfectPairing R V)
    {S T : Type*} (f : MultilinearMap R (fun _ : Option S ↦ V) R)
    (g : MultilinearMap R (fun _ : Option T ↦ V) R) :
    P.pairContractTarget f g =
      Algebra.TensorProduct.includeLeft.toLinearMap.compMultilinearMap
        (P.pairContract f g) := by
  ext a
  apply (TensorProduct.lid R R).injective
  simp only [pairContractTarget_apply, LinearMap.compMultilinearMap_apply,
    pairContract_apply, contractTwoTarget_apply, contractTwo_apply]
  induction P.copairing using TensorProduct.induction_on with
  | zero => simp only [map_zero,
      Algebra.TensorProduct.toLinearMap_includeLeft,
      LinearMap.compMultilinearMap_domDomCongr]
  | tmul x y => simp only [lift.tmul, finTwoToLinearTarget_apply,
      MultilinearMap.currySum_apply', MultilinearMap.domDomCongr_apply,
      MultilinearMap.domCoprod_apply, lid_tmul, smul_eq_mul,
      Algebra.TensorProduct.toLinearMap_includeLeft,
      LinearMap.compMultilinearMap_domDomCongr, finTwoToBilin_apply,
      LinearMap.compMultilinearMap_apply, LinearMap.mul'_apply,
      LinearMap.flip_apply, AlgebraTensorModule.mk_apply, LinearMap.coe_mk,
      AddHom.coe_mk, mul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

end SymmetricPerfectPairing

namespace TopologicalCohFT

variable {R V : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]

/-- Regard a scalar-valued topological CohFT as a full CohFT over the constant
degree-zero stable-curve cohomology system.-/
def toConstantCohFT (T : TopologicalCohFT R V) :
    CohFT R V (constantStableCurveCohomology R) where
  pairing := T.pairing
  unit := T.unit
  omega := T.omega
  relabel := by
    intro g S U _ _ hS hU e
    change (T.omega g S hS).domDomCongr e = T.omega g U hU
    exact T.relabel g S U hS hU e
  unit_insert := by
    intro g S _ h a
    change T.omega g (Option S) (StableArity.option h)
        (fun | none => T.unit | some s => a s) = T.omega g S h a
    exact T.unit_insert g S h a
  nonseparating := by
    intro g S _ h
    rw [T.relabel g (Option (Option S)) (S ⊕ Fin 2)
      (StableArity.double_option_iff.mpr h)
      (StableArity.sum_fin_two_iff.mpr h) (doubleOptionEquiv S)]
    simpa only [constantStableCurveCohomology,
      SymmetricPerfectPairing.selfContractTarget_eq_selfContract,
      AlgHom.toLinearMap_id, LinearMap.id_compMultilinearMap]
      using T.nonseparating g S h
  separating := by
    intro g₁ g₂ S U _ _ h₁ h₂
    rw [T.pairing.pairContractTarget_eq_includeLeft]
    rw [T.separating g₁ g₂ S U h₁ h₂]
  normalization := by
    intro a
    change T.omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two
        (fun | none => T.unit | some i => a i) = T.pairing.form (a 0) (a 1)
    exact T.normalization a

end TopologicalCohFT

namespace CohFT

variable {R V : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]

/-- A full CohFT over the constant degree-zero target is a scalar-valued
topological CohFT.-/
def toTopologicalCohFT
    (Ω : CohFT R V (constantStableCurveCohomology R)) :
    TopologicalCohFT R V where
  pairing := Ω.pairing
  unit := Ω.unit
  omega := Ω.omega
  relabel := by
    intro g S U _ _ hS hU e
    have h := Ω.relabel g S U hS hU e
    change (Ω.omega g S hS).domDomCongr e = Ω.omega g U hU
    exact h
  unit_insert := by
    intro g S _ h a
    have hunit := Ω.unit_insert g S h a
    change Ω.omega g (Option S) (StableArity.option h)
        (fun | none => Ω.unit | some s => a s) = Ω.omega g S h a
    exact hunit
  nonseparating := by
    intro g S _ h
    have hglue := Ω.nonseparating g S h
    have hrename := Ω.relabel g (Option (Option S)) (S ⊕ Fin 2)
      (StableArity.double_option_iff.mpr h)
      (StableArity.sum_fin_two_iff.mpr h) (doubleOptionEquiv S)
    change Ω.pairing.selfContract (Ω.omega g (S ⊕ Fin 2)
      (StableArity.sum_fin_two_iff.mpr h)) = Ω.omega (g + 1) S h
    rw [← hrename]
    exact hglue
  separating := by
    intro g₁ g₂ S U _ _ h₁ h₂
    have hglue := Ω.separating g₁ g₂ S U h₁ h₂
    rw [Ω.pairing.pairContractTarget_eq_includeLeft] at hglue
    ext a
    have ha := congrArg (fun f ↦ f a) hglue
    have hal := congrArg (TensorProduct.lid R R) ha
    simpa only [SymmetricPerfectPairing.pairContract_apply,
      LinearMap.compMultilinearMap_domDomCongr,
      Algebra.TensorProduct.toLinearMap_includeLeft,
      LinearMap.compMultilinearMap_apply, LinearMap.flip_apply,
      AlgebraTensorModule.mk_apply, LinearMap.coe_mk, AddHom.coe_mk, lid_tmul,
      smul_eq_mul, mul_one] using hal
  normalization := by
    intro a
    have h := Ω.normalization a
    change Ω.omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two
        (fun | none => Ω.unit | some i => a i) = Ω.pairing.form (a 0) (a 1)
    exact h

end CohFT

namespace TopologicalCohFT

variable {R V : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]

/-- Passing a topological CohFT through the constant full CohFT model preserves
all correlators definitionally.-/
@[simp]
theorem toConstantCohFT_toTopologicalCohFT_omega
    (T : TopologicalCohFT R V) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) :
    T.toConstantCohFT.toTopologicalCohFT.omega g S h = T.omega g S h := rfl

end TopologicalCohFT

end AxiomaticGW

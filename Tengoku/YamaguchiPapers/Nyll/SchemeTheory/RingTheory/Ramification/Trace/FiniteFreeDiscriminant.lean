/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.Discriminant
import Tengoku.Seed.RingTheory.Finiteness.ModuleFinitePresentation
import Tengoku.Seed.RingTheory.Smooth.Fiber
import Tengoku.Seed.RingTheory.Unramified.Finite
import Tengoku.Seed.LinearAlgebra.TensorProduct.Basis
import Tengoku.Seed.LinearAlgebra.FreeModule.Finite.Basic
import Tengoku.Seed.Data.Fintype.EquivFin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Trace discriminants of finite free algebras

This file develops the linear-algebra input for the dimension-two branch-locus argument.
For a finite free commutative algebra, the trace pairing is onto the module dual exactly when
the discriminant of a basis is a unit.  The statement works over an arbitrary commutative base
ring; no domain, locality, or etaleness hypothesis is used.
-/

noncomputable section

namespace EtaleFundamentalGroups

open Module
open scoped TensorProduct

universe u v w

/-- For a finite basis, surjectivity of the trace-pairing map is equivalent to the
discriminant being a unit.-/
theorem traceForm_surjective_iff_isUnit_discr
    {R : Type u} {S : Type v} {ι : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [Fintype ι] [DecidableEq ι]
    (b : Basis ι R S) :
    Function.Surjective (Algebra.traceForm R S) ↔
      IsUnit (Algebra.discr R b) := by
  let M : Matrix ι ι R :=
    LinearMap.toMatrix b b.dualBasis (Algebra.traceForm R S)
  have hM : M = Algebra.traceMatrix R b := by
    ext i j
    simp [M, LinearMap.toMatrix_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, mul_comm]
  have hsurj :
      Function.Surjective (Algebra.traceForm R S) ↔
        Function.Surjective M.mulVec := by
    constructor
    · intro h v
      obtain ⟨x, hx⟩ := h (b.dualBasis.equivFun.symm v)
      refine ⟨b.equivFun x, ?_⟩
      have hmatrix :=
        LinearMap.toMatrix_mulVec_repr b b.dualBasis
          (Algebra.traceForm R S) x
      calc
        M.mulVec (b.equivFun x) =
            b.dualBasis.equivFun ((Algebra.traceForm R S) x) := by
          simpa [M, Basis.equivFun_apply] using hmatrix
        _ = b.dualBasis.equivFun (b.dualBasis.equivFun.symm v) := by
          rw [hx]
        _ = v := b.dualBasis.equivFun.apply_symm_apply v
    · intro h y
      obtain ⟨v, hv⟩ := h (b.dualBasis.equivFun y)
      refine ⟨b.equivFun.symm v, ?_⟩
      apply b.dualBasis.equivFun.injective
      have hmatrix :=
        LinearMap.toMatrix_mulVec_repr b b.dualBasis
          (Algebra.traceForm R S) (b.equivFun.symm v)
      have hmatrix' :
          M.mulVec v =
            b.dualBasis.equivFun
              ((Algebra.traceForm R S) (b.equivFun.symm v)) := by
        change
          M.mulVec (b.equivFun (b.equivFun.symm v)) =
            b.dualBasis.equivFun
              ((Algebra.traceForm R S) (b.equivFun.symm v)) at hmatrix
        simpa only [LinearEquiv.apply_symm_apply] using hmatrix
      exact hmatrix'.symm.trans hv
  rw [hsurj, Matrix.mulVec_surjective_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det, Algebra.discr_def, hM]

/-- A unit trace discriminant makes the trace-pairing map injective.  This direction works over
an arbitrary commutative base because the corresponding trace matrix is invertible.-/
theorem traceForm_injective_of_isUnit_discr
    {R : Type u} {S : Type v} {ι : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [Fintype ι] [DecidableEq ι]
    (b : Basis ι R S) (hdisc : IsUnit (Algebra.discr R b)) :
    Function.Injective (Algebra.traceForm R S) := by
  let M : Matrix ι ι R :=
    LinearMap.toMatrix b b.dualBasis (Algebra.traceForm R S)
  have hM : M = Algebra.traceMatrix R b := by
    ext i j
    simp [M, LinearMap.toMatrix_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, mul_comm]
  have hMunit : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, hM, ← Algebra.discr_def]
    exact hdisc
  intro x y hxy
  apply b.equivFun.injective
  apply Matrix.mulVec_injective_of_isUnit hMunit
  have hx :=
    LinearMap.toMatrix_mulVec_repr b b.dualBasis
      (Algebra.traceForm R S) x
  have hy :=
    LinearMap.toMatrix_mulVec_repr b b.dualBasis
      (Algebra.traceForm R S) y
  change M.mulVec (b.equivFun x) =
    b.dualBasis.equivFun ((Algebra.traceForm R S) x) at hx
  change M.mulVec (b.equivFun y) =
    b.dualBasis.equivFun ((Algebra.traceForm R S) y) at hy
  rw [hx, hy, hxy]

/-- Surjectivity of the trace pairing produces the separability element witnessing formal
unramifiedness.  The element is the Casimir tensor associated to a basis and its trace-dual
family; both its multiplication and centrality identities are proved from the trace pairing.-/
theorem formallyUnramified_of_traceForm_surjective
    {R : Type u} {S : Type v} {ι : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [_root_.Finite ι]
    (b : Basis ι R S)
    (hsurj : Function.Surjective (Algebra.traceForm R S)) :
    Algebra.FormallyUnramified R S := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Module.Finite R S := Module.Finite.of_basis b
  have hdisc : IsUnit (Algebra.discr R b) :=
    (traceForm_surjective_iff_isUnit_discr b).mp hsurj
  have hinj : Function.Injective (Algebra.traceForm R S) :=
    traceForm_injective_of_isUnit_discr b hdisc
  choose c hc using fun i : ι ↦ hsurj (b.coord i)
  have hdual (i : ι) (x : S) :
      Algebra.trace R S (c i * x) = b.repr x i := by
    have h := LinearMap.congr_fun (hc i) x
    simpa [Algebra.traceForm_apply, Basis.coord_apply] using h
  let t : S ⊗[R] S := ∑ i, c i ⊗ₜ[R] b i
  have ht_lmul : Algebra.TensorProduct.lmul' R t = 1 := by
    apply hinj
    ext x
    rw [Algebra.traceForm_apply, Algebra.traceForm_apply]
    simp only [t, map_sum, Algebra.TensorProduct.lmul'_apply_tmul,
      Finset.sum_mul, one_mul]
    simp_rw [mul_assoc, hdual]
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
    simp_rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
    congr 1
    funext i
    rw [mul_comm (b i) x]
  refine (Algebra.FormallyUnramified.iff_exists_tensorProduct).mpr
    ⟨t, ?_, ht_lmul⟩
  intro s
  rw [sub_mul, sub_eq_zero]
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext j
  simp only [t, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
    map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  apply hinj
  ext x
  rw [Algebra.traceForm_apply, Algebra.traceForm_apply]
  simp only [Finset.sum_mul, map_sum]
  simp_rw [one_mul,
    TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  have hright (i : ι) :
      Algebra.trace R S ((s * c i) * x) = b.repr (s * x) i := by
    rw [mul_comm s (c i), mul_assoc, hdual]
  simp_rw [smul_mul_assoc, map_smul, hdual, hright]
  calc
    (∑ i, b.repr (s * b i) j • b.repr x i) =
        ∑ i, b.repr x i • b.repr (s * b i) j := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ = b.repr (s * x) j := by
      conv_rhs => rw [← b.sum_repr x]
      simp only [Finset.mul_sum, Algebra.mul_smul_comm, map_sum, map_smul]
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply]
    _ = ∑ i, b.repr (b i) j • b.repr (s * x) i := by
      symm
      rw [Fintype.sum_eq_single j]
      · rw [Basis.repr_self_apply, ite_eq_left rfl, one_smul]
      · intro i hij
        simp [Basis.repr_self, hij]

end EtaleFundamentalGroups

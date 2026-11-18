import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfOrder_isHopfOrder_range_includeRight_comp_of_surjective_baseChange.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 5 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfOrder_isHopfOrder_range_includeRight_comp_of_surjective_baseChange

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u v w

open scoped TensorProduct

namespace HopfOrder
namespace Aux
variable {R : Type u} [CommRing R] {K : Type v} [Field K] [Algebra R K]
variable {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]

noncomputable def tensorSqHom (S : Subalgebra R A) : (S ⊗[R] S) →ₐ[R] (A ⊗[K] A) :=
  Algebra.TensorProduct.productMap
    (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
    (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)

/--
@isnad1 id=eq.0h6v.s11.fa8e15fe24f1 from=translated src=- shape=a3af098c vocab=2178e00c
-/
@[scoped simp]
lemma tensorSqHom_tmul (S : Subalgebra R A) (t t' : S) :
    tensorSqHom S (t ⊗ₜ[R] t') = (t : A) ⊗ₜ[K] (t' : A) := by
  simp [tensorSqHom, Algebra.TensorProduct.productMap_apply_tmul,
    Algebra.TensorProduct.tmul_mul_tmul]

/--
@isnad1 id=mem.2h6v.s11.54153e84f743 from=translated src=- shape=b2a196db vocab=0dbdc06a
-/
lemma tmul_mem_range_tensorSqHom {S : Subalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ S) :
    x ⊗ₜ[K] y ∈ (tensorSqHom S).range :=
  ((tensorSqHom S).mem_range).mpr ⟨(⟨x, hx⟩ : S) ⊗ₜ[R] (⟨y, hy⟩ : S), by rw [tensorSqHom_tmul]⟩

end HopfOrder.Aux
open scoped _root_.P2MW.S_HopfOrder_isHopfOrder_range_includeRight_comp_of_surjective_baseChange.HopfOrder _root_.P2MW.S_HopfOrder_isHopfOrder_range_includeRight_comp_of_surjective_baseChange.HopfOrder.Aux
open scoped _root_.P2MW.S_HopfOrder_isHopfOrder_range_includeRight_comp_of_surjective_baseChange.HopfOrder

namespace HopfOrder
namespace AntipodeCompat
section
universe u' v' w'

variable {R : Type u'} [CommRing R]
variable {H : Type v'} [CommRing H] [HopfAlgebra R H]
variable {H' : Type w'} [CommRing H'] [HopfAlgebra R H']

open TensorProduct in

/--
@isnad1 id=eq.0h5v.s10.94ca500e13e5 from=translated src=- shape=d2f11a98 vocab=c9cbbe96
-/
theorem map_antipode (φ : H →ₐc[R] H') (x : H) :
    φ (HopfAlgebra.antipode R x) = HopfAlgebra.antipode R (φ x) := by
  classical
  let φL : H →ₗ[R] H' := (φ : H →ₐc[R] H').toLinearMap
  let Φ : WithConv (H →ₗ[R] H') := WithConv.toConv φL
  let L : WithConv (H →ₗ[R] H') := WithConv.toConv (φL ∘ₗ HopfAlgebra.antipode R)
  let Rt : WithConv (H →ₗ[R] H') := WithConv.toConv (HopfAlgebra.antipode R ∘ₗ φL)
  have hL : L * Φ = 1 := by
    refine WithConv.ext (LinearMap.ext fun c => ?_)
    rw [LinearMap.convMul_apply]
    change LinearMap.mul' R H' (TensorProduct.map (φL ∘ₗ HopfAlgebra.antipode R) φL (Coalgebra.comul c)) =
      algebraMap R H' (Coalgebra.counit c)
    let ρ := Coalgebra.Repr.arbitrary R c
    have hs := HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit ρ
    rw [← ρ.eq, map_sum, map_sum]
    simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply]
    calc ∑ i ∈ ρ.index, φL (HopfAlgebra.antipode R (ρ.left i)) * φL (ρ.right i)
        = φ (∑ i ∈ ρ.index, HopfAlgebra.antipode R (ρ.left i) * ρ.right i) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul]
          rfl
      _ = algebraMap R H' (Coalgebra.counit c) := by
          rw [hs]
          exact AlgHomClass.commutes φ _
  have hR : Φ * Rt = 1 := by
    refine WithConv.ext (LinearMap.ext fun c => ?_)
    rw [LinearMap.convMul_apply]
    change LinearMap.mul' R H' (TensorProduct.map φL (HopfAlgebra.antipode R ∘ₗ φL) (Coalgebra.comul c)) =
      algebraMap R H' (Coalgebra.counit c)
    let ρ := Coalgebra.Repr.arbitrary R c

    have hmap := congrArg (fun f : H →ₗ[R] H' ⊗[R] H' => f c) (CoalgHomClass.map_comp_comul φ)
    simp only [LinearMap.comp_apply] at hmap
    have heq : ∑ i ∈ ρ.index, φ (ρ.left i) ⊗ₜ[R] φ (ρ.right i) = Coalgebra.comul (φ c) := by
      rw [← ρ.eq, map_sum] at hmap
      simp only [TensorProduct.map_tmul] at hmap
      exact hmap
    let ρ' : Coalgebra.Repr R (φ c) _ :=
      Coalgebra.Repr.mk ρ.index (fun i => φ (ρ.left i)) (fun i => φ (ρ.right i)) heq
    have hs := HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit ρ'
    have hcu : Coalgebra.counit (φ c) = Coalgebra.counit (R := R) c := by
      have h := congrArg (fun f : H →ₗ[R] R => f c) (CoalgHomClass.counit_comp φ)
      simpa using h
    rw [← ρ.eq, map_sum, map_sum]
    simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply]
    rw [← hcu, ← hs]
    rfl
  have hLR : L = Rt := left_inv_eq_right_inv hL hR
  have h := congrArg (fun f : WithConv (H →ₗ[R] H') => f.ofConv x) hLR
  exact h

end
open scoped _root_.P2MW.S_HopfOrder_isHopfOrder_range_includeRight_comp_of_surjective_baseChange.HopfOrder _root_.P2MW.S_HopfOrder_isHopfOrder_range_includeRight_comp_of_surjective_baseChange.HopfOrder.Aux
end HopfOrder.AntipodeCompat
open scoped _root_.P2MW.S_HopfOrder_isHopfOrder_range_includeRight_comp_of_surjective_baseChange.HopfOrder _root_.P2MW.S_HopfOrder_isHopfOrder_range_includeRight_comp_of_surjective_baseChange.HopfOrder.Aux
open scoped _root_.P2MW.S_HopfOrder_isHopfOrder_range_includeRight_comp_of_surjective_baseChange.HopfOrder _root_.P2MW.S_HopfOrder_isHopfOrder_range_includeRight_comp_of_surjective_baseChange.HopfOrder.Aux

open HopfOrder.Aux HopfOrder.AntipodeCompat in
/--
@isnad1 id=other.1h5v.s15.ea0531a81559 from=translated src=- shape=7491b771 vocab=91075631
-/
theorem solution
    {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F]
    {H : Type*} [CommRing H] [HopfAlgebra R H] [Module.Finite R H]
    {H' : Type*} [CommRing H'] [HopfAlgebra R H']
    (φ : H →ₐc[R] H')
    (hφ : Function.Surjective ((φ : H →ₐ[R] H').toLinearMap.baseChange F)) :
    let S : Subalgebra R (F ⊗[R] H') :=
      ((Algebra.TensorProduct.includeRight : H' →ₐ[R] F ⊗[R] H').comp (φ : H →ₐ[R] H')).range
    (Module.Finite R ↥S ∧
    Submodule.span F ((S : Subalgebra R (F ⊗[R] H')) : Set (F ⊗[R] H')) = ⊤ ∧
    (∀ x ∈ S, Coalgebra.comul (R := F) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : (F ⊗[R] H') →ₐ[F] (F ⊗[R] H') ⊗[F] (F ⊗[R] H')).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : (F ⊗[R] H') →ₐ[F] (F ⊗[R] H') ⊗[F] (F ⊗[R] H')).restrictScalars R).comp S.val)).range) ∧
    (∀ x ∈ S, HopfAlgebra.antipode F (A := (F ⊗[R] H')) x ∈ S) ∧
    (∀ x ∈ S, Coalgebra.counit (R := F) (A := (F ⊗[R] H')) x ∈ (algebraMap R F).range)) ∧
    S ≤ (Algebra.TensorProduct.includeRight : H' →ₐ[R] F ⊗[R] H').range := by
  intro S
  have hmem : ∀ h : H, ((1 : F) ⊗ₜ[R] (φ h) : F ⊗[R] H') ∈ S := fun h => ⟨h, rfl⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    let f : H →ₗ[R] ↥S :=
      ((Algebra.TensorProduct.includeRight : H' →ₐ[R] F ⊗[R] H').comp (φ : H →ₐ[R] H')).toLinearMap.codRestrict
        (Subalgebra.toSubmodule S) (fun h => hmem h)
    have hf : Function.Surjective f := by
      rintro ⟨_, h, rfl⟩
      exact ⟨h, rfl⟩
    exact Module.Finite.of_surjective f hf
  ·
    have h1 : ∀ h' : H', ((1 : F) ⊗ₜ[R] h' : F ⊗[R] H') ∈ Submodule.span F (S : Set (F ⊗[R] H')) := by
      intro h'
      obtain ⟨z, hz⟩ := hφ ((1 : F) ⊗ₜ[R] h')
      rw [← hz]
      clear hz
      induction z using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | tmul f h =>
          rw [LinearMap.baseChange_tmul]
          have : (f ⊗ₜ[R] ((φ : H →ₐ[R] H').toLinearMap h) : F ⊗[R] H') = f • ((1 : F) ⊗ₜ[R] (φ h)) := by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
            rfl
          rw [this]
          exact Submodule.smul_mem _ f (Submodule.subset_span (hmem h))
      | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    refine Submodule.eq_top_iff'.mpr fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul f h' =>
        have : (f ⊗ₜ[R] h' : F ⊗[R] H') = f • ((1 : F) ⊗ₜ[R] h') := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        exact Submodule.smul_mem _ f (h1 h')
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  ·
    rintro x ⟨h, rfl⟩
    show Coalgebra.comul (R := F) ((1 : F) ⊗ₜ[R] (φ h)) ∈ _
    rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]
    have hmap := congrArg (fun f : H →ₗ[R] H' ⊗[R] H' => f h) (CoalgHomClass.map_comp_comul φ)
    simp only [LinearMap.comp_apply] at hmap
    have hco : Coalgebra.comul (R := R) ((φ : H →ₐ[R] H') h)
        = TensorProduct.map (φ : H →ₐc[R] H').toLinearMap (φ : H →ₐc[R] H').toLinearMap
            (Coalgebra.comul (R := R) h) := hmap.symm
    rw [show (φ h : H') = (φ : H →ₐ[R] H') h from rfl, hco]
    induction Coalgebra.comul (R := R) h using TensorProduct.induction_on with
    | zero => rw [map_zero, TensorProduct.tmul_zero, LinearEquiv.map_zero]; exact Subalgebra.zero_mem _
    | tmul a b =>
        rw [TensorProduct.map_tmul, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
        exact tmul_mem_range_tensorSqHom (K := F) (hmem a) (hmem b)
    | add z₁ z₂ h₁ h₂ =>
        rw [map_add, TensorProduct.tmul_add, LinearEquiv.map_add]; exact Subalgebra.add_mem _ h₁ h₂
  ·
    rintro x ⟨h, rfl⟩
    show HopfAlgebra.antipode F ((1 : F) ⊗ₜ[R] (φ h)) ∈ S
    rw [TensorProduct.antipode_def, TensorProduct.AlgebraTensorModule.map_tmul,
      HopfAlgebra.antipode_one]
    have : HopfAlgebra.antipode R (φ h : H') = φ (HopfAlgebra.antipode R h) := (map_antipode φ h).symm
    rw [show (φ h : H') = (φ : H →ₐc[R] H') h from rfl, this]
    exact hmem _
  ·
    rintro x ⟨h, rfl⟩
    show Coalgebra.counit (R := F) ((1 : F) ⊗ₜ[R] (φ h)) ∈ (algebraMap R F).range
    rw [TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.smul_def, mul_one]
    exact ⟨_, rfl⟩
  ·
    rintro x ⟨h, rfl⟩
    exact ⟨φ h, rfl⟩

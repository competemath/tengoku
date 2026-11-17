import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Bialgebra_bijective_convMul_comp_includeRight_baseChange.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Bialgebra_bijective_convMul_comp_includeRight_baseChange

set_option autoImplicit false

open scoped TensorProduct

open Algebra.TensorProduct WithConv Coalgebra

namespace AlgHom export _root_.AlgHom (ext convOne_apply restrictScalars liftEquiv comp coe_restrictScalars' coe_comp comp_apply convMul_apply) end AlgHom
open scoped _root_.AlgHom in

theorem AlgHom.convMul_apply_of_repr {R : Type*} [CommRing R] {C : Type*} [Ring C] [Bialgebra R C]
    {S : Type*} [CommRing S] [Algebra R S] {a : C} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr R a ι𝓡)
    (f g : WithConv (C →ₐ[R] S)) :
    (f * g) a = ∑ i ∈ 𝓡.index, f (𝓡.left i) * g (𝓡.right i) := by
  rw [AlgHom.convMul_apply, ← 𝓡.eq, map_sum]
  simp [Algebra.TensorProduct.lift_tmul]

theorem solution
    (A : Type*) [CommRing A] (B : Type*) [CommRing B] [Algebra A B]
    (H : Type*) [Ring H] [Bialgebra A H]
    (T : Type*) [CommRing T] [Algebra A T] [Algebra B T] [IsScalarTower A B T] :
    Function.Bijective (fun f : WithConv (B ⊗[A] H →ₐ[B] T) =>
        WithConv.toConv ((f.ofConv.restrictScalars A).comp Algebra.TensorProduct.includeRight)) ∧
      (∀ f g : WithConv (B ⊗[A] H →ₐ[B] T),
        WithConv.toConv (((f * g).ofConv.restrictScalars A).comp Algebra.TensorProduct.includeRight)
          = WithConv.toConv ((f.ofConv.restrictScalars A).comp Algebra.TensorProduct.includeRight) *
            WithConv.toConv ((g.ofConv.restrictScalars A).comp Algebra.TensorProduct.includeRight)) ∧
      WithConv.toConv (((1 : WithConv (B ⊗[A] H →ₐ[B] T)).ofConv.restrictScalars A).comp
          Algebra.TensorProduct.includeRight) = (1 : WithConv (H →ₐ[A] T)) ∧
      ∀ (T' : Type*) [CommRing T'] [Algebra A T'] [Algebra B T'] [IsScalarTower A B T']
        (u : T →ₐ[B] T') (f : WithConv (B ⊗[A] H →ₐ[B] T)),
        WithConv.toConv (((u.comp f.ofConv).restrictScalars A).comp Algebra.TensorProduct.includeRight)
          = WithConv.toConv ((u.restrictScalars A).comp
              ((f.ofConv.restrictScalars A).comp Algebra.TensorProduct.includeRight)) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro f g h
    exact WithConv.ext ((AlgHom.liftEquiv A B H T).symm.injective (WithConv.toConv_injective h))
  · intro h
    exact ⟨WithConv.toConv (AlgHom.liftEquiv A B H T h.ofConv),
      congrArg WithConv.toConv ((AlgHom.liftEquiv A B H T).symm_apply_apply h.ofConv)⟩
  · intro f g
    apply WithConv.ext
    apply AlgHom.ext
    intro c
    let 𝓡 := Coalgebra.Repr.arbitrary A c
    let 𝓡' : Coalgebra.Repr B ((1 : B) ⊗ₜ[A] c) _ :=
      { index := 𝓡.index
        left := fun i => (1 : B) ⊗ₜ[A] 𝓡.left i
        right := fun i => (1 : B) ⊗ₜ[A] 𝓡.right i
        eq := by
          rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, ← 𝓡.eq]
          simp [TensorProduct.tmul_sum, map_sum] }
    have lhs := AlgHom.convMul_apply_of_repr 𝓡' f g
    have rhs := AlgHom.convMul_apply_of_repr 𝓡 (WithConv.toConv ((f.ofConv.restrictScalars A).comp includeRight))
      (WithConv.toConv ((g.ofConv.restrictScalars A).comp includeRight))
    simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
      Algebra.TensorProduct.includeRight_apply] at rhs ⊢
    rw [rhs]
    exact lhs
  · apply WithConv.ext
    apply AlgHom.ext
    intro c
    simp [AlgHom.convOne_apply, Algebra.algebraMap_eq_smul_one]
  · intro T' _ _ _ _ u f
    rfl

import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfOrder_comul_mem_range_sup.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfOrder_comul_mem_range_sup

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
@isnad1 id=eq.0h6v.s11.214aae16dda7 from=translated src=- shape=a3af098c vocab=87594de0
-/
@[scoped simp]
lemma tensorSqHom_tmul (S : Subalgebra R A) (t t' : S) :
    tensorSqHom S (t ⊗ₜ[R] t') = (t : A) ⊗ₜ[K] (t' : A) := by
  simp [tensorSqHom, Algebra.TensorProduct.productMap_apply_tmul,
    Algebra.TensorProduct.tmul_mul_tmul]

/--
@isnad1 id=mem.2h6v.s11.6c134f17c0c5 from=translated src=- shape=b2a196db vocab=3a3c09be
-/
lemma tmul_mem_range_tensorSqHom {S : Subalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ S) :
    x ⊗ₜ[K] y ∈ (tensorSqHom S).range :=
  ((tensorSqHom S).mem_range).mpr ⟨(⟨x, hx⟩ : S) ⊗ₜ[R] (⟨y, hy⟩ : S), by rw [tensorSqHom_tmul]⟩

/--
@isnad1 id=le.1h5v.s11.5d9ec3f92d70 from=translated src=- shape=2976c8da vocab=3d4c3ff0
-/
lemma range_tensorSqHom_mono {S S' : Subalgebra R A} (h : S ≤ S') :
    (tensorSqHom (K := K) S).range ≤ (tensorSqHom (K := K) S').range := by
  rintro w hw
  obtain ⟨z, rfl⟩ := ((tensorSqHom (K := K) S).mem_range).mp hw
  clear hw
  induction z with
  | zero => rw [map_zero]; exact Subalgebra.zero_mem _
  | tmul t t' =>
      rw [tensorSqHom_tmul]
      exact tmul_mem_range_tensorSqHom (h t.2) (h t'.2)
  | add z₁ z₂ h₁ h₂ => rw [map_add]; exact Subalgebra.add_mem _ h₁ h₂

end HopfOrder.Aux
open scoped _root_.P2MW.S_HopfOrder_comul_mem_range_sup.HopfOrder _root_.P2MW.S_HopfOrder_comul_mem_range_sup.HopfOrder.Aux
open scoped _root_.P2MW.S_HopfOrder_comul_mem_range_sup.HopfOrder

open HopfOrder.Aux in
/--
@isnad1 id=mem.3h6v.s14.11d4c1417001 from=translated src=- shape=6f90f85f vocab=25b2b24d
-/
theorem solution
    {R : Type u} [CommRing R] {K : Type v} [Field K] [Algebra R K]
    {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A] {S S' : Subalgebra R A}
    (hS : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hS' : ∀ x ∈ S', Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)).range) :
    ∀ x ∈ S ⊔ S', Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp (S ⊔ S').val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp (S ⊔ S').val)).range := by
  have key : S ⊔ S' ≤
      Subalgebra.comap ((Bialgebra.comulAlgHom K A).restrictScalars R)
        (tensorSqHom (K := K) (S ⊔ S')).range := by
    rw [sup_le_iff]
    constructor
    · intro y hy
      rw [Subalgebra.mem_comap]
      have h2 := range_tensorSqHom_mono (K := K) (le_sup_left : S ≤ S ⊔ S') (hS y hy)
      simpa using h2
    · intro y hy
      rw [Subalgebra.mem_comap]
      have h2 := range_tensorSqHom_mono (K := K) (le_sup_right : S' ≤ S ⊔ S') (hS' y hy)
      simpa using h2
  intro x hx
  have hmem := key hx
  rw [Subalgebra.mem_comap] at hmem
  simp at hmem
  exact hmem

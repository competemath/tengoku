import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfOrder_comul_mem_range_sup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfOrder_comul_mem_range_sup.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v w

open scoped TensorProduct
/--
@isnad1 id=mem.3h6v.s14.11d4c1417001 from=translated src=- shape=6f90f85f vocab=25b2b24d
-/
theorem HopfOrder.comul_mem_range_sup
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
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp (S ⊔ S').val)).range := by exact @_root_.P2MW.S_HopfOrder_comul_mem_range_sup.solution R _ K _ _ A _ _ _ _ S S' hS hS'

import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_exists_hopfOrder_of_basis_structureConstants_mem_range

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_exists_hopfOrder_of_basis_structureConstants_mem_range.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped TensorProduct in
theorem HopfAlgebra.exists_hopfOrder_of_basis_structureConstants_mem_range
    (R : Type) [CommRing R] (K : Type) [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K))
    (A : Type) [CommRing A] [HopfAlgebra K A] (hAcocomm : Coalgebra.IsCocomm K A)
    (n : ℕ) (b : Module.Basis (Fin n) K A)
    (hmul : ∀ i j k, b.repr (b i * b j) k ∈ (algebraMap R K).range)
    (hone : ∀ k, b.repr 1 k ∈ (algebraMap R K).range)
    (hcomul : ∀ i jk, (b.tensorProduct b).repr (Coalgebra.comul (R := K) (b i)) jk
        ∈ (algebraMap R K).range)
    (hcounit : ∀ i, Coalgebra.counit (R := K) (b i) ∈ (algebraMap R K).range)
    (hanti : ∀ i k, b.repr (HopfAlgebra.antipode K (b i)) k ∈ (algebraMap R K).range) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ ψ : (K ⊗[R] H) ≃ₐ[K] A,
        ∀ x, Coalgebra.comul (R := K) (ψ x)
          = (TensorProduct.map ψ.toLinearMap ψ.toLinearMap) (Coalgebra.comul (R := K) x) := by exact @_root_.P2MW.S_HopfAlgebra_exists_hopfOrder_of_basis_structureConstants_mem_range.solution R _ K _ _ hinj A _ _ hAcocomm n b hmul hone hcomul hcounit hanti

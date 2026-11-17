import Tengoku.Seed.RingTheory.TensorProduct.Basic
import Tengoku.Seed.LinearAlgebra.TensorProduct.Basis
import Tengoku.Seed.LinearAlgebra.LinearIndependent.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_Module_Basis_tensorProduct_tensorProduct_linearIndependent_restrictScalars

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_Basis_tensorProduct_tensorProduct_linearIndependent_restrictScalars.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped TensorProduct
theorem Module.Basis.tensorProduct_tensorProduct_linearIndependent_restrictScalars
    (R : Type) (K : Type) (A : Type) [CommRing R] [CommRing K] [Algebra R K] [CommRing A]
    [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    (hinj : Function.Injective (algebraMap R K))
    {n : ℕ} (b : Module.Basis (Fin n) K A) :
    LinearIndependent R ((b.tensorProduct (b.tensorProduct b)) :
      Fin n × Fin n × Fin n → A ⊗[K] (A ⊗[K] A)) := by exact @_root_.P2MW.S_Module_Basis_tensorProduct_tensorProduct_linearIndependent_restrictScalars.solution R K A _ _ _ _ _ _ _ hinj n b

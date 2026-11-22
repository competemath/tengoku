import Tengoku.Seed.LinearAlgebra.Eigenspace.Basic
import Tengoku.Seed.LinearAlgebra.TensorProduct.Basic
import Tengoku.Seed.LinearAlgebra.Dimension.Finrank
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Defs
import Tengoku.Seed.RingTheory.TensorProduct.Finite
import Tengoku.FltAnthropic.P2M.Sol.S_Module_End_finrank_iInf_maxGenEigenspace_map_tensorProduct_eq_mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_End_finrank_iInf_maxGenEigenspace_map_tensorProduct_eq_mul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

/--
@isnad1 id=eq.0h9v.s11.a8f7fab7117d from=translated src=- shape=42f23914 vocab=4371e0da
-/
theorem Module.End.finrank_iInf_maxGenEigenspace_map_tensorProduct_eq_mul
    (F : Type) [Field F]
    (V W : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {ι κ : Type} (A : ι → Module.End F V) (μ : ι → F) (B : κ → Module.End F W) (ν : κ → F) :
    Module.finrank F
      ↥((⨅ i : ι, Module.End.maxGenEigenspace (TensorProduct.map (A i) (LinearMap.id : W →ₗ[F] W)) (μ i)) ⊓
        (⨅ j : κ, Module.End.maxGenEigenspace (TensorProduct.map (LinearMap.id : V →ₗ[F] V) (B j)) (ν j))) =
    Module.finrank F ↥(⨅ i : ι, Module.End.maxGenEigenspace (A i) (μ i)) *
      Module.finrank F ↥(⨅ j : κ, Module.End.maxGenEigenspace (B j) (ν j)) := by exact @_root_.P2MW.S_Module_End_finrank_iInf_maxGenEigenspace_map_tensorProduct_eq_mul.solution F _ V W _ _ _ _ _ _ ι κ A μ B ν

import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_FormallyEtale_existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_FormallyEtale_existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped TensorProduct

universe u v w

/--
@isnad1 id=existsun.2h5v.s10.2816cea6fa09 from=translated src=- shape=cfe1239f vocab=6eac63e1
-/
theorem Algebra.FormallyEtale.existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (H : Type v) [CommRing H] [Algebra 𝓞 H] [Module.Free 𝓞 H] [Module.Finite 𝓞 H] [Algebra.FormallyEtale 𝓞 H]
    (T : Type w) [CommRing T] [Algebra 𝓞 T] [Module.Free 𝓞 T] [Module.Finite 𝓞 T]
    (ψbar : ZMod p ⊗[𝓞] H →ₐ[ZMod p] ZMod p ⊗[𝓞] T) :
    ∃! ψ : H →ₐ[𝓞] T, Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) ψ = ψbar := by exact @_root_.P2MW.S_Algebra_FormallyEtale_existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp.solution 𝓞 _ p _ hp _ hker _ H _ _ _ _ _ T _ _ _ _ ψbar

import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_bijective_translate_and_map_mem_and_exists_comp_translate_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_bijective_translate_and_map_mem_and_exists_comp_translate_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

universe u v w

/--
@isnad1 id=and.1h3v.s13.f655cd5214cc from=translated src=- shape=3d3da1fd vocab=9d5adaef
-/
theorem HopfAlgebra.bijective_translate_and_map_mem_and_exists_comp_translate_eq
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (τ : (H →ₐ[k] k) → (H →ₐ[k] H))
    (hτ : ∀ (g : H →ₐ[k] k) (h : H),
      τ g h = Algebra.TensorProduct.lid k H (Algebra.TensorProduct.map g (AlgHom.id k H) (Coalgebra.comul h))) :
    (∀ g, Function.Bijective (τ g)) ∧
    (∀ (K : Subalgebra k H),
      (∀ x ∈ K, Coalgebra.comul (R := k) x ∈
        Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}) →
      ∀ g, ∀ x ∈ K, τ g x ∈ K) ∧
    (∀ x y : H →ₐ[k] k, ∃ g : H →ₐ[k] k, y = x.comp (τ g)) := by exact @_root_.P2MW.S_HopfAlgebra_bijective_translate_and_map_mem_and_exists_comp_translate_eq.solution k _ H _ _ τ hτ

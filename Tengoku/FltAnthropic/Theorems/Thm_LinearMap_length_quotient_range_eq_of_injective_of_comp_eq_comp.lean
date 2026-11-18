import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_LinearMap_length_quotient_range_eq_of_injective_of_comp_eq_comp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LinearMap_length_quotient_range_eq_of_injective_of_comp_eq_comp.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u

/--
@isnad1 id=eq.3h5v.s11.2dfd0d69f3dc from=translated src=- shape=401acdd5 vocab=35cc7e81
-/
theorem LinearMap.length_quotient_range_eq_of_injective_of_comp_eq_comp
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {r : ℕ}
    (F₁ F₂ φ : (Fin r → A) →ₗ[A] (Fin r → A))
    (hF₁ : Function.Injective F₁) (hφ : Function.Injective φ)
    (hcomm : φ ∘ₗ F₂ = F₁ ∘ₗ φ) :
    Module.length A ((Fin r → A) ⧸ LinearMap.range F₁) =
      Module.length A ((Fin r → A) ⧸ LinearMap.range F₂) := by exact @_root_.P2MW.S_LinearMap_length_quotient_range_eq_of_injective_of_comp_eq_comp.solution A _ _ _ r F₁ F₂ φ hF₁ hφ hcomm

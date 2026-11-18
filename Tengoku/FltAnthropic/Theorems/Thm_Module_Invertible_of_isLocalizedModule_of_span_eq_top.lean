import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_Invertible_of_isLocalizedModule_of_span_eq_top

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_Invertible_of_isLocalizedModule_of_span_eq_top.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open TensorProduct

theorem Module.Invertible.of_isLocalizedModule_of_span_eq_top
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (s : Set R) (hs : Ideal.span s = ⊤)
    {Mₚ : ∀ (_ : s), Type*} [∀ (g : s), AddCommGroup (Mₚ g)] [∀ (g : s), Module R (Mₚ g)]
    {Rₚ : ∀ (_ : s), Type*} [∀ (g : s), CommRing (Rₚ g)] [∀ (g : s), Algebra R (Rₚ g)]
    [∀ (g : s), IsLocalization.Away g.val (Rₚ g)]
    [∀ (g : s), Module (Rₚ g) (Mₚ g)] [∀ (g : s), IsScalarTower R (Rₚ g) (Mₚ g)]
    (ϕ : ∀ (g : s), M →ₗ[R] Mₚ g) [∀ (g : s), IsLocalizedModule (Submonoid.powers g.val) (ϕ g)]
    (h : ∀ (g : s), Module.Invertible (Rₚ g) (Mₚ g)) :
    Module.Invertible R M := by exact @_root_.P2MW.S_Module_Invertible_of_isLocalizedModule_of_span_eq_top.solution R _ M _ _ s hs Mₚ _ _ Rₚ _ _ _ _ _ ϕ _ h

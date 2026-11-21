import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Submodule_Quotient_isOfFinAddOrder_of_forall_isMaximal_of_subalgebra_fg

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Submodule_Quotient_isOfFinAddOrder_of_forall_isMaximal_of_subalgebra_fg.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
open scoped Pointwise
/--
@isnad1 id=isoffina.5h7v.s11.c89b17f1bd0e from=translated src=- shape=9ee6e1c8 vocab=ced9c95e
-/
theorem Submodule.Quotient.isOfFinAddOrder_of_forall_isMaximal_of_subalgebra_fg
    {R J : Type*} [CommRing R] [AddCommGroup J] [Module R J]
    (ρ : R →+* Module.End ℤ J) (hρ : ∀ (t : R) (x : J), t • x = ρ t x)
    (S : Subalgebra ℤ (Module.End ℤ J)) (hS : (Subalgebra.toSubmodule S).FG)
    (hρS : ∀ t, ρ t ∈ S)
    (I γ : Ideal R) (hγ : ∀ t : R, (∃ i ∈ I, ∀ x : J, ((1 + i) * t) • x = 0) → t ∈ γ)
    (z : J ⧸ (γ • (⊤ : Submodule R J)))
    (hz : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → I ≤ 𝔪 → ∃ s ∉ 𝔪, IsOfFinAddOrder (s • z)) :
    IsOfFinAddOrder z := by exact @_root_.P2MW.S_Submodule_Quotient_isOfFinAddOrder_of_forall_isMaximal_of_subalgebra_fg.solution R J _ _ _ ρ hρ S hS hρS I γ hγ z hz

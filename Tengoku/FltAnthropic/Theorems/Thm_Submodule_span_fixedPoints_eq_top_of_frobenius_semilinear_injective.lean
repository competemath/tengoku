import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Submodule_span_fixedPoints_eq_top_of_frobenius_semilinear_injective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Submodule_span_fixedPoints_eq_top_of_frobenius_semilinear_injective.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=eq.3h5v.s9.35ad9973f06d from=translated src=- shape=6a0c1c25 vocab=bece6e94
-/
theorem Submodule.span_fixedPoints_eq_top_of_frobenius_semilinear_injective
    {K V : Type*} [Field K] [IsAlgClosed K] {p : ℕ} [Fact p.Prime] [CharP K p]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (s : ℕ) (hs : s ≠ 0) (θ : V →+ V)
    (hθ : ∀ (c : K) (v : V), θ (c • v) = c ^ p ^ s • θ v) (hinj : Function.Injective θ) :
    Submodule.span K (Function.fixedPoints θ) = ⊤ := by exact @_root_.P2MW.S_Submodule_span_fixedPoints_eq_top_of_frobenius_semilinear_injective.solution K V _ _ p _ _ _ _ _ s hs θ hθ hinj

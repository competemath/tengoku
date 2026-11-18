import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfOrder_finite_sup_and_span_sup_eq_top

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfOrder_finite_sup_and_span_sup_eq_top.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v w
theorem HopfOrder.finite_sup_and_span_sup_eq_top
    {R : Type u} [CommRing R] {K : Type v} [Field K] [Algebra R K]
    {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A] {S S' : Subalgebra R A}
    [Module.Finite R S] [Module.Finite R S'] (hspan : Submodule.span K (S : Set A) = ⊤) :
    Module.Finite R ↥(S ⊔ S') ∧ Submodule.span K ((S ⊔ S' : Subalgebra R A) : Set A) = ⊤ := by exact @_root_.P2MW.S_HopfOrder_finite_sup_and_span_sup_eq_top.solution R _ K _ _ A _ _ _ _ S S' _ _ hspan

import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_exists_notMem_forall_dual_eq_trace_iff_fiber

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_exists_notMem_forall_dual_eq_trace_iff_fiber.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.exists_notMem_forall_dual_eq_trace_iff_fiber
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (P' : Ideal (p.Fiber B)) [P'.IsPrime]
    (hP' : P = P'.comap Algebra.TensorProduct.includeRight.toRingHom) :
    (∃ s ∉ P, ∀ φ : Module.Dual A B, ∃ x : B, ∀ y : B, φ (s * y) = Algebra.trace A B (x * y)) ↔
      (∃ s ∉ P', ∀ φ : Module.Dual p.ResidueField (p.Fiber B), ∃ x : p.Fiber B, ∀ y : p.Fiber B,
        φ (s * y) = Algebra.trace p.ResidueField (p.Fiber B) (x * y)) := by exact @_root_.P2MW.S_Algebra_exists_notMem_forall_dual_eq_trace_iff_fiber.solution A B _ _ _ _ _ p _ P _ _ P' _ hP'

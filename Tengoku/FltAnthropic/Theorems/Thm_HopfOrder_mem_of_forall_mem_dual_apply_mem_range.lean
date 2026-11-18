import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.P2M.Sol.S_HopfOrder_mem_of_forall_mem_dual_apply_mem_range

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfOrder_mem_of_forall_mem_dual_apply_mem_range.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-simp] HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul

set_option autoImplicit false

open scoped TensorProduct

theorem HopfOrder.mem_of_forall_mem_dual_apply_mem_range
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    [Module.Finite K A] [Coalgebra.IsCocomm K A]
    [Algebra R (CartierDual K A)] [IsScalarTower R K (CartierDual K A)]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (S' : Subalgebra R (CartierDual K A))
    (hS' : ∀ φ : CartierDual K A, φ ∈ S' ↔ ∀ b ∈ S, φ b ∈ (algebraMap R K).range)
    (a : A) (ha : ∀ φ ∈ S', φ a ∈ (algebraMap R K).range) : a ∈ S := by exact @_root_.P2MW.S_HopfOrder_mem_of_forall_mem_dual_apply_mem_range.solution R _ _ _ K _ _ _ A _ _ _ _ _ _ _ _ S hfin hspan S' hS' a ha
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)

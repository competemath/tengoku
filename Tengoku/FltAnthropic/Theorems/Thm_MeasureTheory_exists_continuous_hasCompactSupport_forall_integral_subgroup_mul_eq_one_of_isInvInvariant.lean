import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_exists_continuous_hasCompactSupport_forall_integral_subgroup_mul_eq_one_of_isInvInvariant

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_exists_continuous_hasCompactSupport_forall_integral_subgroup_mul_eq_one_of_isInvInvariant.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_continuous_hasCompactSupport_forall_integral_subgroup_mul_eq_one_of_isInvInvariant
    {T : Type*} [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (S : Subgroup T) (hS : IsClosed (S : Set T)) [MeasurableSpace S] [BorelSpace S]
    (τS : Measure S) [τS.IsHaarMeasure] [τS.IsInvInvariant]
    (C : Set T) (hC : IsCompact C) (hSC : ∀ t : T, ∃ s : S, ∃ c ∈ C, t = (s : T) * c) :
    ∃ β : T → ℝ, Continuous β ∧ HasCompactSupport β ∧ (∀ t, 0 ≤ β t) ∧
      ∀ t : T, ∫ s : S, β ((s : T) * t) ∂τS = 1 := by exact @_root_.P2MW.S_MeasureTheory_exists_continuous_hasCompactSupport_forall_integral_subgroup_mul_eq_one_of_isInvInvariant.solution T _ _ _ _ _ _ _ S hS _ _ τS _ _ C hC hSC

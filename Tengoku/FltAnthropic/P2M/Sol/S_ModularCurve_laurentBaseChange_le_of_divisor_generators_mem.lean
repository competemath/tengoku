import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_laurentBaseChange_le_of_divisor_generators_mem.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_laurentBaseChange_le_of_divisor_generators_mem

set_option autoImplicit false

open _root_.ModularCurve

namespace ModularCurve export _root_.ModularCurve (qExpand algebraMap_apply_eq_single jq modularFunctionFieldFull coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange mem_laurentBaseChange_iff) end ModularCurve
open scoped _root_.ModularCurve in

theorem ModularCurve.ringHom_mem_of_mem_adjoin' {L : Type*} [Field L] (T : Subfield (LaurentSeries L))
    (g : LaurentSeries ℚ →+* LaurentSeries L)
    (hgc : ∀ c : ℚ, g (algebraMap ℚ (LaurentSeries ℚ) c) ∈ T)
    {S : Set (LaurentSeries ℚ)} (hS : ∀ s ∈ S, g s ∈ T)
    {y : LaurentSeries ℚ} (hy : y ∈ IntermediateField.adjoin ℚ S) : g y ∈ T := by
  induction hy using IntermediateField.adjoin_induction with
  | mem x hx => exact hS x hx
  | algebraMap c => exact hgc c
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem solution
    (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ) [NeZero M]
    (T : IntermediateField L (LaurentSeries L))
    (hgens : ∀ (d : ℕ) (_ : NeZero d), d ∣ M → coeffEmb L (qExpand ℚ d jq) ∈ T) :
    laurentBaseChange L (modularFunctionFieldFull M) ≤ T := by
  intro x hx
  rw [mem_laurentBaseChange_iff] at hx
  show x ∈ T.toSubfield
  refine (Subfield.closure_le (t := T.toSubfield)).mpr ?_ hx
  rintro y (⟨c, rfl⟩ | ⟨z, hz, rfl⟩)
  · exact T.algebraMap_mem c
  · refine ModularCurve.ringHom_mem_of_mem_adjoin' T.toSubfield (coeffEmb L) ?_ ?_ hz
    · intro c
      have : coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) c) = algebraMap L (LaurentSeries L) (algebraMap ℚ L c) := by
        rw [coeffEmb, algebraMap_apply_eq_single, coeffMap_single, algebraMap_laurentSeries_eq_single]
      rw [this]
      exact T.algebraMap_mem _
    · rintro s ⟨d, hne, hdvd, rfl⟩
      exact hgens d hne hdvd

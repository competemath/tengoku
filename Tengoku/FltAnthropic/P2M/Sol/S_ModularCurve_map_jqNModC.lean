import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_JqCoeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_map_jqNModC.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_map_jqNModC

open _root_.ModularCurve

set_option autoImplicit false

namespace ModularCurve export _root_.ModularCurve (coeffMap coeffMap_coeff jqModC jqNModC map_jqModC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd) end ModularCurve
open scoped _root_.ModularCurve in

/--
@isnad1 id=eq.0h5v.s9.58a3cfbe3ba5 from=translated src=- shape=0f099109 vocab=6d87040a
-/
theorem ModularCurve.solution_aux_coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases h : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

/--
@isnad1 id=eq.0h4v.s7.e3f4924ffc8a from=translated src=- shape=4f6a501c vocab=c0346c1d
-/
theorem solution {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (N : ℕ) [NeZero N] : coeffMap φ (jqNModC R N) = jqNModC S N := by
  have hj : coeffMap φ (jqModC R) = jqModC S := map_jqModC φ
  rw [jqNModC, jqNModC, ModularCurve.solution_aux_coeffMap_qExpand, hj]

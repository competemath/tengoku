import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.FltAnthropic.Theorems.Thm_LaurentSeries_exists_eq_C_of_isAlgebraic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_modularFunctionFieldFull.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 3 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_modularFunctionFieldFull

set_option autoImplicit false

open _root_.ModularCurve

namespace ModularCurve
export _root_.ModularCurve (modularFunctionFieldFull)
open _root_.ModularCurve

namespace AlgClosedFull

variable (N : ℕ) [NeZero N]

def v : ↥(modularFunctionFieldFull N) →+* LaurentSeries ℚ :=
  { toFun := Subtype.val, map_one' := rfl, map_mul' := fun _ _ => rfl,
    map_zero' := rfl, map_add' := fun _ _ => rfl }

/--
@isnad1 id=isalgebr.1h2v.s10.13917d7cc64f from=translated src=- shape=29e37bec vocab=2ea3b948
-/
theorem isAlgebraic_coe (x : ↥(modularFunctionFieldFull N)) (hx : IsAlgebraic ℚ x) :
    IsAlgebraic ℚ (x : LaurentSeries ℚ) := by
  obtain ⟨p, hp0, hpx⟩ := hx
  have key : ((Polynomial.aeval x p : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) =
      Polynomial.aeval (x : LaurentSeries ℚ) p := by
    rw [Polynomial.aeval_def, Polynomial.aeval_def]
    change v N (Polynomial.eval₂ (algebraMap ℚ ↥(modularFunctionFieldFull N)) x p) = _
    rw [Polynomial.hom_eval₂]
    congr 1
    · exact Subsingleton.elim _ _
  refine ⟨p, hp0, ?_⟩
  rw [← key, hpx]
  rfl

/--
@isnad1 id=ex.1h2v.s12.af8e908b86d3 from=translated src=- shape=67ac737e vocab=ece34815
-/
theorem main (x : ↥(modularFunctionFieldFull N)) (hx : IsAlgebraic ℚ x) :
    ∃ c : ℚ, x = algebraMap ℚ ↥(modularFunctionFieldFull N) c := by
  obtain ⟨c, hc⟩ := LaurentSeries.exists_eq_C_of_isAlgebraic (x : LaurentSeries ℚ) (isAlgebraic_coe N x hx)
  refine ⟨c, Subtype.ext ?_⟩
  rw [hc]

  exact congrArg (fun f : ℚ →+* LaurentSeries ℚ => f c)
    (Subsingleton.elim (HahnSeries.C : ℚ →+* LaurentSeries ℚ) ((v N).comp (algebraMap ℚ ↥(modularFunctionFieldFull N))))

end AlgClosedFull

end ModularCurve

open _root_.ModularCurve open _root_.P2MW.S_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_modularFunctionFieldFull.ModularCurve

/--
@isnad1 id=ex.1h2v.s12.af8e908b86d3 from=translated src=- shape=67ac737e vocab=ece34815
-/
theorem solution
    (N : ℕ) [NeZero N] (x : ↥(modularFunctionFieldFull N)) (hx : IsAlgebraic ℚ x) :
    ∃ c : ℚ, x = algebraMap ℚ ↥(modularFunctionFieldFull N) c :=
  ModularCurve.AlgClosedFull.main N x hx

import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_open`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField

set_option autoImplicit false

open _root_.AlgebraicCurve open _root_.ModularCurve

namespace AlgebraicCurve export _root_.AlgebraicCurve (Place Place.deg) namespace Place export _root_.AlgebraicCurve.Place (ResidueField deg) end AlgebraicCurve.Place
open scoped _root_.AlgebraicCurve _root_.AlgebraicCurve.Place in

private theorem AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.deg = 1 ↔ Function.Surjective (algebraMap K v.ResidueField) := by
  unfold Place.deg
  rw [show Function.Surjective (algebraMap K v.ResidueField)
        ↔ Function.Bijective (algebraMap K v.ResidueField) from
      ⟨fun h => ⟨(algebraMap K v.ResidueField).injective, h⟩, fun h => h.2⟩]
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField.AlgebraicCurve ModularCurve in

/--
@isnad1 id=iff.0h3v.s9.361e1ea12d19 from=translated src=- shape=dba853dc vocab=767350e7
-/
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.deg = 1 ↔ Function.Surjective (algebraMap K v.ResidueField) :=
  AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField v


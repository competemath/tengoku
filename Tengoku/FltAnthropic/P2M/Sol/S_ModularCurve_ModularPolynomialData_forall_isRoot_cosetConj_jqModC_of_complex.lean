import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_JqCoeff
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_PrimCosetReps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_ModularPolynomialData_forall_isRoot_cosetConj_jqModC_of_complex.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_ModularPolynomialData_forall_isRoot_cosetConj_jqModC_of_complex

set_option autoImplicit false

noncomputable section

open _root_.ModularCurve open _root_.Polynomial

namespace ModularCurve
export _root_.ModularCurve (qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd ModularPolynomialData jqModC map_jqModC primCosetReps cosetConj qTwist qTwist_coeff cosetSubst coeffMap coeffMap_coeff)
namespace CosetDescentAux
open _root_.ModularCurve

variable {R S : Type*} [CommRing R] [CommRing S]

def conjR (u : Rˣ) (J : LaurentSeries R) (t : ℕ × ℕ × ℕ) : LaurentSeries R :=
  if h : t.1 = 0 then 0 else
    haveI : NeZero (t.1 * t.1) := ⟨Nat.mul_ne_zero h h⟩
    qExpand R (t.1 * t.1) (qTwist (u ^ (t.1 * t.2.1)) J)

def phiAt (N : ℕ) [NeZero N] (Φ : Polynomial (Polynomial ℤ)) (R : Type*) [CommRing R] :
    Polynomial (LaurentSeries R) :=
  Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries R)) (qExpand R N (jqModC R)))

end ModularCurve.CosetDescentAux

end

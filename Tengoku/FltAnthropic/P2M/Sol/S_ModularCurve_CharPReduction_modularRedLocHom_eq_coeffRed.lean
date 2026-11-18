import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_CharPReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_CharPReduction_modularRedLocHom_eq_coeffRed.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_CharPReduction_modularRedLocHom_eq_coeffRed

open _root_.ModularCurve open _root_.ModularCurve.CharPReduction

set_option autoImplicit false

noncomputable section

namespace ModularCurve
open _root_.ModularCurve
namespace CharpSD2

section LocalizedReduction

variable {L : Type*} [CommRing L] {k : Type*} [Field k]
variable {A : Subring L} {red : A →+* k}
variable {R : Subring (LaurentSeries L)} {hR : R ≤ integralCoeffs A}

private theorem redLoc_eq_coeffRed (f : localizedAtKer A red R hR)
    (hf : (f : LaurentSeries L) ∈ integralCoeffs A) :
    redLoc f = coeffRed A red ⟨(f : LaurentSeries L), hf⟩ := by
  obtain ⟨r, s, hs, hfs⟩ := f.2
  have hmul : coeffRed A red ⟨(f : LaurentSeries L), hf⟩ * redRes A red R hR s
      = redRes A red R hR r := by
    rw [redRes_apply, redRes_apply, ← map_mul]
    congr 1
    exact Subtype.ext hfs
  have hspec := redLoc_spec f hfs
  have hsne := redRes_ne_zero_of_notMem (A := A) (red := red) (R := R) (hR := hR) hs
  exact mul_right_cancel₀ hsne (hspec.trans hmul.symm)

end LocalizedReduction

end CharpSD2
end ModularCurve

end

/--
@isnad1 id=eq.1h6v.s11.80a1983a3a01 from=translated src=- shape=1c0b4535 vocab=06752ff5
-/
theorem solution {L : Type*} [CommRing L] (A : Subring L)
    {k : Type*} [Field k] (red : A →+* k) (N : ℕ) [NeZero N]
    (f : modularLocalized N A red) (hf : (f : LaurentSeries L) ∈ integralCoeffs A) :
    modularRedLocHom N A red f = coeffRed A red ⟨(f : LaurentSeries L), hf⟩:=
  ModularCurve.CharpSD2.redLoc_eq_coeffRed f hf

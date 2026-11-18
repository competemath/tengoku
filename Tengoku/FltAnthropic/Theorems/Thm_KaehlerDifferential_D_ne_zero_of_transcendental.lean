import Tengoku.Seed.RingTheory.Kaehler.Basic
import Tengoku.Seed.FieldTheory.IntermediateField.Adjoin.Basic
import Tengoku.Seed.FieldTheory.Separable
import Tengoku.Seed.RingTheory.Algebraic.Defs
import Tengoku.FltAnthropic.P2M.Sol.S_KaehlerDifferential_D_ne_zero_of_transcendental

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_KaehlerDifferential_D_ne_zero_of_transcendental.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=ne.1h3v.s8.4b2887ab9a3a from=translated src=- shape=4214a536 vocab=cae8451e
-/
theorem KaehlerDifferential.D_ne_zero_of_transcendental (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendental K x)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :
    KaehlerDifferential.D K F x ≠ 0 := by exact @_root_.P2MW.S_KaehlerDifferential_D_ne_zero_of_transcendental.solution K _ F _ _ x hx _

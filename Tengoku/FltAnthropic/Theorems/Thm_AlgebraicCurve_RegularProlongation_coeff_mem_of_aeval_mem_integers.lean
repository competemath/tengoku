import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_RegularProlongation
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_RegularProlongation_coeff_mem_of_aeval_mem_integers

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_RegularProlongation_coeff_mem_of_aeval_mem_integers.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open AlgebraicCurve

/--
@isnad1 id=mem.2h8v.s9.c6611222bfd0 from=translated src=- shape=f50fb800 vocab=7b017bf6
-/
theorem AlgebraicCurve.RegularProlongation.coeff_mem_of_aeval_mem_integers
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (c : Polynomial L) (hc : Polynomial.aeval (x : F) c ∈ R.integers) (i : ℕ) :
    c.coeff i ∈ A := by exact @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_coeff_mem_of_aeval_mem_integers.solution L _ A F _ _ Fbar _ _ R x hx c hc i

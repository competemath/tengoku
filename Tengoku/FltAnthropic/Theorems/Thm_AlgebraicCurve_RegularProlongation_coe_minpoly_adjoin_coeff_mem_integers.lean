import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_RegularProlongation
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_RegularProlongation_coe_minpoly_adjoin_coeff_mem_integers

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_RegularProlongation_coe_minpoly_adjoin_coeff_mem_integers.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open AlgebraicCurve

/--
@isnad1 id=mem.3h8v.s10.72df4bd87320 from=translated src=- shape=d9c16136 vocab=65d8b7d8
-/
theorem AlgebraicCurve.RegularProlongation.coe_minpoly_adjoin_coeff_mem_integers
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (f : F) (hint : IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) f)
    (h₃ : ∀ V : ValuationSubring F,
      (∀ e : F, e ∈ IntermediateField.adjoin L {(x : F)} → (e ∈ V ↔ e ∈ R.integers)) → f ∈ V)
    (j : ℕ) :
    (((minpoly (Algebra.adjoin L ({(x : F)} : Set F)) f).coeff j :
      Algebra.adjoin L ({(x : F)} : Set F)) : F) ∈ R.integers := by exact @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_coe_minpoly_adjoin_coeff_mem_integers.solution L _ A F _ _ Fbar _ _ R x hx f hint h₃ j

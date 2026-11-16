import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_Place_exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_Place_exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open AlgebraicCurve

/--
@isnad1 id=ex.2h4v.s10.92a6b9693015 from=translated src=- shape=77c8b457 vocab=4cdbc820
-/
theorem AlgebraicCurve.Place.exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing
    {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Subring F) [IsLocalRing D] (hK : ∀ a : K, algebraMap K F a ∈ D)
    (hD : ∃ d : D, d ≠ 0 ∧ ¬ IsUnit d) :
    ∃ Q : AlgebraicCurve.Place K F, (∀ d : F, d ∈ D → d ∈ Q.toValuationSubring) ∧
      ∀ d : D, ((d : F) ∈ Q.toValuationSubring.nonunits ↔ ¬ IsUnit d) := by exact @_root_.P2MW.S_AlgebraicCurve_Place_exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing.solution K F _ _ _ x _ D _ hK hD

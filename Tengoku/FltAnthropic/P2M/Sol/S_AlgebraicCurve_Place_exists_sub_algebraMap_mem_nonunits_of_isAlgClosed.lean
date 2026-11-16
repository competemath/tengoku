import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Place_exists_sub_algebraMap_mem_nonunits_of_isAlgClosed.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_Place_exists_sub_algebraMap_mem_nonunits_of_isAlgClosed

set_option autoImplicit false

open AlgebraicCurve
open scoped Pointwise

/--
@isnad1 id=ex.1h4v.s7.d27d31a79439 from=translated src=- shape=b0e8dc4b vocab=9690b66b
-/
theorem solution
    {κ' : Type*} [Field κ'] [IsAlgClosed κ'] {F' : Type*} [Field F'] [Algebra κ' F']
    (P' : Place κ' F') [P'.FiniteResidue]
    (x : F') (hx : x ∈ P'.toValuationSubring) :
    ∃ c : κ', x - algebraMap κ' F' c ∈ P'.toValuationSubring.nonunits := by
  classical
  haveI : Module.Finite κ' P'.ResidueField := AlgebraicCurve.Place.FiniteResidue.finite
  haveI : Algebra.IsIntegral κ' P'.ResidueField := Algebra.IsIntegral.of_finite κ' _
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := κ') (K := P'.ResidueField)).2
    (IsLocalRing.residue _ ⟨x, hx⟩)
  refine ⟨c, ?_⟩
  have hmem : (⟨x, hx⟩ : P'.toValuationSubring) - algebraMap κ' P'.toValuationSubring c ∈
      IsLocalRing.maximalIdeal P'.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc,
      IsScalarTower.algebraMap_apply κ' P'.toValuationSubring P'.ResidueField, IsLocalRing.ResidueField.algebraMap_eq,
      sub_self]
  have e : ((⟨x, hx⟩ - algebraMap κ' P'.toValuationSubring c : P'.toValuationSubring) : F') = x - algebraMap κ' F' c := by
    change P'.toValuationSubring.subtype (⟨x, hx⟩ - algebraMap κ' P'.toValuationSubring c) = _
    rw [map_sub]
    rfl
  rw [← e]
  exact ValuationSubring.coe_mem_nonunits_iff.mpr hmem

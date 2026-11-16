import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Place_exists_sub_algebraMap_mem_maximalIdeal.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_Place_exists_sub_algebraMap_mem_maximalIdeal

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F]
    [Algebra K F] (u : AlgebraicCurve.Place K F) (hdeg : u.deg = 1) (b : u.toValuationSubring) :
    ∃ c : K, b - algebraMap K u.toValuationSubring c
      ∈ IsLocalRing.maximalIdeal u.toValuationSubring := by
  obtain ⟨c, hc⟩ := ((Place.deg_eq_one_iff_surjective_algebraMap_residueField u).mp hdeg)
    (IsLocalRing.residue _ b)
  refine ⟨c, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc, sub_eq_zero,
    IsScalarTower.algebraMap_apply K u.toValuationSubring u.ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq]


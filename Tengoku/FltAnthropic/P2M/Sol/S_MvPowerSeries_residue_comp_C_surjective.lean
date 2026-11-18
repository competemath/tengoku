import Tengoku.Seed.RingTheory.MvPowerSeries.Inverse
import Tengoku.Seed.RingTheory.AdicCompletion.Noetherian

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPowerSeries_residue_comp_C_surjective.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPowerSeries_residue_comp_C_surjective

set_option autoImplicit false

universe u v w

namespace M4cP4PS

open MvPowerSeries IsLocalRing

variable {σ : Type u} {R : Type v} [CommRing R]

theorem maximalIdeal_eq_comap [IsLocalRing R] :
    maximalIdeal (MvPowerSeries σ R) = (maximalIdeal R).comap (constantCoeff (σ := σ) (R := R)) := by
  ext φ
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    isUnit_iff_constantCoeff]

def dropVar (i : σ) (φ : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun m => if m i = 0 then φ m else 0

theorem residue_comp_C_surjective [IsLocalRing R] :
    Function.Surjective (⇑(residue (MvPowerSeries σ R)) ∘ ⇑(C (σ := σ) (R := R))) := by
  intro x
  obtain ⟨φ, rfl⟩ := residue_surjective x
  refine ⟨constantCoeff φ, ?_⟩
  simp only [Function.comp_apply]
  rw [residue_def, residue_def]
  refine (Ideal.Quotient.eq (I := maximalIdeal (MvPowerSeries σ R))).mpr ?_
  rw [maximalIdeal_eq_comap, Ideal.mem_comap, map_sub, constantCoeff_C, sub_self]
  exact Ideal.zero_mem _

end M4cP4PS

theorem solution {σ : Type u} {R : Type v} [CommRing R]
    [IsLocalRing R] :
    Function.Surjective (⇑(IsLocalRing.residue (MvPowerSeries σ R)) ∘ ⇑(MvPowerSeries.C (σ := σ) (R := R))) :=
  M4cP4PS.residue_comp_C_surjective

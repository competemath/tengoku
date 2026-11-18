import Tengoku.Seed.RingTheory.MvPowerSeries.Inverse
import Tengoku.Seed.RingTheory.AdicCompletion.Noetherian

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPowerSeries_maximalIdeal_eq_comap_constantCoeff.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPowerSeries_maximalIdeal_eq_comap_constantCoeff

set_option autoImplicit false

universe u v w

namespace M4cP4PS

open MvPowerSeries IsLocalRing

variable {σ : Type u} {R : Type v} [CommRing R]

/--
@isnad1 id=eq.0h2v.s6.a4fab4979b4f from=translated src=- shape=643f6d6f vocab=e5cce57c
-/
theorem maximalIdeal_eq_comap [IsLocalRing R] :
    maximalIdeal (MvPowerSeries σ R) = (maximalIdeal R).comap (constantCoeff (σ := σ) (R := R)) := by
  ext φ
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    isUnit_iff_constantCoeff]

def dropVar (i : σ) (φ : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun m => if m i = 0 then φ m else 0

end M4cP4PS

/--
@isnad1 id=eq.0h2v.s6.a4fab4979b4f from=translated src=- shape=643f6d6f vocab=e5cce57c
-/
theorem solution {σ : Type u} {R : Type v} [CommRing R]
    [IsLocalRing R] :
    IsLocalRing.maximalIdeal (MvPowerSeries σ R) =
      (IsLocalRing.maximalIdeal R).comap (MvPowerSeries.constantCoeff (σ := σ) (R := R)) :=
  M4cP4PS.maximalIdeal_eq_comap

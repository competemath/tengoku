import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_TateFormal
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_TateSlots
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_tateBase_map_coeffMap.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_tateBase_map_coeffMap

set_option autoImplicit false

namespace TateBaseCoeffAux

open ModularCurve

/--
@isnad1 id=eq.0h4v.s8.26d29d953e7c from=translated src=- shape=f1272d01 vocab=b31bae85
-/
theorem coeffMap_laurentOfInt {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : PowerSeries ℤ) :
    coeffMap f (laurentOfInt R p) = laurentOfInt S p := by
  ext k
  rw [coeffMap_coeff, laurentOfInt_apply, laurentOfInt_apply]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_map]
    simp
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

/--
@isnad1 id=eq.0h5v.s9.58a3cfbe3ba5 from=translated src=- shape=0f099109 vocab=6d87040a
-/
theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N]
    (x : LaurentSeries R) :
    coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext k
  by_cases h : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd N _ h, qExpand_coeff_of_not_dvd N _ h, map_zero]

end TateBaseCoeffAux

open TateBaseCoeffAux

/--
@isnad1 id=eq.0h4v.s6.1234b70ecc19 from=translated src=- shape=b8ed767f vocab=7e10e7a3
-/
theorem solution {K K' : Type*} [CommRing K] [CommRing K'] (f : K →+* K') (N : ℕ) [NeZero N] :
    (ModularCurve.tateBase K N).map (ModularCurve.coeffMap f) = ModularCurve.tateBase K' N := by
  simp only [ModularCurve.tateBase, ModularCurve.tateLaurent, WeierstrassCurve.map_map]
  ext <;> simp only [WeierstrassCurve.map, RingHom.coe_comp, Function.comp_apply, coeffMap_qExpand, coeffMap_laurentOfInt]

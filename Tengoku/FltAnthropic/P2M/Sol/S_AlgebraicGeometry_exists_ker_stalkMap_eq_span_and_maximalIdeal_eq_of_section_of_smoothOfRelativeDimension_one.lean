import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_exists_algHom_retraction_stalk_and_ker_le_span_sup_sq_of_section_of_smoothOfRelativeDimension_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_exists_ker_stalkMap_eq_span_and_maximalIdeal_eq_of_section_of_smoothOfRelativeDimension_one.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_exists_ker_stalkMap_eq_span_and_maximalIdeal_eq_of_section_of_smoothOfRelativeDimension_one

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace SecParam

theorem eq_span_of_le_span_sup_sq {S : Type*} [CommRing S] [IsLocalRing S] {I : Ideal S} (hfg : I.FG)
    (hI : I ≤ maximalIdeal S) {t : S} (ht : t ∈ I) (hle : I ≤ Ideal.span {t} ⊔ I ^ 2) : I = Ideal.span {t} := by
  apply le_antisymm _ ((Ideal.span_singleton_le_iff_mem _).mpr ht)
  have hjac : I ≤ (⊥ : Ideal S).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact hI
  exact Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac (by rwa [Ideal.smul_eq_mul, ← pow_two])

theorem maximalIdeal_eq_ker_sup_map {A S : Type*} [CommRing A] [IsLocalRing A] [CommRing S] [IsLocalRing S]
    (ι : A →+* S) (π : S →+* A) (hπ : ∀ a, π (ι a) = a) :
    maximalIdeal S = RingHom.ker π ⊔ (maximalIdeal A).map ι := by
  have hkle : RingHom.ker π ≤ maximalIdeal S := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top π)
  apply le_antisymm
  · intro z hz
    have hk : z - ι (π z) ∈ RingHom.ker π := by
      rw [RingHom.mem_ker, map_sub, hπ, sub_self]
    by_cases hu : IsUnit (π z)
    · exfalso
      have h1 : ι (π z) ∈ maximalIdeal S := by
        have e : ι (π z) = z - (z - ι (π z)) := by ring
        rw [e]
        exact sub_mem hz (hkle hk)
      exact (IsLocalRing.mem_maximalIdeal _).mp h1 (hu.map ι)
    · have hm : π z ∈ maximalIdeal A := hu
      have e : z = (z - ι (π z)) + ι (π z) := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hk) (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hm))
  · refine sup_le hkle ?_
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap]
    exact (IsLocalRing.mem_maximalIdeal _).mpr fun h =>
      (IsLocalRing.mem_maximalIdeal _).mp ha (by simpa [hπ] using h.map π)

end SecParam

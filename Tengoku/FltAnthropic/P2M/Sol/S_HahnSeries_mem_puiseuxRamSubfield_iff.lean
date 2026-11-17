import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HahnSeries_RamificationBound

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HahnSeries_mem_puiseuxRamSubfield_iff.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HahnSeries_mem_puiseuxRamSubfield_iff

set_option autoImplicit false

open HahnSeries

namespace P2MWs13
namespace Puiseux

variable {K : Type*} [Field K]

/--
@isnad1 id=hasrambo.1h3v.s8.51db8b93c2d2 from=translated src=- shape=57536f5a vocab=ca6cd715
-/
theorem hasRamBound_puiseuxRamEmb {e : ℕ} (he : 0 < e) (x : HahnSeries ℤ K) :
    HasRamBound e (puiseuxRamEmb he x) := by
  intro q hq
  have hsub : (puiseuxRamEmb he x).support ⊆ (ramScale e) '' x.support := by
    unfold puiseuxRamEmb
    rw [embDomainRingHom_apply]
    exact HahnSeries.support_embDomain_subset
  obtain ⟨k, _, rfl⟩ := hsub hq
  exact ⟨k, rfl⟩

/--
@isnad1 id=ispwo.1h3v.s6.98c8e47d939b from=translated src=- shape=ecb3f1ff vocab=b7b319a6
-/
theorem isPWO_ramScale_preimage_support {e : ℕ} (he : 0 < e) (y : HahnSeries ℚ K) :
    {k : ℤ | y.coeff ((k : ℚ) / e) ≠ 0}.IsPWO := by
  have hmono : StrictMono (fun k : ℤ => (k : ℚ) / e) :=
    fun a b hab => div_lt_div_of_pos_right (Int.cast_lt.mpr hab) (Nat.cast_pos.mpr he)
  have hmap : Set.MapsTo (fun k : ℤ => (k : ℚ) / e)
      {k : ℤ | y.coeff ((k : ℚ) / e) ≠ 0} y.support := fun k hk => hk
  rw [Set.isPWO_iff_isWF]
  refine Set.WellFoundedOn.mono
    (r' := (fun a b : ℤ => ((a : ℚ) / e : ℚ) < ((b : ℚ) / e : ℚ)))
    (Set.WellFoundedOn.mapsTo _ hmap y.isPWO_support.isWF)
    (fun a b hab => hmono hab) (le_refl _)

def puiseuxRamSection {e : ℕ} (he : 0 < e) (y : HahnSeries ℚ K) : HahnSeries ℤ K where
  coeff k := y.coeff ((k : ℚ) / e)
  isPWO_support' := isPWO_ramScale_preimage_support he y

/--
@isnad1 id=eq.2h3v.s8.4193362ccdea from=translated src=- shape=569b2bc6 vocab=23a35976
-/
theorem puiseuxRamEmb_section {e : ℕ} (he : 0 < e) {y : HahnSeries ℚ K}
    (hy : HasRamBound e y) : puiseuxRamEmb he (puiseuxRamSection he y) = y := by
  ext q
  by_cases hq : q ∈ Set.range (ramScale e)
  · obtain ⟨k, rfl⟩ := hq
    simp only [ramScale_apply, puiseuxRamEmb, embDomainRingHom_apply]
    erw [embDomain_mk_coeff (ramScale_injective he) (fun a b => ramScale_le_iff he a b)]
    rfl
  · have hL : (puiseuxRamEmb he (puiseuxRamSection he y)).coeff q = 0 := by
      simp only [puiseuxRamEmb, embDomainRingHom_apply]
      exact embDomain_of_notMem_range (by simpa [Set.range, ramScale_apply] using hq)
    have hR : y.coeff q = 0 := by
      by_contra hne
      exact hq (hy hne)
    rw [hL, hR]

/--
@isnad1 id=iff.1h3v.s8.3893dda6beb1 from=translated src=- shape=98728770 vocab=f3f9b306
-/
theorem mem_range_puiseuxRamEmb_iff {e : ℕ} (he : 0 < e) {y : HahnSeries ℚ K} :
    y ∈ Set.range (puiseuxRamEmb (K := K) he) ↔ HasRamBound e y :=
  ⟨fun ⟨x, hx⟩ => hx ▸ hasRamBound_puiseuxRamEmb he x,
    fun hy => ⟨puiseuxRamSection he y, puiseuxRamEmb_section he hy⟩⟩

end P2MWs13.Puiseux

open P2MWs13.Puiseux in
/--
@isnad1 id=iff.1h3v.s7.b5dace6e5ff4 from=translated src=- shape=300803e1 vocab=f26c86b7
-/
theorem solution {K : Type*} [Field K] {e : ℕ} (he : 0 < e)
    {y : HahnSeries ℚ K} :
    y ∈ HahnSeries.puiseuxRamSubfield K he ↔ HahnSeries.HasRamBound e y := by
  rw [HahnSeries.puiseuxRamSubfield, RingHom.mem_fieldRange]
  exact mem_range_puiseuxRamEmb_iff he

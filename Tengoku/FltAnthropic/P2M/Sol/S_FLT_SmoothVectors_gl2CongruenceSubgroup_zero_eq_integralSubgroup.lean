import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_LocalHeckeInstance
import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_IntegralSubgroupOpen

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FLT_SmoothVectors_gl2CongruenceSubgroup_zero_eq_integralSubgroup.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FLT_SmoothVectors_gl2CongruenceSubgroup_zero_eq_integralSubgroup

open FLT.SmoothVectors

/--
@isnad1 id=eq.0h1v.s7.0e548426babe from=translated src=- shape=c3392215 vocab=759692b9
-/
theorem solution (p : ℕ) [Fact p.Prime] :
    gl2CongruenceSubgroup p 0 = LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] := by
  have hinj : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) := fun a b hab => by
    have ha := PadicInt.algebraMap_apply (p := p) a
    have hb := PadicInt.algebraMap_apply (p := p) b
    rw [ha, hb] at hab
    exact Subtype.coe_injective hab
  have mem_range_iff : ∀ {x : ℚ_[p]},
      x ∈ Set.range (algebraMap ℤ_[p] ℚ_[p]) ↔ ‖x‖ ≤ 1 := by
    intro x
    rw [FLT.SpectralSide.range_algebraMap_padicInt p]
    exact ⟨fun ⟨z, hz⟩ => hz ▸ z.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hradius : ((p : ℝ) ^ (-((0 : ℕ) : ℤ)) : ℝ) = 1 := by norm_num
  ext g
  rw [mem_gl2CongruenceSubgroup_iff,
    FLT.SpectralSide.mem_integralSubgroup_iff_entries_mem hinj g]
  simp only [hradius]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => mem_range_iff.mpr ((norm_sub_one_entry_le_one_iff p).mp (h1 i j)),
           fun i j => mem_range_iff.mpr ((norm_sub_one_entry_le_one_iff p).mp (h2 i j))⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => (norm_sub_one_entry_le_one_iff p).mpr (mem_range_iff.mp (h1 i j)),
           fun i j => (norm_sub_one_entry_le_one_iff p).mpr (mem_range_iff.mp (h2 i j))⟩

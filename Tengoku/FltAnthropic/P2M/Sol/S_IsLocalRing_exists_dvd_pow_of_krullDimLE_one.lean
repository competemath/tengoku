import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_exists_dvd_pow_of_krullDimLE_one.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_exists_dvd_pow_of_krullDimLE_one

open IsLocalRing

namespace RankOneNilSol

theorem exists_dvd_pow {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 1 R]
    {b : R} (hb : b ≠ 0) {c : R} (hc : c ∈ maximalIdeal R) : ∃ n : ℕ, b ∣ c ^ n := by
  by_cases hu : IsUnit b
  · exact ⟨0, hu.dvd⟩
  · have hne : Ideal.span {b} ≠ ⊤ := by
      rwa [Ne, Ideal.span_singleton_eq_top]
    have hrad : (Ideal.span {b}).radical = maximalIdeal R := by
      rw [Ideal.radical_eq_sInf]
      refine le_antisymm (sInf_le ⟨IsLocalRing.le_maximalIdeal hne, inferInstance⟩) (le_sInf ?_)
      rintro J ⟨hJ, hJp⟩
      have hJ0 : J ≠ ⊥ := by
        intro h0
        rw [h0, Ideal.span_singleton_le_iff_mem, Ideal.mem_bot] at hJ
        exact hb hJ
      exact (IsLocalRing.eq_maximalIdeal (hJp.isMaximal_of_ne_bot hJ0)).ge
    have hc' : c ∈ (Ideal.span {b}).radical := hrad ▸ hc
    obtain ⟨n, hn⟩ := hc'
    exact ⟨n, Ideal.mem_span_singleton.mp hn⟩

end RankOneNilSol

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 1 R]
    {b : R} (hb : b ≠ 0) {c : R} (hc : c ∈ IsLocalRing.maximalIdeal R) : ∃ n : ℕ, b ∣ c ^ n :=
  RankOneNilSol.exists_dvd_pow hb hc

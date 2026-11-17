import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.PositiveCharacteristic
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.FiniteFieldNorm
import Tengoku.Seed.Algebra.Field.ZMod
import Tengoku.Seed.Analysis.Normed.Group.Ultra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Norms of finite Laurent sums in characteristic `p`

Lemma D.2(1) and (2): a normed field of characteristic `p` is ultrametric with `‖c‖ = 1` for
`c ∈ 𝔽_p^×`, and if `0 < ‖t‖ < 1` then `‖∑ a_i t^i‖ = ‖t‖ ^ i₀` for `a_i ∈ 𝔽_p`, where `i₀` is
the least index with `a_{i₀} ≠ 0`. Negative exponents are allowed.
-/
namespace Tengoku.AlternatingAnalyticCharacteristicP end Tengoku.AlternatingAnalyticCharacteristicP open Tengoku.AlternatingAnalyticCharacteristicP
namespace AlternatingAnalytic

/-- Lemma D.2(1): in characteristic `p` the norm is ultrametric and `‖c‖ = 1` for `c ∈ 𝔽_p^×`.-/
theorem charP_isUltrametricDist_and_norm_zmod (K : Type*) [NormedField K] (p : ℕ)
    [Fact p.Prime] [CharP K p] :
    IsUltrametricDist K ∧ ∀ c : ZMod p, c ≠ 0 → ‖ZMod.castHom (dvd_refl p) K c‖ = 1 :=
  ⟨charP_isUltrametricDist p, fun c hc => norm_finiteField_map _ c hc⟩

/-- Lemma D.2(2): a finite `𝔽_p`-combination of integer powers of `t` has the norm of its lowest term.-/
theorem norm_sum_zmod_zpow_eq {K : Type*} [NormedField K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (t : K) (ht0 : 0 < ‖t‖) (ht1 : ‖t‖ < 1) (s : Finset ℤ) (a : ℤ → ZMod p) (i₀ : ℤ)
    (hi₀ : i₀ ∈ s) (ha : a i₀ ≠ 0) (hmin : ∀ i ∈ s, a i ≠ 0 → i₀ ≤ i) :
    ‖∑ i ∈ s, ZMod.castHom (dvd_refl p) K (a i) * t ^ i‖ = ‖t‖ ^ i₀ := by
  let : IsUltrametricDist K := charP_isUltrametricDist p
  set f := ZMod.castHom (dvd_refl p) K
  have hpos : 0 < ‖t‖ ^ i₀ := zpow_pos ht0 i₀
  have hlead : ‖f (a i₀) * t ^ i₀‖ = ‖t‖ ^ i₀ := by
    rw [norm_mul, norm_finiteField_map f _ ha, one_mul, norm_zpow]
  have hrest : ‖∑ i ∈ s.erase i₀, f (a i) * t ^ i‖ < ‖t‖ ^ i₀ := by
    have hterm : ∀ j ∈ s.erase i₀, ‖f (a j) * t ^ j‖ < ‖t‖ ^ i₀ := by
      intro j hj
      obtain ⟨hji, hjs⟩ := Finset.mem_erase.mp hj
      by_cases haj : a j = 0
      · simpa [haj] using hpos
      · rw [norm_mul, norm_finiteField_map f _ haj, one_mul, norm_zpow]
        exact zpow_lt_zpow_right_of_lt_one₀ ht0 ht1
          (lt_of_le_of_ne (hmin j hjs haj) (Ne.symm hji))
    rcases (s.erase i₀).eq_empty_or_nonempty with h | h
    · simpa [h] using hpos
    · obtain ⟨j, hj, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty h
        (fun i => f (a i) * t ^ i)
      exact hle.trans_lt (hterm j hj)
  rw [← Finset.add_sum_erase s _ hi₀,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hlead]; exact hrest.ne'),
    hlead, max_eq_left hrest.le]

end AlternatingAnalytic
-- Tengoku: root names of this library moved to Tengoku.AlternatingAnalyticCharacteristicP so they do not collide with other libraries (generated)

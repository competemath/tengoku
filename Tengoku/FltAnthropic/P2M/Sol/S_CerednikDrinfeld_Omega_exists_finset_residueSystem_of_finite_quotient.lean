import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_Omega_exists_finset_residueSystem_of_finite_quotient.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_Omega_exists_finset_residueSystem_of_finite_quotient.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_Omega_exists_finset_residueSystem_of_finite_quotient

set_option autoImplicit false

noncomputable section

namespace UAP

section PUTree

variable {R K₀ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
  [IsFractionRing R K₀] {ϖ : R}
  {K : Type} [Field K] [Algebra K₀ K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

/--
@isnad1 id=eq.1h5v.s8.cb540d82e803 from=translated src=- shape=dcaad085 vocab=0e30dab5
-/
theorem v_algebraMap_units_eq_one
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (u : Rˣ) :
    Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) = 1 := by
  apply le_antisymm (hint u)
  have h1 : algebraMap K₀ K (algebraMap R K₀ (u : R)) * algebraMap K₀ K (algebraMap R K₀ (↑u⁻¹ : R)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  calc (1 : Γ₀) = Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) *
        Valued.v (algebraMap K₀ K (algebraMap R K₀ (↑u⁻¹ : R))) := by rw [← Valuation.map_mul, h1, Valuation.map_one]
    _ ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) * 1 := mul_le_mul_right (hint _) _
    _ = _ := mul_one _

/--
@isnad1 id=ne.1h3v.s7.5a2cf9668069 from=translated src=- shape=c6d43a16 vocab=531db9f5
-/
theorem algebraMap_ne_zero_of_irreducible (hϖ : Irreducible ϖ) : algebraMap R K₀ ϖ ≠ 0 := fun h =>
  hϖ.ne_zero ((IsFractionRing.to_map_eq_zero_iff (K := K₀)).mp h)

/--
@isnad1 id=lt.1h5v.s8.cc7acc74060b from=translated src=- shape=7f35af98 vocab=147ddcf7
-/
theorem v_algebraMap_pos (hϖ : Irreducible ϖ) : 0 < Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) :=
  lt_of_le_of_ne zero_le (Ne.symm ((Valuation.ne_zero_iff _).mpr
    ((map_ne_zero _).mpr (algebraMap_ne_zero_of_irreducible hϖ))))

/--
@isnad1 id=lt.2h5v.s8.7bbcd65de50e from=translated src=- shape=3fe62867 vocab=1aa61e0c
-/
theorem v_algebraMap_lt_one (hϖ : Irreducible ϖ)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) < 1 := by
  by_contra h
  rw [not_lt] at h
  have hϖ0 := algebraMap_ne_zero_of_irreducible (K₀ := K₀) hϖ
  have hle : Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)⁻¹) ≤ 1 := by
    rw [map_inv₀, Valuation.map_inv, inv_le_one₀ (v_algebraMap_pos hϖ)]
    exact h
  obtain ⟨b, hb⟩ := hv _ hle
  apply hϖ.not_isUnit
  refine isUnit_iff_exists_inv.mpr ⟨b, ?_⟩
  apply IsFractionRing.injective R K₀
  rw [map_mul, hb, map_one, mul_inv_cancel₀ hϖ0]

/--
@isnad1 id=ex.3h6v.s9.24cccbee6799 from=translated src=- shape=c81be635 vocab=f6ad003d
-/
theorem exists_v_algebraMap_eq_zpow (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (a : K₀) (ha : a ≠ 0) :
    ∃ k : ℤ, Valued.v (algebraMap K₀ K a) = Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ k := by
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ ha
  refine ⟨k, ?_⟩
  rw [Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, Valuation.map_mul, map_zpow₀,
    v_algebraMap_units_eq_one hint, one_mul]

/--
@isnad1 id=or.3h6v.s9.6160e48ac9e9 from=translated src=- shape=5346bfdc vocab=5d321af6
-/
theorem v_algebraMap_le_or_one_le (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) (a : K₀) :
    Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ∨
      1 ≤ Valued.v (algebraMap K₀ K a) := by
  by_cases ha : a = 0
  · left; rw [ha, map_zero, Valuation.map_zero]; exact zero_le
  obtain ⟨k, hk⟩ := exists_v_algebraMap_eq_zpow hϖ hint a ha
  rw [hk]
  have h0 := v_algebraMap_pos (K₀ := K₀) (K := K) hϖ
  have h1 := (v_algebraMap_lt_one hϖ hv).le
  rcases le_or_gt k 0 with hk0 | hk0
  · exact Or.inr (one_le_zpow_of_nonpos₀ h0 h1 hk0)
  · left
    calc Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ k
        ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ h0 h1 (by omega)
      _ = _ := zpow_one _

/--
@isnad1 id=dvd.4h6v.s9.e49db93ab307 from=translated src=- shape=0e4c621b vocab=a0879e04
-/
theorem dvd_of_v_algebraMap_lt_one (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) (d : R)
    (hd : Valued.v (algebraMap K₀ K (algebraMap R K₀ d)) < 1) : ϖ ∣ d := by
  have hϖ0 := algebraMap_ne_zero_of_irreducible (K₀ := K₀) hϖ
  have h0 := v_algebraMap_pos (K₀ := K₀) (K := K) hϖ
  have hle : Valued.v (algebraMap K₀ K (algebraMap R K₀ d)) ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) := by
    rcases v_algebraMap_le_or_one_le hϖ hint hv (algebraMap R K₀ d) with h | h
    · exact h
    · exact absurd hd (not_lt.mpr h)
  have hint' : Valued.v (algebraMap K₀ K (algebraMap R K₀ d / algebraMap R K₀ ϖ)) ≤ 1 := by
    rw [map_div₀, Valuation.map_div, div_le_one₀ h0]
    exact hle
  obtain ⟨c, hc⟩ := hv _ hint'
  refine ⟨c, ?_⟩
  apply IsFractionRing.injective R K₀
  rw [map_mul, hc, mul_div_cancel₀ _ hϖ0]

/--
@isnad1 id=ex.3h5v.s10.dba87535c3a7 from=translated src=- shape=5bdd84c7 vocab=a06dbdbb
-/
theorem exists_finset_residue_representatives (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    ∃ T : Finset K₀, (∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1) ∧
      (∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1) ∧
      (∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 1 ≤ Valued.v (algebraMap K₀ K t - algebraMap K₀ K t')) := by
  classical
  haveI : Fintype (R ⧸ Ideal.span {ϖ}) := Fintype.ofFinite _
  set σ : R ⧸ Ideal.span {ϖ} → R := Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {ϖ})) with hσ
  have hσmk : ∀ q, Ideal.Quotient.mk (Ideal.span {ϖ}) (σ q) = q :=
    Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := Ideal.span {ϖ}))
  refine ⟨Finset.univ.image (fun q => algebraMap R K₀ (σ q)), ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    exact hint _
  · intro a ha
    obtain ⟨b, hb⟩ := hv a ha
    refine ⟨algebraMap R K₀ (σ (Ideal.Quotient.mk _ b)), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have hmem : b - σ (Ideal.Quotient.mk _ b) ∈ Ideal.span {ϖ} := by
      rw [← Ideal.Quotient.eq, hσmk]
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton.mp hmem
    rw [← hb, ← map_sub, ← map_sub, he, map_mul, map_mul, Valuation.map_mul]
    calc Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) * Valued.v (algebraMap K₀ K (algebraMap R K₀ e))
        ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) * 1 := mul_le_mul_right (hint e) _
      _ < 1 := by rw [mul_one]; exact v_algebraMap_lt_one hϖ hv
  · intro t ht t' ht' hne
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.mp ht'
    have hqq : q ≠ q' := fun h => hne (by rw [h])
    by_contra hlt
    rw [not_le] at hlt
    rw [← map_sub, ← map_sub] at hlt
    have hdvd := dvd_of_v_algebraMap_lt_one hϖ hint hv _ hlt
    apply hqq
    rw [← hσmk q, ← hσmk q', Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton.mpr hdvd

end PUTree

end UAP

end

/--
@isnad1 id=ex.3h5v.s10.4d5ea6803028 from=translated src=- shape=81daf19a vocab=a06dbdbb
-/
theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    ∃ T : Finset K₀, (∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1) ∧
      (∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1) ∧
      (∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 1 ≤ Valued.v (algebraMap K₀ K t - algebraMap K₀ K t')) := by
  exact UAP.exists_finset_residue_representatives hϖ hint hv

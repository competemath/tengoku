import Tengoku.Seed.RingTheory.MvPowerSeries.Inverse
import Tengoku.Seed.RingTheory.AdicCompletion.Noetherian

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPowerSeries_maximalIdeal_eq_map_C_sup_span_X.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPowerSeries_maximalIdeal_eq_map_C_sup_span_X

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

theorem coeff_dropVar (i : σ) (φ : MvPowerSeries σ R) (m : σ →₀ ℕ) :
    coeff m (dropVar i φ) = if m i = 0 then coeff m φ else 0 := rfl

theorem mem_span_X_of_constantCoeff_eq_zero [Finite σ] (φ : MvPowerSeries σ R)
    (hφ : constantCoeff φ = 0) : φ ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by
  classical
  haveI := Fintype.ofFinite σ

  suffices h : ∀ (s : Finset σ) (ψ : MvPowerSeries σ R), constantCoeff ψ = 0 →
      (∀ m : σ →₀ ℕ, ¬ (m.support ⊆ s) → coeff m ψ = 0) →
      ψ ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) by
    exact h Finset.univ φ hφ fun m hm => (hm (Finset.subset_univ _)).elim
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro ψ h0 hs
    have : ψ = 0 := by
      ext m
      by_cases hm : m = 0
      · subst hm; simpa using h0
      · rw [map_zero]
        refine hs m fun hsub => hm ?_
        ext j
        have : j ∉ m.support := fun hj => by simpa using hsub hj
        simpa [Finsupp.mem_support_iff] using this
    rw [this]; exact Ideal.zero_mem _
  | insert i s hi ih =>
    intro ψ h0 hs

    have hdiv : (X i : MvPowerSeries σ R) ∣ ψ - dropVar i ψ := by
      rw [X_dvd_iff]
      intro m hm
      rw [map_sub, coeff_dropVar, ite_eq_left hm, sub_self]
    obtain ⟨q, hq⟩ := hdiv
    have hrest : dropVar i ψ ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by
      refine ih _ ?_ ?_
      · rw [← coeff_zero_eq_constantCoeff_apply, coeff_dropVar, ite_eq_left (by simp),
          coeff_zero_eq_constantCoeff_apply, h0]
      · intro m hm
        rw [coeff_dropVar]
        split_ifs with hmi
        · refine hs m fun hsub => hm fun j hj => ?_
          have hj' := hsub hj
          rcases Finset.mem_insert.mp hj' with rfl | h
          · exact absurd hmi (by simpa [Finsupp.mem_support_iff] using hj)
          · exact h
        · rfl
    have : ψ = dropVar i ψ + X i * q := by rw [← hq]; ring
    rw [this]
    exact Ideal.add_mem _ hrest (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩))

theorem maximalIdeal_eq_map_C_sup_span_X [Finite σ] [IsLocalRing R] :
    maximalIdeal (MvPowerSeries σ R) =
      (maximalIdeal R).map (C (σ := σ) (R := R)) ⊔
        Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by
  apply le_antisymm
  · intro φ hφ
    rw [maximalIdeal_eq_comap, Ideal.mem_comap] at hφ
    have hsplit : φ = C (constantCoeff φ) + (φ - C (constantCoeff φ)) := by ring
    rw [hsplit]
    refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hφ))
      (Ideal.mem_sup_right (mem_span_X_of_constantCoeff_eq_zero _ ?_))
    rw [map_sub, constantCoeff_C, sub_self]
  · refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, maximalIdeal_eq_comap, Ideal.mem_comap, constantCoeff_C]
      exact ha
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, maximalIdeal_eq_comap, Ideal.mem_comap, constantCoeff_X]
      exact Ideal.zero_mem _

end M4cP4PS

theorem solution {σ : Type u} {R : Type v} [Finite σ]
    [CommRing R] [IsLocalRing R] :
    IsLocalRing.maximalIdeal (MvPowerSeries σ R) =
      (IsLocalRing.maximalIdeal R).map (MvPowerSeries.C (σ := σ) (R := R)) ⊔
        Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) :=
  M4cP4PS.maximalIdeal_eq_map_C_sup_span_X

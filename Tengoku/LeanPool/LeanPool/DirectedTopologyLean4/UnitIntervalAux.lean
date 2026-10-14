/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
module

public import Tengoku

/-!
# LeanPool.DirectedTopologyLean4.UnitIntervalAux
-/

@[expose] public section

/-
  This file contains lemmas about
  * elements being contained in the unit interval.
  * relations between elements in the unit interval.
-/

open scoped unitInterval

namespace unitIAux

/--
@isnad1 id=le.0h1v.s5.905f5dd0ea1b from=translated src=- shape=ea96b1d4 vocab=08f112d4
-/
lemma zero_le (T : I) : ⟨0, unitInterval.zero_mem⟩ ≤ T := Subtype.coe_le_coe.mp T.2.1
/--
@isnad1 id=le.0h1v.s5.eb54fc222a36 from=translated src=- shape=42fdb6f5 vocab=25665f6e
-/
lemma le_one (T : I) : T ≤ ⟨1, unitInterval.one_mem⟩:= Subtype.coe_le_coe.mp T.2.2

/--
@isnad1 id=lt.1h1v.s6.6d0c96a72252 from=translated src=- shape=d8c02f56 vocab=58fb4af0
-/
lemma double_pos_of_pos {T : I} (hT₀ : 0 < T) : 0 < (2 * T : ℝ) :=
  mul_pos two_pos hT₀
/--
@isnad1 id=lt.1h1v.s6.cd4da7756006 from=translated src=- shape=e7173398 vocab=5bdb8e49
-/
lemma double_sigma_pos_of_lt_one {T : I} (hT₁ : T < 1) : 0 < (2 * (1 - T) : ℝ) :=
  mul_pos two_pos (by simpa using hT₁)

/--
@isnad1 id=mem.1h1v.s6.9c810dac4d50 from=translated src=- shape=391fdd25 vocab=2f0ebfb1
-/
lemma double_mem_I {t : I} (ht : ↑t ≤ (2⁻¹ : ℝ)) : 2 * (t : ℝ) ∈ I :=
  ⟨by nlinarith [t.2.1], by nlinarith⟩

/--
@isnad1 id=mem.1h1v.s6.55d14983064a from=translated src=- shape=90c8b431 vocab=89319b60
-/
lemma double_sub_one_mem_I {t : I} (ht : (2⁻¹ : ℝ) ≤ ↑t) : 2 * (t : ℝ) - 1 ∈ I :=
  ⟨by nlinarith, by nlinarith [t.2.2]⟩

/--
@isnad1 id=le.1h3v.s7.c2442adad0a1 from=translated src=- shape=ca9209e9 vocab=65e74aec
-/
lemma interp_left_le_of_le (T : I) {a b : I} (hab : a ≤ b) :
    (σ T : ℝ) * ↑a + ↑T ≤ (σ T : ℝ) * ↑b + ↑T := by
  have hσT : (0 : ℝ) ≤ σ T := (σ T).2.1
  have hab' : (a : ℝ) ≤ b := hab
  nlinarith

section

noncomputable section

/--
@isnad1 id=mem.0h0v.s4.0c2557e7e088 from=translated src=- shape=4d462cc7 vocab=88a08301
-/
lemma half_mem_I : (2⁻¹ : ℝ) ∈ I :=
⟨inv_nonneg.mpr zero_le_two, inv_le_one_of_one_le₀ one_le_two⟩

/-- The midpoint `1/2` of the unit interval. -/
abbrev halfI : I := ⟨(2⁻¹ : ℝ), half_mem_I⟩

/--
@isnad1 id=ex.2h3v.s7.aa55e466c1f7 from=translated src=- shape=c99e2097 vocab=b3c9d37a
-/
lemma has_T_half {t₀ t₁ : I} (γ : Path t₀ t₁) (ht₀ : ↑t₀ < (2⁻¹ : ℝ)) (ht₁ : ↑t₁ > (2⁻¹ : ℝ)) :
  ∃ (T : I),  0 < T ∧ T < 1 ∧ (γ T) = halfI := by
  have : γ.toFun 0 ≤ halfI := by rw [γ.source']; exact Subtype.coe_le_coe.mp (le_of_lt ht₀)
  have h₀ : ∃ (t : I), γ t ≤ halfI := ⟨0, this⟩
  have : halfI ≤ γ.toFun 1 := by rw [γ.target']; exact Subtype.coe_le_coe.mp (le_of_lt ht₁)
  have h₁ : ∃ (t : I), halfI ≤ γ t := ⟨1, this⟩
  have hy := Set.mem_range.mp (mem_range_of_exists_le_of_exists_ge γ.continuous_toFun h₀ h₁)
  obtain ⟨T, hT⟩ := hy
  use T
  have hT₀ : 0 ≠ T := by
    rintro ⟨rfl⟩
    simp_all
  have hT₁ : T ≠ 1 := by
    rintro ⟨rfl⟩
    simp_all
  exact ⟨lt_iff_le_and_ne.mpr ⟨T.2.1, hT₀⟩, lt_iff_le_and_ne.mpr ⟨T.2.2, hT₁⟩, hT⟩
end

end

end unitIAux

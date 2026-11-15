import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_LocalHeckeInstance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace LocalNewvector

variable (p : ℕ) [Fact p.Prime]

def IsUnramified (μ : ℚ_[p]ˣ →* ℂˣ) : Prop :=
  ∀ u : ℚ_[p]ˣ, ‖(u : ℚ_[p])‖ = 1 → μ u = 1

/--
@isnad1 id=isunrami.0h1v.s8.0f56a74a4daf from=translated src=- shape=756fed53 vocab=458988de
-/
theorem isUnramified_one : IsUnramified p (1 : ℚ_[p]ˣ →* ℂˣ) := fun _ _ => rfl

def unitValuation : ℚ_[p]ˣ →* Multiplicative ℤ where
  toFun u := Multiplicative.ofAdd (u : ℚ_[p]).valuation
  map_one' := by simp [Padic.valuation_one]
  map_mul' u v := by
    simp only [Units.val_mul]
    rw [Padic.valuation_mul u.ne_zero v.ne_zero, ofAdd_add]

/--
@isnad1 id=eq.0h2v.s8.0bfd6dd7a9fb from=translated src=- shape=73bb8a6f vocab=f3973427
-/
@[simp] theorem unitValuation_apply (u : ℚ_[p]ˣ) :
    Multiplicative.toAdd (unitValuation p u) = (u : ℚ_[p]).valuation := rfl

def valChar (s : ℂˣ) : ℚ_[p]ˣ →* ℂˣ :=
  (zpowersHom ℂˣ s).comp (unitValuation p)

/--
@isnad1 id=eq.0h3v.s8.a01961f03c96 from=translated src=- shape=59f2ebf5 vocab=18424016
-/
@[simp] theorem valChar_apply (s : ℂˣ) (u : ℚ_[p]ˣ) :
    valChar p s u = s ^ (u : ℚ_[p]).valuation := rfl

/--
@isnad1 id=isunrami.0h2v.s4.94bb67607034 from=translated src=- shape=9682e38e vocab=50b9a645
-/
theorem isUnramified_valChar (s : ℂˣ) : IsUnramified p (valChar p s) := by
  intro u hu
  rw [valChar_apply]
  have hv0 : (u : ℚ_[p]).valuation = 0 := by
    have hp_ne_one : (p : ℝ) ≠ 1 := mod_cast (Fact.out : p.Prime).ne_one
    have hp_pos : (0 : ℝ) < p := mod_cast (Fact.out : p.Prime).pos
    have := Padic.norm_eq_zpow_neg_valuation u.ne_zero
    rw [hu] at this
    have := (zpow_right_inj₀ hp_pos hp_ne_one).mp
      (this.symm.trans (zpow_zero (p : ℝ)).symm)
    omega
  rw [hv0, zpow_zero]

/--
@isnad1 id=ne.1h2v.s8.b5cf77cfd863 from=translated src=- shape=437aee52 vocab=e5b8d684
-/
theorem valChar_ne_one {s : ℂˣ} (hs : s ≠ 1) : valChar p s ≠ 1 := by
  intro h
  have hpne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp1 : (p : ℚ_[p]).valuation = 1 := by
    have := Padic.valuation_p (p := p); exact_mod_cast this
  have := DFunLike.congr_fun h (Units.mk0 (p : ℚ_[p]) hpne)
  rw [valChar_apply, Units.val_mk0, hp1, zpow_one, MonoidHom.one_apply] at this
  exact hs this

/--
@isnad1 id=ex.0h1v.s9.af482c3b260c from=translated src=- shape=8c208228 vocab=458988de
-/
theorem exists_isUnramified_ne_one : ∃ μ : ℚ_[p]ˣ →* ℂˣ, IsUnramified p μ ∧ μ ≠ 1 := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  refine ⟨valChar p (Units.mk0 2 h2), isUnramified_valChar p _, valChar_ne_one p ?_⟩
  intro h1
  have := Units.val_eq_one.mpr h1
  simp only [Units.val_mk0] at this
  exact (by norm_num : (2 : ℂ) ≠ 1) this

def higherUnits (n : ℕ) : Set ℚ_[p]ˣ :=
  {u | ‖(u : ℚ_[p])‖ = 1 ∧ (n = 0 ∨ ‖(u : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ)))}

/--
@isnad1 id=iff.0h3v.s7.dc48ceb72374 from=translated src=- shape=424df068 vocab=7c0e3e96
-/
theorem mem_higherUnits_iff {n : ℕ} {u : ℚ_[p]ˣ} :
    u ∈ higherUnits p n ↔ ‖(u : ℚ_[p])‖ = 1 ∧ (n = 0 ∨ ‖(u : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ))) :=
  Iff.rfl

/--
@isnad1 id=iff.0h2v.s7.d38b100c7d13 from=translated src=- shape=27f1e675 vocab=fcc84edd
-/
theorem mem_higherUnits_zero_iff {u : ℚ_[p]ˣ} : u ∈ higherUnits p 0 ↔ ‖(u : ℚ_[p])‖ = 1 := by
  simp [mem_higherUnits_iff]

/--
@isnad1 id=mem.0h2v.s7.7464d17c2038 from=translated src=- shape=c243ed13 vocab=bec7f73f
-/
theorem one_mem_higherUnits (n : ℕ) : (1 : ℚ_[p]ˣ) ∈ higherUnits p n := by
  refine ⟨by simp, ?_⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · exact Or.inl h
  · right
    simp only [Units.val_one, sub_self, norm_zero]
    positivity

/--
@isnad1 id=antitone.0h1v.s7.ff8dfc276eb7 from=translated src=- shape=6a932253 vocab=c3ca7e6d
-/
theorem higherUnits_antitone : Antitone (higherUnits p) := by
  intro m n hmn u hu
  obtain ⟨hnorm, hball⟩ := hu
  refine ⟨hnorm, ?_⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exact Or.inl hm
  · right
    rcases hball with hn0 | hle
    · omega
    · have hp1 : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (Nat.Prime.one_lt (Fact.out (p := p.Prime))).le
      exact hle.trans (zpow_le_zpow_right₀ hp1 (by omega))

def HasCharConductor (μ : ℚ_[p]ˣ →* ℂˣ) (c : ℕ) : Prop :=
  (∀ u ∈ higherUnits p c, μ u = 1) ∧ ∀ m < c, ∃ u ∈ higherUnits p m, μ u ≠ 1

/--
@isnad1 id=iff.0h2v.s6.7a3ebe5e351e from=translated src=- shape=bf3a42a1 vocab=995db9b0
-/
theorem hasCharConductor_zero_iff_isUnramified {μ : ℚ_[p]ˣ →* ℂˣ} :
    HasCharConductor p μ 0 ↔ IsUnramified p μ := by
  constructor
  · intro h u hu
    exact h.1 u ((mem_higherUnits_zero_iff p).mpr hu)
  · intro h
    exact ⟨fun u hu => h u ((mem_higherUnits_zero_iff p).mp hu), fun m hm => absurd hm (Nat.not_lt_zero m)⟩

/--
@isnad1 id=eq.2h4v.s6.b0bdf95ebe7e from=translated src=- shape=5c965e33 vocab=7bdc9d0a
-/
theorem hasCharConductor_unique {μ : ℚ_[p]ˣ →* ℂˣ} {c c' : ℕ}
    (h : HasCharConductor p μ c) (h' : HasCharConductor p μ c') : c = c' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨u, hu, hne1⟩ := h'.2 c hlt
    exact hne1 (h.1 u hu)
  · obtain ⟨u, hu, hne1⟩ := h.2 c' hgt
    exact hne1 (h'.1 u hu)

/--
@isnad1 id=hascharc.0h1v.s8.264813665c03 from=translated src=- shape=498a9e45 vocab=7bdc9d0a
-/
theorem hasCharConductor_one_zero : HasCharConductor p (1 : ℚ_[p]ˣ →* ℂˣ) 0 :=
  (hasCharConductor_zero_iff_isUnramified p).mpr (isUnramified_one p)

/--
@isnad1 id=hascharc.0h2v.s4.926df91af179 from=translated src=- shape=9275c2f3 vocab=b7059c10
-/
theorem hasCharConductor_valChar_zero (s : ℂˣ) : HasCharConductor p (valChar p s) 0 :=
  (hasCharConductor_zero_iff_isUnramified p).mpr (isUnramified_valChar p s)

/--
@isnad1 id=not.0h2v.s8.f2b4bcd15239 from=translated src=- shape=84612c9d vocab=c67da27d
-/
theorem not_hasCharConductor_one_succ (c : ℕ) : ¬ HasCharConductor p (1 : ℚ_[p]ˣ →* ℂˣ) (c + 1) := by
  rintro ⟨-, hmin⟩
  obtain ⟨u, -, hne⟩ := hmin c (Nat.lt_succ_self c)
  exact hne rfl

end LocalNewvector

end

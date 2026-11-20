/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
TODOs:
  * General proof cleanup
  * File docstring
  * Does this generalize beyond I?  Is it useful to do so?
    Can we, for instance, just take an arbitrary path in a path-connected space?
-/
namespace Tengoku.LeanTnorms end Tengoku.LeanTnorms open Tengoku.LeanTnorms
open unitInterval

/--
@isnad1 id=mem.3h5v.s6.094dc1debcd1 from=translated src=- shape=6e8a70cd vocab=72864702
-/
lemma _root_.Tengoku.LeanTnorms.interpolate_mem {a b c : ℝ} (p q : I) (hab : a ≤ b) (hbc : b ≤ c) (hac : a < c) :
    (q.1 - p.1) / (c - a) * (b - a) + p.1 ∈ I := by
  have hp := p.2
  have hq := q.2
  rw [Set.mem_Icc] at hp hq ⊢
  constructor
  · by_cases hpq : p.1 ≤ q.1
    · suffices 0 ≤ (q.1 - p.1) / (c - a) * (b - a) by grind
      refine mul_nonneg (div_nonneg ?_ ?_) ?_ <;> grind
    · rw [← neg_le_iff_add_nonneg, mul_comm_div]
      trans (q.1 - p.1)
      · grind
      · conv => lhs; rw [← mul_one (q.1-p.1)]
        refine mul_le_mul_of_nonpos_left ?_ ?_
        · rw [div_le_one] <;> grind
        · grind
  · rw [mul_comm_div]
    by_cases hpq : p.1 ≤ q.1
    · suffices (q.1 - p.1) * ((b - a) / (c - a)) ≤ q.1 - p.1 by grind
      refine mul_le_of_le_one_right ?_ ?_
      · grind
      · rw [div_le_one] <;> grind
    · suffices (q.1 - p.1) * ((b - a) / (c - a)) ≤ 0 by grind
      refine mul_nonpos_of_nonpos_of_nonneg ?_ ?_
      · grind
      · exact div_nonneg (by grind) (by grind)

noncomputable
def _root_.Tengoku.LeanTnorms.interpolate (a c : ℝ) (p q : I) : ℝ → I :=
  fun b ↦ if habc : ¬a ≤ b ∨ ¬b ≤ c ∨ ¬a < c then 0 else
  ⟨(q.1 - p.1) / (c - a) * (b - a) + p.1, by
    simp only [not_le, not_lt, not_or] at habc
    obtain ⟨hab, hbc, hac⟩ := habc
    exact interpolate_mem p q hab hbc hac⟩

noncomputable
abbrev _root_.Tengoku.LeanTnorms.interpolate_n (d : ℕ → ℝ) (p : ℕ → I) (n : ℕ) := interpolate (d (n + 1)) (d n) (p (n + 1)) (p n)

/--
@isnad1 id=eq.3h4v.s5.164e7db6a56a from=translated src=- shape=2bbe75dc vocab=8ce9aa1e
-/
@[simp]
lemma _root_.Tengoku.LeanTnorms.interpolate_self (a b c : ℝ) (p : I) (hab : a ≤ b) (hbc : b ≤ c) (hac : a < c) :
    interpolate a c p p b = p := by grind [interpolate]

/--
@isnad1 id=eq.1h4v.s4.fd6565714680 from=translated src=- shape=a538438d vocab=41e6e64c
-/
@[simp]
lemma _root_.Tengoku.LeanTnorms.interpolate_right (a b : ℝ) (p q : I) (hab : a < b) :
    (interpolate a b p q) b = q := by grind [interpolate]

/--
@isnad1 id=eq.1h4v.s4.ae07d2cf90e1 from=translated src=- shape=b7a28ce8 vocab=41e6e64c
-/
@[simp]
lemma _root_.Tengoku.LeanTnorms.interpolate_left (a b : ℝ) (p q : I) (hab : a < b) :
    (interpolate a b p q) a = p := by grind [interpolate]

/--
@isnad1 id=le.3h5v.s6.01f52deb6776 from=translated src=- shape=8311cadd vocab=a52638e6
-/
lemma _root_.Tengoku.LeanTnorms.min_le_interpolate (a b c : ℝ) (p q : I) (hab : a ≤ b) (hbc : b ≤ c) (hac : a < c) :
    min p q ≤ interpolate a c p q b := by
  simp [interpolate, hab, hbc, hac]
  field_simp
  simp [mul_div_assoc]
  rw [Subtype.mk_le_mk, Subtype.mk_le_mk]
  have habc0 : 0 ≤ (b - a) / (c - a) := by
    refine div_nonneg (by grind) (by grind)
  have habc1 : (b - a) / (c - a) ≤ 1 := by
    rw [div_le_one] <;> grind
  by_cases! hpq : p < q
  · have h : 0 ≤ (q.1 - p.1) * ((b - a) / (c - a)) := by
      refine mul_nonneg ?_ habc0
      rw [sub_nonneg, Subtype.coe_le_coe]
      exact le_of_lt hpq
    grind
  · have h : q.1 - p.1 ≤ (q.1 - p.1) * ((b - a) / (c - a)) := by
      refine le_mul_of_le_one_right ?_ habc1
      rw [sub_nonpos, Subtype.coe_le_coe]
      exact hpq
    grind

/--
@isnad1 id=le.3h5v.s6.19f6c5cb24de from=translated src=- shape=a6de32b5 vocab=a0008b2e
-/
lemma _root_.Tengoku.LeanTnorms.interpolate_le_max (a b c : ℝ) (p q : I) (hab : a ≤ b) (hbc : b ≤ c) (hac : a < c) :
    interpolate a c p q b ≤ max p q := by
  simp [interpolate, hab, hbc, hac]
  field_simp
  simp [mul_div_assoc]
  rw [Subtype.mk_le_mk, Subtype.mk_le_mk]
  have habc0 : 0 ≤ (b - a) / (c - a) := by
    refine div_nonneg (by grind) (by grind)
  have habc1 : (b - a) / (c - a) ≤ 1 := by
    rw [div_le_one] <;> grind
  by_cases! hpq : p < q
  · have h : (q.1 - p.1) * ((b - a) / (c - a)) ≤ q.1 - p.1 := by
      refine mul_le_of_le_one_right ?_ habc1
      rw [sub_nonneg, Subtype.coe_le_coe]
      exact le_of_lt hpq
    grind
  · have h : (q.1 - p.1) * ((b - a) / (c - a)) ≤ 0 := by
      refine mul_nonpos_of_nonpos_of_nonneg ?_ habc0
      rw [sub_nonpos, Subtype.coe_le_coe]
      exact hpq
    grind

/--
@isnad1 id=eq.3h5v.s6.66af00130c5a from=translated src=- shape=915efbc5 vocab=2b7ba277
-/
@[simp]
lemma _root_.Tengoku.LeanTnorms.interpolate_add (a b c : ℝ) (p q : I) (hab : a ≤ b) (hbc : b ≤ c) (hac : a < c) :
    (interpolate a c p q b).1 + (interpolate a c q p b).1 = p.1 + q := by
  simp [interpolate, hab, hbc, hac]
  ring

/--
@isnad1 id=continuo.0h4v.s5.0dfaf78e092d from=translated src=- shape=7fef3bd0 vocab=ddec3c09
-/
lemma _root_.Tengoku.LeanTnorms.interpolate_continuousOn (a c : ℝ) (p q : I) :
    ContinuousOn (interpolate a c p q) (Set.Icc a c) := by
  by_cases! hac : ¬a ≤ c
  · simp [hac]
  by_cases! hac' : a = c
  · simp [hac']
  have hac : a < c := lt_of_le_of_ne hac hac'
  intro b hb
  rw [Set.mem_Icc] at hb
  obtain ⟨hab, hbc⟩ := hb
  have h : ContinuousWithinAt (fun x ↦ (q.1 - p.1) / (c - a) * (x - a) + p.1) (Set.Icc a c) b := by
    refine Continuous.continuousWithinAt ?_
    refine Continuous.add ?_ continuous_const
    refine Continuous.mul continuous_const ?_
    exact continuous_add_const (-a)
  rw [Metric.continuousWithinAt_iff] at ⊢ h
  intro ε hε
  specialize h ε hε
  obtain ⟨δ, hd, h⟩ := h
  use δ
  constructor
  · exact hd
  intro x hx hxb
  specialize h hx hxb
  rw [Set.mem_Icc] at hx
  simp [interpolate, hab, hbc, hac, hx.1, hx.2]
  exact h

/--
@isnad1 id=eq.5h6v.s7.91e8fb0182b1 from=translated src=- shape=6e5ad2ce vocab=2c7cab70
-/
lemma _root_.Tengoku.LeanTnorms.interpolate_dist {a b x y : ℝ} {p q : I} (hab : a < b)
    (hax : a ≤ x) (hxb : x ≤ b) (hay : a ≤ y) (hyb : y ≤ b) :
    dist (interpolate a b p q x) (interpolate a b p q y) =
    |q.1 - p.1| / (b - a) * (dist x y) := by
  simp [interpolate, hab, hax, hxb, hay, hyb, Real.dist_eq, Subtype.dist_eq]
  field_simp
  rw [abs_div, abs_mul]
  grind

/--
@isnad1 id=eq.3h5v.s7.40281acf2372 from=translated src=- shape=8ad97bad vocab=2c7cab70
-/
lemma _root_.Tengoku.LeanTnorms.interpolate_dist_left {a b x : ℝ} {p q : I} (hab : a < b)
    (hax : a ≤ x) (hxb : x ≤ b) :
    dist p (interpolate a b p q x) =
    |q.1 - p.1| / (b - a) * dist x a := by
  simp [interpolate, hab, hax, hxb, Real.dist_eq, Subtype.dist_eq]
  grind

/--
@isnad1 id=eq.3h5v.s7.1953c6ce467a from=translated src=- shape=2c2c73f3 vocab=2c7cab70
-/
lemma _root_.Tengoku.LeanTnorms.interpolate_dist_right {a b x : ℝ} {p q : I} (hab : a < b)
    (hax : a ≤ x) (hxb : x ≤ b) :
    dist (interpolate a b p q x) q =
    |q.1 - p.1| / (b - a) * dist x b := by
  simp [interpolate, hab, hax, hxb, Real.dist_eq, Subtype.dist_eq]
  rw [← sub_sub_eq_add_sub]
  field_simp
  rw [abs_mul, mul_div_assoc]
  congr
  rw [show 1 = (b - a) / (b - a) by grind, div_sub_div_same, abs_div]
  grind

/--
@isnad1 id=uniformc.1h4v.s6.0eb7be9a237c from=translated src=- shape=9318fceb vocab=f69e59ce
-/
lemma _root_.Tengoku.LeanTnorms.ite_interpolate_uniformContinuous (a b : ℝ) (p q : I) (hab : a < b) :
    UniformContinuous (fun x ↦ if x ≤ a then p else
      if a ≤ x ∧ x ≤ b then interpolate a b p q x else q) := by
  by_cases! hpq : p = q
  · subst hpq
    suffices (fun x ↦ p) = (fun x ↦ if x ≤ a then p else if a ≤ x ∧ x ≤ b then
        interpolate a b p p x else p) by
      rw [← this]
      exact uniformContinuous_const
    ext x
    split_ifs
    · rfl
    · rename_i hxa hx
      rw [interpolate_self _ _ _ _ hx.1 hx.2 hab]
    · rfl
  rw [Metric.uniformContinuous_iff]
  intro ε he
  wlog he' : ε ≤ |q.1 - p.1| generalizing ε
  · specialize this (|q.1 - p.1|) (by grind) (by rfl)
    grind
  have heab : ε * (b - a) / |q.1 - p.1| ≤ b - a := by
    rw [div_le_iff₀' (by grind), mul_le_mul_iff_left₀ (by grind)]
    exact he'
  have hpqba : 0 < |q.1 - p.1| / (b - a) := div_pos (by grind) (by grind)
  use ε * (b - a) / |q.1 - p.1|
  constructor
  · refine div_pos ?_ (by grind)
    refine mul_pos he (by grind)
  intro x y hxy
  split_ifs
  · simp [he]
  · rename_i hy
    rw [interpolate_dist_left hab hy.1 hy.2, ← lt_div_iff₀' hpqba, div_div_eq_mul_div]
    exact lt_of_le_of_lt (by grind [Real.dist_eq]) hxy
  · grind [Real.dist_eq]
  · rename_i hx _
    rw [dist_comm, interpolate_dist_left hab hx.1 hx.2, ← lt_div_iff₀' hpqba, div_div_eq_mul_div]
    exact lt_of_le_of_lt (by grind [Real.dist_eq]) hxy
  · rename_i hx _ hy
    rw [interpolate_dist hab hx.1 hx.2 hy.1 hy.2, ← lt_div_iff₀' hpqba, div_div_eq_mul_div]
    exact hxy
  · rename_i hx _ _
    rw [interpolate_dist_right hab hx.1 hx.2, ← lt_div_iff₀' hpqba, div_div_eq_mul_div]
    exact lt_of_le_of_lt (by grind [Real.dist_eq]) hxy
  · grind [Real.dist_eq]
  · rename_i hy
    rw [dist_comm, interpolate_dist_right hab hy.1 hy.2, ← lt_div_iff₀' hpqba, div_div_eq_mul_div]
    exact lt_of_le_of_lt (by grind [Real.dist_eq]) hxy
  · simp [he]
-- Tengoku: root names of this library moved to Tengoku.LeanTnorms so they do not collide with other libraries (generated)

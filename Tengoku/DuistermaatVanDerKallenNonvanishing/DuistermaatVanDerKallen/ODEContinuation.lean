/-
SPDX-License-Identifier: Apache-2.0
The local Picard construction is adapted from mathlib's
Analysis/ODE/ExistUnique.lean and Analysis/ODE/PicardLindelof.lean.
Copyright (c) 2026 Winston Yin. All rights reserved.
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Authors of the upstream proofs: Yury Kudryashov, Winston Yin.
Modified here to retain range control and prove compact-domain continuation.
See LICENSES/Apache-2.0.txt and THIRD_PARTY_NOTICES.md.
-/

import Tengoku.Seed.Analysis.ODE.ExistUnique

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Compact-domain continuation for autonomous real ODEs. The compact set lies
inside the regular domain; boundedness of positions alone is not the hypothesis.
The local Picard construction retains its closed-ball range bound. -/

open Set Metric Filter
open scoped Topology NNReal

namespace DuistermaatVanDerKallen

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Smoothness near a compact set gives one Lipschitz constant on that set,
without any convexity assumption on the compact set itself.-/
theorem smooth_lipschitz_on_compact {V : E → E} {K : Set E}
    (hK : IsCompact K) (hV : ∀ x ∈ K, ContDiffAt ℝ 1 V x) :
    ∃ L, LipschitzOnWith L V K := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  intro x hx
  obtain ⟨L, s, hs, hL⟩ := (hV x hx).exists_lipschitzOnWith
  exact ⟨L, s, mem_nhdsWithin_of_mem_nhds hs, hL⟩

omit [CompleteSpace E] in
/-- Uniqueness on a closed interval for curves in an open smooth domain.
Only their compact images are used to obtain a common Lipschitz constant.-/
theorem ode_unique_on_closed_interval {V : E → E} {U : Set E}
    (hV : ∀ x ∈ U, ContDiffAt ℝ 1 V x)
    {γ η : ℝ → E} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hη : ContinuousOn η (Icc a b))
    (hdγ : ∀ t ∈ Ico a b, HasDerivAt γ (V (γ t)) t)
    (hdη : ∀ t ∈ Ico a b, HasDerivAt η (V (η t)) t)
    (hmemγ : MapsTo γ (Icc a b) U) (hmemη : MapsTo η (Icc a b) U)
    (heq : γ a = η a) : EqOn γ η (Icc a b) := by
  let K := γ '' Icc a b ∪ η '' Icc a b
  have hK : IsCompact K := (isCompact_Icc.image_of_continuousOn hγ).union (isCompact_Icc.image_of_continuousOn hη)
  have hKU : K ⊆ U := union_subset (image_subset_iff.mpr hmemγ) (image_subset_iff.mpr hmemη)
  obtain ⟨L, hL⟩ := smooth_lipschitz_on_compact hK (fun x hx => hV x (hKU hx))
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => K) (fun _ _ => hL)
    hγ (fun t ht => (hdγ t ht).hasDerivWithinAt)
    (fun t ht => Or.inl ⟨t, Ico_subset_Icc_self ht, rfl⟩)
    hη (fun t ht => (hdη t ht).hasDerivWithinAt)
    (fun t ht => Or.inr ⟨t, Ico_subset_Icc_self ht, rfl⟩) heq

omit [CompleteSpace E] in
/-- Uniqueness on an open interval, with any initial time in that interval.-/
theorem ode_unique_on_open_interval {V : E → E} {U : Set E}
    (hV : ∀ x ∈ U, ContDiffAt ℝ 1 V x)
    {γ η : ℝ → E} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hγ : ∀ t ∈ Ioo a b, γ t ∈ U ∧ HasDerivAt γ (V (γ t)) t)
    (hη : ∀ t ∈ Ioo a b, η t ∈ U ∧ HasDerivAt η (V (η t)) t)
    (heq : γ t₀ = η t₀) : EqOn γ η (Ioo a b) := by
  intro t ht
  let l := (a + min t t₀) / 2
  let r := (max t t₀ + b) / 2
  have hal : a < l := by dsimp [l]; linarith [lt_min ht.1 ht₀.1]
  have hrb : r < b := by dsimp [r]; linarith [max_lt ht.2 ht₀.2]
  have hlt : l < t := by dsimp [l]; linarith [min_le_left t t₀, ht.1]
  have hlt₀ : l < t₀ := by dsimp [l]; linarith [min_le_right t t₀, ht₀.1]
  have htr : t < r := by dsimp [r]; linarith [le_max_left t t₀, ht.2]
  have ht₀r : t₀ < r := by dsimp [r]; linarith [le_max_right t t₀, ht₀.2]
  have hsub : Icc l r ⊆ Ioo a b := fun x hx => ⟨hal.trans_le hx.1, hx.2.trans_lt hrb⟩
  let K := γ '' Icc l r ∪ η '' Icc l r
  have hcγ : ContinuousOn γ (Icc l r) := fun x hx => (hγ x (hsub hx)).2.continuousAt.continuousWithinAt
  have hcη : ContinuousOn η (Icc l r) := fun x hx => (hη x (hsub hx)).2.continuousAt.continuousWithinAt
  have hK : IsCompact K := (isCompact_Icc.image_of_continuousOn hcγ).union
    (isCompact_Icc.image_of_continuousOn hcη)
  have hKU : K ⊆ U := by
    rintro x (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact (hγ u (hsub hu)).1
    · exact (hη u (hsub hu)).1
  obtain ⟨L, hL⟩ := smooth_lipschitz_on_compact hK (fun x hx => hV x (hKU hx))
  exact ODE_solution_unique_of_mem_Ioo (s := fun _ => K) (fun _ _ => hL) ⟨hlt₀, ht₀r⟩
    (fun u hu => ⟨(hγ u (hsub (Ioo_subset_Icc_self hu))).2,
      Or.inl ⟨u, Ioo_subset_Icc_self hu, rfl⟩⟩)
    (fun u hu => ⟨(hη u (hsub (Ioo_subset_Icc_self hu))).2,
      Or.inr ⟨u, Ioo_subset_Icc_self hu, rfl⟩⟩) heq ⟨hlt, htr⟩

end
end DuistermaatVanDerKallen

/-
SPDX-License-Identifier: Apache-2.0
Adapted from this project's ODEContinuation.lean. The inherited upstream notices
are retained here; the local driven Picard construction is implemented separately.
Copyright (c) 2026 Winston Yin. All rights reserved.
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Authors of the upstream proofs: Yury Kudryashov, Winston Yin.
Modified here for continuous scalar time-dependent velocities, using compactness
in both time and the regular spatial domain.
See LICENSES/Apache-2.0.txt and THIRD_PARTY_NOTICES.md.
-/

import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.DrivenLocalODE
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.ODEContinuation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Uniqueness and compact-domain continuation for a continuous scalar driving
velocity. Compactness controls both time and the regular spatial domain. -/

open Set Metric Filter
open scoped Topology

namespace DuistermaatVanDerKallen
noncomputable section

/-- Spatial Lipschitz control uniform for a continuous velocity on a compact
time set and positions in a compact subset of the regular torus.-/
theorem laurent_driven_lipschitz_on_compact {d : ℕ} (f : MultiLaurent d)
    (v : ℝ → ℂ) (hv : Continuous v) {J : Set ℝ} {K : Set (Fin d → ℂ)}
    (hJ : IsCompact J) (hK : IsCompact K) (hKU : K ⊆ laurentRegularDomain f) :
    ∃ L, ∀ t ∈ J, LipschitzOnWith L (laurentVectorField f (v t)) K := by
  let S : Set (ℂ × (Fin d → ℂ)) := (v '' J) ×ˢ K
  let V : ℂ × (Fin d → ℂ) → (Fin d → ℂ) := fun p => laurentVectorField f p.1 p.2
  have hS : IsCompact S := (hJ.image hv).prod hK
  have hloc : LocallyLipschitzOn S V := by
    intro p hp
    have h : ContDiffAt ℝ 1 V p :=
      (polynomialVectorField_contDiffAt (laurentRepresentative f) (hKU hp.2)).of_le le_top
    obtain ⟨L, U, hU, hL⟩ := h.exists_lipschitzOnWith
    exact ⟨L, U, mem_nhdsWithin_of_mem_nhds hU, hL⟩
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hS
  refine ⟨L, ?_⟩
  intro t ht
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro x hx y hy
  have hh := hL.dist_le_mul (v t, x) (show (v t, x) ∈ S from ⟨⟨t, ht, rfl⟩, hx⟩)
    (v t, y) (show (v t, y) ∈ S from ⟨⟨t, ht, rfl⟩, hy⟩)
  simpa only [V, Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hh

/-- Uniqueness of regular time-dependent horizontal curves on an open interval.-/
theorem laurent_driven_unique_on_open_interval {d : ℕ} (f : MultiLaurent d)
    (v : ℝ → ℂ) (hv : Continuous v)
    {γ η : ℝ → Fin d → ℂ} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hγ : ∀ t ∈ Ioo a b, γ t ∈ laurentRegularDomain f ∧
      HasDerivAt γ (laurentVectorField f (v t) (γ t)) t)
    (hη : ∀ t ∈ Ioo a b, η t ∈ laurentRegularDomain f ∧
      HasDerivAt η (laurentVectorField f (v t) (η t)) t)
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
  have hKU : K ⊆ laurentRegularDomain f := by
    rintro x (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact (hγ u (hsub hu)).1
    · exact (hη u (hsub hu)).1
  obtain ⟨L, hL⟩ := laurent_driven_lipschitz_on_compact f v hv isCompact_Icc hK hKU
  exact ODE_solution_unique_of_mem_Ioo (s := fun _ => K) (fun u hu => hL u (Ioo_subset_Icc_self hu)) ⟨hlt₀, ht₀r⟩
    (fun u hu => ⟨(hγ u (hsub (Ioo_subset_Icc_self hu))).2,
      Or.inl ⟨u, Ioo_subset_Icc_self hu, rfl⟩⟩)
    (fun u hu => ⟨(hη u (hsub (Ioo_subset_Icc_self hu))).2,
      Or.inr ⟨u, Ioo_subset_Icc_self hu, rfl⟩⟩) heq ⟨hlt, htr⟩

/-- Uniqueness with initial data at the left end of a closed time interval.-/
theorem laurent_driven_unique_on_closed_interval {d : ℕ} (f : MultiLaurent d)
    (v : ℝ → ℂ) (hv : Continuous v)
    {γ η : ℝ → Fin d → ℂ} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hη : ContinuousOn η (Icc a b))
    (hdγ : ∀ t ∈ Ico a b, HasDerivAt γ (laurentVectorField f (v t) (γ t)) t)
    (hdη : ∀ t ∈ Ico a b, HasDerivAt η (laurentVectorField f (v t) (η t)) t)
    (hmemγ : MapsTo γ (Icc a b) (laurentRegularDomain f))
    (hmemη : MapsTo η (Icc a b) (laurentRegularDomain f))
    (heq : γ a = η a) : EqOn γ η (Icc a b) := by
  let K := γ '' Icc a b ∪ η '' Icc a b
  have hK : IsCompact K := (isCompact_Icc.image_of_continuousOn hγ).union (isCompact_Icc.image_of_continuousOn hη)
  have hKU : K ⊆ laurentRegularDomain f := union_subset (image_subset_iff.mpr hmemγ) (image_subset_iff.mpr hmemη)
  obtain ⟨L, hL⟩ := laurent_driven_lipschitz_on_compact f v hv isCompact_Icc hK hKU
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => K) (fun t ht => hL t (Ico_subset_Icc_self ht))
    hγ (fun t ht => (hdγ t ht).hasDerivWithinAt)
    (fun t ht => Or.inl ⟨t, Ico_subset_Icc_self ht, rfl⟩)
    hη (fun t ht => (hdη t ht).hasDerivWithinAt)
    (fun t ht => Or.inr ⟨t, Ico_subset_Icc_self ht, rfl⟩) heq

end
end DuistermaatVanDerKallen

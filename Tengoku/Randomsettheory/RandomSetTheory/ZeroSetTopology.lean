/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.ZeroSetStability

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Topology of zero sets of correspondences

For a closed nonempty-valued correspondence `G`, membership of zero in
`G θ` is equivalent to the vanishing of the scalar criterion
`infDist 0 (G θ)`.  Consequently, continuity of this criterion makes exact
zero sets and all closed enlarged zero sets closed, and compact whenever the
parameter domain (or a parameter restriction) is compact.

The last part derives criterion continuity from continuity of `G` in
Hausdorff distance.  Compact nonempty fibres automatically discharge the
finiteness condition needed for real-valued Hausdorff distance.
-/

open Set Metric Filter Topology

noncomputable section

namespace RandomSetTheory

/-! ## Level-set descriptions and threshold calculus -/

/-- For closed nonempty fibres, the exact zero set is precisely the zero
level set of the minimum-distance criterion.-/
theorem setValuedZeroSet_eq_zeroLevel
    {Θ E : Type*} [PseudoMetricSpace E] [Zero E]
    (G : Θ → Set E) (hclosed : ∀ θ, IsClosed (G θ))
    (hne : ∀ θ, (G θ).Nonempty) :
    setValuedZeroSet G = {θ | infDist 0 (G θ) = 0} := by
  ext θ
  change 0 ∈ G θ ↔ infDist 0 (G θ) = 0
  exact (hclosed θ).mem_iff_infDist_zero (hne θ)

/-- The zero-threshold enlargement agrees with the exact zero set for
closed nonempty fibres.-/
theorem enlargedSetValuedZeroSet_zero
    {Θ E : Type*} [PseudoMetricSpace E] [Zero E]
    (G : Θ → Set E) (hclosed : ∀ θ, IsClosed (G θ))
    (hne : ∀ θ, (G θ).Nonempty) :
    enlargedSetValuedZeroSet G 0 = setValuedZeroSet G := by
  ext θ
  change infDist 0 (G θ) ≤ 0 ↔ 0 ∈ G θ
  rw [(hclosed θ).mem_iff_infDist_zero (hne θ)]
  constructor
  · intro h
    exact le_antisymm h infDist_nonneg
  · intro h
    exact h.le

/-- Enlarged zero sets are monotone in their threshold.-/
theorem enlargedSetValuedZeroSet_mono
    {Θ E : Type*} [PseudoMetricSpace E] [Zero E]
    (G : Θ → Set E) {δ τ : ℝ} (hδτ : δ ≤ τ) :
    enlargedSetValuedZeroSet G δ ⊆ enlargedSetValuedZeroSet G τ := by
  intro θ hθ
  exact hθ.trans hδτ

/-- Every exact zero is retained by every nonnegative enlargement.  This
direction does not require closedness of the fibres.-/
theorem setValuedZeroSet_subset_enlarged_of_nonneg
    {Θ E : Type*} [PseudoMetricSpace E] [Zero E]
    (G : Θ → Set E) {τ : ℝ} (hτ : 0 ≤ τ) :
    setValuedZeroSet G ⊆ enlargedSetValuedZeroSet G τ := by
  intro θ hθ
  change 0 ∈ G θ at hθ
  change infDist 0 (G θ) ≤ τ
  rw [infDist_zero_of_mem hθ]
  exact hτ

/-! ## Closedness and compactness from criterion continuity -/

/-- A closed enlargement is a closed sublevel set of the continuous
minimum-distance criterion.-/
theorem isClosed_enlargedSetValuedZeroSet
    {Θ E : Type*} [TopologicalSpace Θ] [PseudoMetricSpace E] [Zero E]
    (G : Θ → Set E) {τ : ℝ}
    (hcont : Continuous (fun θ => infDist 0 (G θ))) :
    IsClosed (enlargedSetValuedZeroSet G τ) := by
  simpa [enlargedSetValuedZeroSet] using
    (isClosed_le hcont (continuous_const : Continuous (fun _ : Θ => τ)))

/-- Strict sublevel sets of the minimum-distance criterion are open.-/
theorem isOpen_infDist_zero_lt
    {Θ E : Type*} [TopologicalSpace Θ] [PseudoMetricSpace E] [Zero E]
    (G : Θ → Set E) {τ : ℝ}
    (hcont : Continuous (fun θ => infDist 0 (G θ))) :
    IsOpen {θ | infDist 0 (G θ) < τ} := by
  exact isOpen_lt hcont continuous_const

/-- Under closed nonempty fibres, continuity of the minimum-distance
criterion makes the exact zero set closed.-/
theorem isClosed_setValuedZeroSet
    {Θ E : Type*} [TopologicalSpace Θ] [PseudoMetricSpace E] [Zero E]
    (G : Θ → Set E) (hclosed : ∀ θ, IsClosed (G θ))
    (hne : ∀ θ, (G θ).Nonempty)
    (hcont : Continuous (fun θ => infDist 0 (G θ))) :
    IsClosed (setValuedZeroSet G) := by
  rw [setValuedZeroSet_eq_zeroLevel G hclosed hne]
  exact isClosed_eq hcont continuous_const

/-- Intersecting an enlarged zero set with a compact parameter restriction
gives a compact set.-/
theorem isCompact_inter_enlargedSetValuedZeroSet
    {Θ E : Type*} [TopologicalSpace Θ] [PseudoMetricSpace E] [Zero E]
    {K : Set Θ} (hK : IsCompact K) (G : Θ → Set E) {τ : ℝ}
    (hcont : Continuous (fun θ => infDist 0 (G θ))) :
    IsCompact (K ∩ enlargedSetValuedZeroSet G τ) :=
  hK.inter_right (isClosed_enlargedSetValuedZeroSet G hcont)

/-- Intersecting the exact zero set with a compact parameter restriction
gives a compact set.-/
theorem isCompact_inter_setValuedZeroSet
    {Θ E : Type*} [TopologicalSpace Θ] [PseudoMetricSpace E] [Zero E]
    {K : Set Θ} (hK : IsCompact K) (G : Θ → Set E)
    (hclosed : ∀ θ, IsClosed (G θ)) (hne : ∀ θ, (G θ).Nonempty)
    (hcont : Continuous (fun θ => infDist 0 (G θ))) :
    IsCompact (K ∩ setValuedZeroSet G) :=
  hK.inter_right (isClosed_setValuedZeroSet G hclosed hne hcont)

/-- On a compact parameter space, every closed enlarged zero set is
compact.-/
theorem isCompact_enlargedSetValuedZeroSet
    {Θ E : Type*} [TopologicalSpace Θ] [CompactSpace Θ]
    [PseudoMetricSpace E] [Zero E]
    (G : Θ → Set E) {τ : ℝ}
    (hcont : Continuous (fun θ => infDist 0 (G θ))) :
    IsCompact (enlargedSetValuedZeroSet G τ) :=
  (isClosed_enlargedSetValuedZeroSet G hcont).isCompact

/-- On a compact parameter space, the exact zero set is compact.-/
theorem isCompact_setValuedZeroSet
    {Θ E : Type*} [TopologicalSpace Θ] [CompactSpace Θ]
    [PseudoMetricSpace E] [Zero E]
    (G : Θ → Set E) (hclosed : ∀ θ, IsClosed (G θ))
    (hne : ∀ θ, (G θ).Nonempty)
    (hcont : Continuous (fun θ => infDist 0 (G θ))) :
    IsCompact (setValuedZeroSet G) :=
  (isClosed_setValuedZeroSet G hclosed hne hcont).isCompact

/-! ## Continuity inherited from Hausdorff continuity -/

/-- Hausdorff continuity of a correspondence at a parameter: its fibres
converge to the fibre at that parameter in real-valued Hausdorff distance.-/
def HausdorffContinuousAt
    {Θ E : Type*} [TopologicalSpace Θ] [PseudoMetricSpace E]
    (G : Θ → Set E) (θ : Θ) : Prop :=
  Tendsto (fun η => hausdorffDist (G η) (G θ)) (𝓝 θ) (𝓝 0)

/-- Pointwise Hausdorff continuity on the whole parameter space.-/
def HausdorffContinuous
    {Θ E : Type*} [TopologicalSpace Θ] [PseudoMetricSpace E]
    (G : Θ → Set E) : Prop :=
  ∀ θ, HausdorffContinuousAt G θ

/-- Hausdorff continuity at `θ` implies continuity there of distance from a
fixed point, provided the relevant Hausdorff distances are eventually
finite.-/
theorem HausdorffContinuousAt.continuousAt_infDist
    {Θ E : Type*} [TopologicalSpace Θ] [PseudoMetricSpace E]
    {G : Θ → Set E} {θ : Θ} (hG : HausdorffContinuousAt G θ)
    (x : E)
    (hfin : ∀ᶠ η in 𝓝 θ, hausdorffEDist (G η) (G θ) ≠ ⊤) :
    ContinuousAt (fun η => infDist x (G η)) θ := by
  change Tendsto (fun η => infDist x (G η)) (𝓝 θ)
    (𝓝 (infDist x (G θ)))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hhaus := (Metric.tendsto_nhds.1 hG) ε hε
  filter_upwards [hhaus, hfin] with η hη hηfin
  have hη' : hausdorffDist (G η) (G θ) < ε := by
    simpa [Real.dist_eq, abs_of_nonneg hausdorffDist_nonneg] using hη
  have hstab := abs_infDist_sub_infDist_le_hausdorffDist
    x (G η) (G θ) hηfin
  simpa [Real.dist_eq] using hstab.trans_lt hη'

/-- A Hausdorff-continuous correspondence with finite pairwise Hausdorff
distances has a continuous distance-from-a-fixed-point criterion.-/
theorem HausdorffContinuous.continuous_infDist
    {Θ E : Type*} [TopologicalSpace Θ] [PseudoMetricSpace E]
    {G : Θ → Set E} (hG : HausdorffContinuous G) (x : E)
    (hfin : ∀ η θ, hausdorffEDist (G η) (G θ) ≠ ⊤) :
    Continuous (fun θ => infDist x (G θ)) := by
  rw [continuous_iff_continuousAt]
  intro θ
  exact (hG θ).continuousAt_infDist x (Filter.Eventually.of_forall (fun η => hfin η θ))

/-- Compact nonempty fibres automatically make all pairwise Hausdorff
distances finite, so Hausdorff continuity directly yields criterion
continuity.-/
theorem HausdorffContinuous.continuous_infDist_of_compact
    {Θ E : Type*} [TopologicalSpace Θ] [PseudoMetricSpace E]
    {G : Θ → Set E} (hG : HausdorffContinuous G) (x : E)
    (hcompact : ∀ θ, IsCompact (G θ)) (hne : ∀ θ, (G θ).Nonempty) :
    Continuous (fun θ => infDist x (G θ)) := by
  apply hG.continuous_infDist x
  intro η θ
  exact hausdorffEDist_ne_top_of_nonempty_of_bounded
    (hne η) (hne θ) (hcompact η).isBounded (hcompact θ).isBounded

/-- Direct closedness of every enlarged zero set under Hausdorff continuity
and compact nonempty fibres.-/
theorem HausdorffContinuous.isClosed_enlargedSetValuedZeroSet_of_compact
    {Θ E : Type*} [TopologicalSpace Θ] [PseudoMetricSpace E] [Zero E]
    {G : Θ → Set E} (hG : HausdorffContinuous G)
    (hcompact : ∀ θ, IsCompact (G θ)) (hne : ∀ θ, (G θ).Nonempty)
    {τ : ℝ} : IsClosed (enlargedSetValuedZeroSet G τ) :=
  isClosed_enlargedSetValuedZeroSet G
    (hG.continuous_infDist_of_compact 0 hcompact hne)

/-- Direct closedness of the exact zero set under Hausdorff continuity and
compact nonempty fibres.-/
theorem HausdorffContinuous.isClosed_setValuedZeroSet_of_compact
    {Θ E : Type*} [TopologicalSpace Θ] [MetricSpace E] [Zero E]
    {G : Θ → Set E} (hG : HausdorffContinuous G)
    (hcompact : ∀ θ, IsCompact (G θ)) (hne : ∀ θ, (G θ).Nonempty) :
    IsClosed (setValuedZeroSet G) :=
  isClosed_setValuedZeroSet G (fun θ => (hcompact θ).isClosed) hne
    (hG.continuous_infDist_of_compact 0 hcompact hne)

/-- On a compact parameter space, Hausdorff continuity and compact nonempty
fibres make every enlarged zero set compact.-/
theorem HausdorffContinuous.isCompact_enlargedSetValuedZeroSet_of_compact
    {Θ E : Type*} [TopologicalSpace Θ] [CompactSpace Θ]
    [PseudoMetricSpace E] [Zero E]
    {G : Θ → Set E} (hG : HausdorffContinuous G)
    (hcompact : ∀ θ, IsCompact (G θ)) (hne : ∀ θ, (G θ).Nonempty)
    {τ : ℝ} : IsCompact (enlargedSetValuedZeroSet G τ) :=
  (hG.isClosed_enlargedSetValuedZeroSet_of_compact hcompact hne).isCompact

/-- On a compact parameter space, Hausdorff continuity and compact nonempty
fibres make the exact zero set compact.-/
theorem HausdorffContinuous.isCompact_setValuedZeroSet_of_compact
    {Θ E : Type*} [TopologicalSpace Θ] [CompactSpace Θ]
    [MetricSpace E] [Zero E]
    {G : Θ → Set E} (hG : HausdorffContinuous G)
    (hcompact : ∀ θ, IsCompact (G θ)) (hne : ∀ θ, (G θ).Nonempty) :
    IsCompact (setValuedZeroSet G) :=
  (hG.isClosed_setValuedZeroSet_of_compact hcompact hne).isCompact

end RandomSetTheory

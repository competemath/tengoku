/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.Geometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hausdorff transport under locally Lipschitz maps

The Lipschitz assumption needed to transport two compact sets only concerns
their union.  This module records that precise form, its compatibility with
closed convexification of the images, and the resulting convergence
principles.
-/

open Set Metric Filter Topology

noncomputable section

namespace RandomSetTheory

/-- A map which is `c`-Lipschitz on `K ∪ L` transports the Hausdorff
distance between the two compact nonempty sets with factor `c`.
@isnad1 id=le.5h6v.s6.9fab2aec8a2f from=translated src=- shape=b29d0fbf vocab=61c917d1
-/
theorem hausdorffDist_image_le_of_lipschitzOnWith
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {K L : Set X} {c : NNReal}
    (hf : LipschitzOnWith c f (K ∪ L))
    (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) :
    hausdorffDist (f '' K) (f '' L) ≤
      (c : ℝ) * hausdorffDist K L := by
  have hfin : hausdorffEDist K L ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded
      hKne hLne hK.isBounded hL.isBounded
  apply hausdorffDist_le_of_mem_dist
    (mul_nonneg c.coe_nonneg hausdorffDist_nonneg)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hL.exists_infDist_eq_dist hLne x
    refine ⟨f y, ⟨y, hy, rfl⟩, ?_⟩
    calc
      dist (f x) (f y) ≤ (c : ℝ) * dist x y :=
        hf.dist_le_mul x (subset_union_left hx) y (subset_union_right hy)
      _ = (c : ℝ) * infDist x L := by rw [hxy]
      _ ≤ (c : ℝ) * hausdorffDist K L := by
        gcongr
        exact infDist_le_hausdorffDist_of_mem hx hfin
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hyx⟩ := hK.exists_infDist_eq_dist hKne y
    refine ⟨f x, ⟨x, hx, rfl⟩, ?_⟩
    calc
      dist (f y) (f x) ≤ (c : ℝ) * dist y x :=
        hf.dist_le_mul y (subset_union_right hy) x (subset_union_left hx)
      _ = (c : ℝ) * infDist y K := by rw [hyx]
      _ ≤ (c : ℝ) * hausdorffDist K L := by
        gcongr
        rw [hausdorffDist_comm]
        apply infDist_le_hausdorffDist_of_mem hy
        simpa [hausdorffEDist_comm] using hfin

/-- A Lipschitz bound on a larger domain transports Hausdorff distance
between any two compact nonempty subsets of that domain.
@isnad1 id=le.7h7v.s6.8f7f2851a67f from=translated src=- shape=e1c9e8de vocab=9b527a36
-/
theorem hausdorffDist_image_le_of_lipschitzOnWith_of_subset
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {D K L : Set X} {c : NNReal}
    (hf : LipschitzOnWith c f D)
    (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKD : K ⊆ D) (hLD : L ⊆ D) :
    hausdorffDist (f '' K) (f '' L) ≤
      (c : ℝ) * hausdorffDist K L :=
  hausdorffDist_image_le_of_lipschitzOnWith
    (hf.mono (union_subset hKD hLD)) hK hL hKne hLne

/-- The same transport bound holds after taking the closed convex hull of
both images.
@isnad1 id=le.5h6v.s8.9aaac92f9bee from=translated src=- shape=6a87ef2c vocab=fde5ab95
-/
theorem hausdorffDist_closedConvexHull_image_le_of_lipschitzOnWith
    {X Y : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {K L : Set X} {c : NNReal}
    (hf : LipschitzOnWith c f (K ∪ L))
    (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) :
    hausdorffDist (closedConvexHull ℝ (f '' K))
        (closedConvexHull ℝ (f '' L)) ≤
      (c : ℝ) * hausdorffDist K L := by
  have hKimage : IsCompact (f '' K) :=
    hK.image_of_continuousOn
      (hf.continuousOn.mono subset_union_left)
  have hLimage : IsCompact (f '' L) :=
    hL.image_of_continuousOn
      (hf.continuousOn.mono subset_union_right)
  calc
    hausdorffDist (closedConvexHull ℝ (f '' K))
        (closedConvexHull ℝ (f '' L)) ≤
        hausdorffDist (f '' K) (f '' L) :=
      hausdorffDist_closedConvexHull_le hKimage hLimage
        (hKne.image f) (hLne.image f)
    _ ≤ (c : ℝ) * hausdorffDist K L :=
      hausdorffDist_image_le_of_lipschitzOnWith hf hK hL hKne hLne

/-- Hausdorff convergence is preserved by a fixed map which is uniformly
`c`-Lipschitz on each `K i ∪ L`.  The index filter is arbitrary.
@isnad1 id=tendsto.6h8v.s7.96ad2c449ce3 from=translated src=- shape=2fa18cc9 vocab=979bbc32
-/
theorem tendsto_hausdorffDist_image_of_lipschitzOnWith
    {X Y ι : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {l : Filter ι} {f : X → Y} {K : ι → Set X} {L : Set X} {c : NNReal}
    (hf : ∀ i, LipschitzOnWith c f (K i ∪ L))
    (hK : ∀ i, IsCompact (K i)) (hL : IsCompact L)
    (hKne : ∀ i, (K i).Nonempty) (hLne : L.Nonempty)
    (hKL : Tendsto (fun i => hausdorffDist (K i) L) l (nhds 0)) :
    Tendsto (fun i => hausdorffDist (f '' K i) (f '' L)) l (nhds 0) := by
  apply squeeze_zero
    (fun _ => hausdorffDist_nonneg)
    (fun i => hausdorffDist_image_le_of_lipschitzOnWith
      (hf i) (hK i) hL (hKne i) hLne)
  simpa using hKL.const_mul (c : ℝ)

/-- Hausdorff convergence remains true after mapping and closed
convexification, under the same uniform local Lipschitz bound.
@isnad1 id=tendsto.6h8v.s8.39b1282be975 from=translated src=- shape=f9489fdd vocab=c636dc9d
-/
theorem tendsto_hausdorffDist_closedConvexHull_image_of_lipschitzOnWith
    {X Y ι : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {l : Filter ι} {f : X → Y} {K : ι → Set X} {L : Set X} {c : NNReal}
    (hf : ∀ i, LipschitzOnWith c f (K i ∪ L))
    (hK : ∀ i, IsCompact (K i)) (hL : IsCompact L)
    (hKne : ∀ i, (K i).Nonempty) (hLne : L.Nonempty)
    (hKL : Tendsto (fun i => hausdorffDist (K i) L) l (nhds 0)) :
    Tendsto
      (fun i => hausdorffDist (closedConvexHull ℝ (f '' K i))
        (closedConvexHull ℝ (f '' L))) l (nhds 0) := by
  apply squeeze_zero
    (fun _ => hausdorffDist_nonneg)
    (fun i => hausdorffDist_closedConvexHull_image_le_of_lipschitzOnWith
      (hf i) (hK i) hL (hKne i) hLne)
  simpa using hKL.const_mul (c : ℝ)

end RandomSetTheory

/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Convex.Hull

/-!
# Convex join

This file defines the convex join of two sets. The convex join of `s` and `t` is the union of the
segments with one end in `s` and the other in `t`. This is notably a useful gadget to deal with
convex hulls of finite sets.
-/

@[expose] public section


open Set

variable {ι : Sort*} {𝕜 E : Type*}

section OrderedSemiring

variable (𝕜) [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [Module 𝕜 E]
  {s t s₁ s₂ t₁ t₂ u : Set E}
  {x y : E}

/-- The join of two sets is the union of the segments joining them. This can be interpreted as the
topological join, but within the original space. -/
def convexJoin (s t : Set E) : Set E :=
  ⋃ (x ∈ s) (y ∈ t), segment 𝕜 x y

variable {𝕜}

/--
@isnad1 id=iff.0h5v.s6.39eb92f3d5a5 from=seed src=0 shape=c6154cd0 vocab=5ea889b5
-/
theorem mem_convexJoin : x ∈ convexJoin 𝕜 s t ↔ ∃ a ∈ s, ∃ b ∈ t, x ∈ segment 𝕜 a b := by
  simp [convexJoin]

/--
@isnad1 id=eq.0h4v.s5.db697c349191 from=seed src=0 shape=004f83cf vocab=88560d8e
-/
theorem convexJoin_comm (s t : Set E) : convexJoin 𝕜 s t = convexJoin 𝕜 t s :=
  (iUnion₂_comm _).trans <| by simp_rw [convexJoin, segment_symm]

/--
@isnad1 id=le.2h6v.s6.2f0ae3314879 from=seed src=0 shape=487ebd28 vocab=f6dc848a
-/
theorem convexJoin_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : convexJoin 𝕜 s₁ t₁ ⊆ convexJoin 𝕜 s₂ t₂ :=
  biUnion_mono hs fun _ _ => biUnion_subset_biUnion_left ht

/--
@isnad1 id=le.1h5v.s5.0814455a62d3 from=seed src=0 shape=b3c9f323 vocab=f6dc848a
-/
theorem convexJoin_mono_left (hs : s₁ ⊆ s₂) : convexJoin 𝕜 s₁ t ⊆ convexJoin 𝕜 s₂ t :=
  convexJoin_mono hs Subset.rfl

/--
@isnad1 id=le.1h5v.s5.06a265125cf1 from=seed src=0 shape=5b2fcd0c vocab=f6dc848a
-/
theorem convexJoin_mono_right (ht : t₁ ⊆ t₂) : convexJoin 𝕜 s t₁ ⊆ convexJoin 𝕜 s t₂ :=
  convexJoin_mono Subset.rfl ht

/--
@isnad1 id=eq.0h3v.s5.0a2dc0691f68 from=seed src=0 shape=9da46086 vocab=79f5ce95
-/
@[simp]
theorem convexJoin_empty_left (t : Set E) : convexJoin 𝕜 ∅ t = ∅ := by simp [convexJoin]

/--
@isnad1 id=eq.0h3v.s5.e565aae07691 from=seed src=0 shape=4e463802 vocab=79f5ce95
-/
@[simp]
theorem convexJoin_empty_right (s : Set E) : convexJoin 𝕜 s ∅ = ∅ := by simp [convexJoin]

/--
@isnad1 id=eq.0h4v.s6.04985b062265 from=seed src=0 shape=5aa8f829 vocab=2b88f29e
-/
@[simp]
theorem convexJoin_singleton_left (t : Set E) (x : E) :
    convexJoin 𝕜 {x} t = ⋃ y ∈ t, segment 𝕜 x y := by simp [convexJoin]

/--
@isnad1 id=eq.0h4v.s6.229ca7a6e36e from=seed src=0 shape=be637375 vocab=2b88f29e
-/
@[simp]
theorem convexJoin_singleton_right (s : Set E) (y : E) :
    convexJoin 𝕜 s {y} = ⋃ x ∈ s, segment 𝕜 x y := by simp [convexJoin]

/--
@isnad1 id=eq.0h4v.s6.4561fd6ec9bf from=seed src=0 shape=3b5f348c vocab=983713df
-/
theorem convexJoin_singletons (x : E) : convexJoin 𝕜 {x} {y} = segment 𝕜 x y := by simp

/--
@isnad1 id=eq.0h5v.s6.f3bab2df1feb from=seed src=0 shape=7dfcf861 vocab=24138df0
-/
@[simp]
theorem convexJoin_union_left (s₁ s₂ t : Set E) :
    convexJoin 𝕜 (s₁ ∪ s₂) t = convexJoin 𝕜 s₁ t ∪ convexJoin 𝕜 s₂ t := by
  simp_rw [convexJoin, mem_union, iUnion_or, iUnion_union_distrib]

/--
@isnad1 id=eq.0h5v.s6.ebbabdd374c5 from=seed src=0 shape=52fd6491 vocab=24138df0
-/
@[simp]
theorem convexJoin_union_right (s t₁ t₂ : Set E) :
    convexJoin 𝕜 s (t₁ ∪ t₂) = convexJoin 𝕜 s t₁ ∪ convexJoin 𝕜 s t₂ := by
  simp_rw [convexJoin_comm s, convexJoin_union_left]

/--
@isnad1 id=eq.0h5v.s6.8bb18de97c40 from=seed src=0 shape=0cbbcd26 vocab=576d953e
-/
@[simp]
theorem convexJoin_iUnion_left (s : ι → Set E) (t : Set E) :
    convexJoin 𝕜 (⋃ i, s i) t = ⋃ i, convexJoin 𝕜 (s i) t := by
  simp_rw [convexJoin, mem_iUnion, iUnion_exists]
  exact iUnion_comm _

/--
@isnad1 id=eq.0h5v.s6.088f557de25f from=seed src=0 shape=36c96a5d vocab=576d953e
-/
@[simp]
theorem convexJoin_iUnion_right (s : Set E) (t : ι → Set E) :
    convexJoin 𝕜 s (⋃ i, t i) = ⋃ i, convexJoin 𝕜 s (t i) := by
  simp_rw [convexJoin_comm s, convexJoin_iUnion_left]

/--
@isnad1 id=le.2h6v.s6.83840066e289 from=seed src=0 shape=a0641840 vocab=2cc9ebbd
-/
theorem segment_subset_convexJoin (hx : x ∈ s) (hy : y ∈ t) : segment 𝕜 x y ⊆ convexJoin 𝕜 s t :=
  subset_iUnion₂_of_subset x hx <| subset_iUnion₂ (s := fun y _ ↦ segment 𝕜 x y) y hy

section
variable [IsOrderedRing 𝕜]

/--
@isnad1 id=le.1h4v.s5.f29f8f5f378c from=seed src=0 shape=1a439c08 vocab=f1b45746
-/
theorem subset_convexJoin_left (h : t.Nonempty) : s ⊆ convexJoin 𝕜 s t := fun _x hx =>
  let ⟨_y, hy⟩ := h
  segment_subset_convexJoin hx hy <| left_mem_segment _ _ _

/--
@isnad1 id=le.1h4v.s5.a53f63b6d7ac from=seed src=0 shape=219d65b0 vocab=f1b45746
-/
theorem subset_convexJoin_right (h : s.Nonempty) : t ⊆ convexJoin 𝕜 s t :=
  convexJoin_comm (𝕜 := 𝕜) t s ▸ subset_convexJoin_left h

end

/--
@isnad1 id=le.3h5v.s6.fd19f08f4b78 from=seed src=0 shape=e9c00014 vocab=6428ad61
-/
theorem convexJoin_subset (hs : s ⊆ u) (ht : t ⊆ u) (hu : Convex 𝕜 u) : convexJoin 𝕜 s t ⊆ u :=
  iUnion₂_subset fun _x hx => iUnion₂_subset fun _y hy => hu.segment_subset (hs hx) (ht hy)

/--
@isnad1 id=le.0h4v.s6.27bcd7faa233 from=seed src=0 shape=27408bdc vocab=31bbe5e8
-/
theorem convexJoin_subset_convexHull (s t : Set E) : convexJoin 𝕜 s t ⊆ convexHull 𝕜 (s ∪ t) :=
  convexJoin_subset (subset_union_left.trans <| subset_convexHull _ _)
      (subset_union_right.trans <| subset_convexHull _ _) <|
    convex_convexHull _ _

end OrderedSemiring

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] {s t : Set E} {x : E}

/--
@isnad1 id=le.0h5v.s7.beb0704c9448 from=seed src=0 shape=d8441fb8 vocab=cc48b782
-/
theorem convexJoin_assoc_aux (s t u : Set E) :
    convexJoin 𝕜 (convexJoin 𝕜 s t) u ⊆ convexJoin 𝕜 s (convexJoin 𝕜 t u) := by
  simp_rw [subset_def, mem_convexJoin]
  rintro _ ⟨z, ⟨x, hx, y, hy, a₁, b₁, ha₁, hb₁, hab₁, rfl⟩, z, hz, a₂, b₂, ha₂, hb₂, hab₂, rfl⟩
  obtain rfl | hb₂ := hb₂.eq_or_lt
  · refine ⟨x, hx, y, ⟨y, hy, z, hz, left_mem_segment 𝕜 _ _⟩, a₁, b₁, ha₁, hb₁, hab₁, ?_⟩
    linear_combination (norm := module) -hab₂ • (a₁ • x + b₁ • y)
  refine
    ⟨x, hx, (a₂ * b₁ / (a₂ * b₁ + b₂)) • y + (b₂ / (a₂ * b₁ + b₂)) • z,
      ⟨y, hy, z, hz, _, _, by positivity, by positivity, by field, rfl⟩,
      a₂ * a₁, a₂ * b₁ + b₂, by positivity, by positivity, ?_, ?_⟩
  · linear_combination a₂ * hab₁ + hab₂
  · match_scalars <;> field

/--
@isnad1 id=eq.0h5v.s7.b7be7737a550 from=seed src=0 shape=d8441fb8 vocab=08c8d3ed
-/
theorem convexJoin_assoc (s t u : Set E) :
    convexJoin 𝕜 (convexJoin 𝕜 s t) u = convexJoin 𝕜 s (convexJoin 𝕜 t u) := by
  refine (convexJoin_assoc_aux _ _ _).antisymm ?_
  simp_rw [convexJoin_comm s, convexJoin_comm _ u]
  exact convexJoin_assoc_aux _ _ _

/--
@isnad1 id=eq.0h5v.s7.4d4045509061 from=seed src=0 shape=b9d0db16 vocab=08c8d3ed
-/
theorem convexJoin_left_comm (s t u : Set E) :
    convexJoin 𝕜 s (convexJoin 𝕜 t u) = convexJoin 𝕜 t (convexJoin 𝕜 s u) := by
  simp_rw [← convexJoin_assoc, convexJoin_comm]

/--
@isnad1 id=eq.0h5v.s7.0e8888d8f392 from=seed src=0 shape=10f2a4a4 vocab=08c8d3ed
-/
theorem convexJoin_right_comm (s t u : Set E) :
    convexJoin 𝕜 (convexJoin 𝕜 s t) u = convexJoin 𝕜 (convexJoin 𝕜 s u) t := by
  simp_rw [convexJoin_assoc, convexJoin_comm]

/--
@isnad1 id=eq.0h6v.s7.3d86d5a5a1ff from=seed src=0 shape=912c74ec vocab=08c8d3ed
-/
theorem convexJoin_convexJoin_convexJoin_comm (s t u v : Set E) :
    convexJoin 𝕜 (convexJoin 𝕜 s t) (convexJoin 𝕜 u v) =
      convexJoin 𝕜 (convexJoin 𝕜 s u) (convexJoin 𝕜 t v) := by
  simp_rw [← convexJoin_assoc, convexJoin_right_comm]

/--
@isnad1 id=convex.2h4v.s8.04c9fa5ed5bf from=seed src=0 shape=faa43274 vocab=a2cd3ca6
-/
protected theorem Convex.convexJoin (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) :
    Convex 𝕜 (convexJoin 𝕜 s t) := by
  simp only [Convex, StarConvex, convexJoin, mem_iUnion]
  rintro _ ⟨x₁, hx₁, y₁, hy₁, a₁, b₁, ha₁, hb₁, hab₁, rfl⟩
    _ ⟨x₂, hx₂, y₂, hy₂, a₂, b₂, ha₂, hb₂, hab₂, rfl⟩ p q hp hq hpq
  rcases hs.exists_mem_add_smul_eq hx₁ hx₂ (mul_nonneg hp ha₁) (mul_nonneg hq ha₂) with ⟨x, hxs, hx⟩
  rcases ht.exists_mem_add_smul_eq hy₁ hy₂ (mul_nonneg hp hb₁) (mul_nonneg hq hb₂) with ⟨y, hyt, hy⟩
  refine ⟨_, hxs, _, hyt, p * a₁ + q * a₂, p * b₁ + q * b₂, ?_, ?_, ?_, ?_⟩ <;> try positivity
  · linear_combination p * hab₁ + q * hab₂ + hpq
  · rw [hx, hy]
    module

/--
@isnad1 id=eq.4h4v.s8.8cd496735e2d from=seed src=0 shape=ee244071 vocab=71da644f
-/
protected theorem Convex.convexHull_union (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) (hs₀ : s.Nonempty)
    (ht₀ : t.Nonempty) : convexHull 𝕜 (s ∪ t) = convexJoin 𝕜 s t :=
  (convexHull_min (union_subset (subset_convexJoin_left ht₀) <| subset_convexJoin_right hs₀) <|
        hs.convexJoin ht).antisymm <|
    convexJoin_subset_convexHull _ _

/--
@isnad1 id=eq.2h4v.s8.4968dc3b70ab from=seed src=0 shape=929d9bb5 vocab=e38df72d
-/
theorem convexHull_union (hs : s.Nonempty) (ht : t.Nonempty) :
    convexHull 𝕜 (s ∪ t) = convexJoin 𝕜 (convexHull 𝕜 s) (convexHull 𝕜 t) := by
  rw [← convexHull_convexHull_union_left, ← convexHull_convexHull_union_right]
  exact (convex_convexHull 𝕜 s).convexHull_union (convex_convexHull 𝕜 t) hs.convexHull ht.convexHull

/--
@isnad1 id=eq.1h4v.s7.81a2a6fe3844 from=seed src=0 shape=f94e201e vocab=991705e3
-/
theorem convexHull_insert (hs : s.Nonempty) :
    convexHull 𝕜 (insert x s) = convexJoin 𝕜 {x} (convexHull 𝕜 s) := by
  rw [insert_eq, convexHull_union (singleton_nonempty _) hs, convexHull_singleton]

/--
@isnad1 id=eq.0h6v.s8.19b95bc1e8b0 from=seed src=0 shape=bad2498a vocab=a8cfaf77
-/
theorem convexJoin_segments (a b c d : E) :
    convexJoin 𝕜 (segment 𝕜 a b) (segment 𝕜 c d) = convexHull 𝕜 {a, b, c, d} := by
  simp_rw [← convexHull_pair, convexHull_insert (insert_nonempty _ _),
    convexHull_insert (singleton_nonempty _), convexJoin_assoc,
    convexHull_singleton]

/--
@isnad1 id=eq.0h5v.s8.19b5774b05dc from=seed src=0 shape=6e8c4e79 vocab=a8cfaf77
-/
theorem convexJoin_segment_singleton (a b c : E) :
    convexJoin 𝕜 (segment 𝕜 a b) {c} = convexHull 𝕜 {a, b, c} := by
  rw [← pair_eq_singleton, ← convexJoin_segments, segment_same, pair_eq_singleton]

/--
@isnad1 id=eq.0h5v.s8.31b12f09081e from=seed src=0 shape=a1dcd2c7 vocab=a8cfaf77
-/
theorem convexJoin_singleton_segment (a b c : E) :
    convexJoin 𝕜 {a} (segment 𝕜 b c) = convexHull 𝕜 {a, b, c} := by
  rw [← segment_same 𝕜, convexJoin_segments, insert_idem]

end LinearOrderedField

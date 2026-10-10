/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Tengoku.Aperiodicmonotiles.AM.Mathlib.Combinatorics.Tiling.Function.Basic
import Tengoku

/-!
# Disjointness properties for tiles

This file defines disjointness properties for tiles in a discrete context.

## Main definitions

* `t.Disjoint`: A `TileSetFunction` for whether the tiles of `t` are disjoint.

* `t.DisjointOn s`: A `VarTileSetFunction` for whether the tiles of `t` are disjoint
within the set `s`.

* `t.FiniteIntersections`: A `TileSetFunction` for whether only finitely many of the
tiles of `t` contain any point.

* `t.FiniteIntersectionsOn s`: A `VarTileSetFunction` for whether only finitely many of
the tiles of `t` contain any point of `s`.

* `t.FiniteDistinctIntersections`: A `TileSetFunction` for whether only finitely many
distinct tiles of `t` contain any point.

* `t.FiniteDistinctIntersectionsOn s`: A `VarTileSetFunction` for whether only finitely
many distinct tiles of `t` contain any point of `s`.

## References

* [Branko Grünbaum and G. C. Shephard, *Tilings and Patterns*][GrunbaumShephard1987]
-/

noncomputable section

namespace DiscreteTiling

open Function
open scoped Pointwise

variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ ιₜ' F : Type*}
variable [FunLike F ιₜ' ιₜ] [EmbeddingLike F ιₜ' ιₜ]

namespace TileSet

/-- Whether the tiles of `t` are pairwise disjoint. -/
protected def Disjoint : TileSetFunction ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦ Pairwise fun i j ↦ Disjoint (t i : Set X) (t j),
   by
     intro ιₜ ιₜ' f t
     simp only [eq_iff_iff]
     convert EquivLike.pairwise_comp_iff f.symm _
     rfl,
   by simp [TileSet.smul_apply]⟩

/--
@isnad1 id=iff.0h6v.s7.770ce851f168 from=translated src=- shape=8c0d8c66 vocab=4b5cd1d1
-/
protected lemma disjoint_iff {t : TileSet ps ιₜ} :
    t.Disjoint ↔ Pairwise fun i j ↦ Disjoint (t i : Set X) (t j) :=
  Iff.rfl

/--
@isnad1 id=tofun.1h9v.s6.7d9fe013eb7b from=translated src=- shape=e6abd822 vocab=5bf374dd
-/
lemma Disjoint.reindex_of_injective {t : TileSet ps ιₜ} (hd : t.Disjoint) {e : ιₜ' → ιₜ}
    (h : Injective e) : (t.reindex e).Disjoint :=
  hd.comp_of_injective h

/--
@isnad1 id=tofun.0h10v.s6.3394df99f715 from=translated src=- shape=120f4f0e vocab=fb1550e9
-/
lemma Disjoint.reindex_of_embeddingLike {t : TileSet ps ιₜ} (hd : t.Disjoint) (e : F) :
    (t.reindex e).Disjoint :=
  EmbeddingLike.pairwise_comp e hd

/--
@isnad1 id=tofun.1h9v.s6.35000201de9a from=translated src=- shape=bf68470f vocab=447786d1
-/
lemma Disjoint.reindex_of_surjective {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (hd : (t.reindex e).Disjoint) (h : Surjective e) : t.Disjoint :=
  Pairwise.of_comp_of_surjective hd h

/--
@isnad1 id=tofun.0h6v.s5.13fc248f4d45 from=translated src=- shape=74ce4195 vocab=e2d424fa
-/
@[simp] lemma disjoint_of_subsingleton [Subsingleton ιₜ] (t : TileSet ps ιₜ) :
    t.Disjoint := by
  simp [TileSet.disjoint_iff, Subsingleton.pairwise]

/--
@isnad1 id=pairwise.0h7v.s7.1e98c5009c94 from=translated src=- shape=78a83bc4 vocab=1382b1cd
-/
lemma Disjoint.coeSet_disjoint {t : TileSet ps ιₜ} (hd : t.Disjoint) :
    (t : Set (PlacedTile ps)).Pairwise fun x y ↦ Disjoint (x : Set X) y :=
  hd.range_pairwise (r := fun (x y : PlacedTile ps) ↦ Disjoint (x : Set X) y)

/--
@isnad1 id=iff.1h6v.s7.99d6fcb30505 from=translated src=- shape=73819e28 vocab=51c80e2e
-/
lemma coeSet_disjoint_iff_disjoint_of_injective {t : TileSet ps ιₜ} (h : Injective t) :
    ((t : Set (PlacedTile ps)).Pairwise fun x y ↦ Disjoint (x : Set X) y) ↔ t.Disjoint :=
  ⟨fun hd ↦ hd.on_injective h Set.mem_range_self, Disjoint.coeSet_disjoint⟩

/-- Whether the tiles of `t` are pairwise disjoint within the set `s`. -/
protected def DisjointOn : VarTileSetFunction (Set X) ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (s : Set X) (t : TileSet ps ιₜ) ↦ Pairwise fun i j ↦
     Disjoint ((t i : Set X) ∩ s) ((t j : Set X) ∩ s),
   by
     intro ιₜ ιₜ' f s t
     simp only [eq_iff_iff]
     convert EquivLike.pairwise_comp_iff f.symm _
     rfl,
   by simp [TileSet.smul_apply, ← Set.smul_set_inter]⟩

/--
@isnad1 id=iff.0h7v.s7.5b4e2a3c96f9 from=translated src=- shape=46354b0e vocab=393798b4
-/
protected lemma disjointOn_iff {s : Set X} {t : TileSet ps ιₜ} :
    t.DisjointOn s ↔ Pairwise fun i j ↦ Disjoint ((t i : Set X) ∩ s) ((t j : Set X) ∩ s) :=
  Iff.rfl

/--
@isnad1 id=tofun.1h10v.s7.967dfe893890 from=translated src=- shape=eb3e1eb1 vocab=45207405
-/
lemma DisjointOn.reindex_of_injective {s : Set X} {t : TileSet ps ιₜ} (hd : t.DisjointOn s)
    {e : ιₜ' → ιₜ} (h : Injective e) : (t.reindex e).DisjointOn s :=
  hd.comp_of_injective h

/--
@isnad1 id=tofun.0h11v.s7.051d42d0a81b from=translated src=- shape=6afe415b vocab=68c10ad0
-/
lemma DisjointOn.reindex_of_embeddingLike {s : Set X} {t : TileSet ps ιₜ}
    (hd : t.DisjointOn s) (e : F) : (t.reindex e).DisjointOn s :=
  EmbeddingLike.pairwise_comp e hd

/--
@isnad1 id=tofun.1h10v.s7.75e7de727794 from=translated src=- shape=04631f47 vocab=ad8db46a
-/
lemma DisjointOn.reindex_of_surjective {s : Set X} {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (hd : (t.reindex e).DisjointOn s) (h : Surjective e) : t.DisjointOn s :=
  Pairwise.of_comp_of_surjective hd h

/--
@isnad1 id=tofun.0h7v.s6.09e656a52be3 from=translated src=- shape=8416b16d vocab=aa3601f7
-/
@[simp] lemma disjointOn_of_subsingleton [Subsingleton ιₜ] (s : Set X) (t : TileSet ps ιₜ) :
    t.DisjointOn s := by
  simp [TileSet.disjointOn_iff, Subsingleton.pairwise]

/--
@isnad1 id=tofun.1h9v.s6.9a9cb7bd5b21 from=translated src=- shape=f1970390 vocab=6c4960cf
-/
lemma DisjointOn.subset {s₁ s₂ : Set X} {t : TileSet ps ιₜ} (hd : t.DisjointOn s₂)
    (hs : s₁ ⊆ s₂) : t.DisjointOn s₁ :=
  fun _ _ h ↦ Set.disjoint_of_subset (Set.inter_subset_inter_right _ hs)
    (Set.inter_subset_inter_right _ hs) (hd h)

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=tofun.0h6v.s6.c8881f8e6fa7 from=translated src=- shape=4b62c92e vocab=d82f3e72
-/
@[simp] lemma disjointOn_empty (t : TileSet ps ιₜ) : t.DisjointOn ∅ := by
  simp [TileSet.DisjointOn, Pairwise]

/--
@isnad1 id=iff.0h6v.s6.25c6fc5d631e from=translated src=- shape=6398d2b8 vocab=9b4434ca
-/
@[simp] lemma disjointOn_univ_iff {t : TileSet ps ιₜ} :
    t.DisjointOn Set.univ ↔ t.Disjoint := by
  simp [TileSet.Disjoint, TileSet.DisjointOn]

/--
@isnad1 id=tofun.0h8v.s6.f8e8d27531b8 from=translated src=- shape=a52daa99 vocab=e61a2ef0
-/
lemma Disjoint.disjointOn (s : Set X) {t : TileSet ps ιₜ} (hd : t.Disjoint) :
    t.DisjointOn s :=
  fun _ _ h ↦ ((hd h).inter_left _).inter_right _

/-- Whether only finitely many tiles of `t` contain any point. -/
def FiniteIntersections : TileSetFunction ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦ ∀ x, {i | x ∈ t i}.Finite,
   by
     intro ιₜ ιₜ' f t
     refine forall_congr ?_
     simp only [eq_iff_iff]
     intro x
     convert Set.finite_image_iff (Set.injOn_of_injective (EquivLike.injective f))
     exact Equiv.setOfPred_apply_symm_eq_image_setOfPred f fun i ↦ x ∈ t i,
   by
     intro ιₜ g t _
     simp only [eq_iff_iff]
     refine ⟨fun h ↦ fun x ↦ by simpa using h (g • x), fun h ↦ fun x ↦ ?_⟩
     convert h (g⁻¹ • x) using 2
     ext i
     exact mem_smul_apply_iff_smul_inv_mem⟩

/--
@isnad1 id=iff.0h6v.s6.691ca5f91097 from=translated src=- shape=0dd70278 vocab=c8fe33a7
-/
lemma finiteIntersections_iff {t : TileSet ps ιₜ} :
    t.FiniteIntersections ↔ ∀ x, {i | x ∈ t i}.Finite :=
  Iff.rfl

/--
@isnad1 id=tofun.1h9v.s6.4ff71b4942b1 from=translated src=- shape=e6abd822 vocab=bd0fbbd8
-/
lemma FiniteIntersections.reindex_of_injective {t : TileSet ps ιₜ}
    (hfi : t.FiniteIntersections) {e : ιₜ' → ιₜ} (h : Injective e) :
    (t.reindex e).FiniteIntersections :=
  fun x ↦ Set.Finite.preimage (Set.injOn_of_injective h) (hfi x)

/--
@isnad1 id=tofun.0h10v.s6.eb7e30cf77b3 from=translated src=- shape=120f4f0e vocab=1a57e89b
-/
lemma FiniteIntersections.reindex_of_embeddingLike {t : TileSet ps ιₜ}
    (hfi : t.FiniteIntersections) (e : F) : (t.reindex e).FiniteIntersections :=
  FiniteIntersections.reindex_of_injective hfi (EmbeddingLike.injective _)

/--
@isnad1 id=tofun.1h9v.s6.16aac66901b3 from=translated src=- shape=bf68470f vocab=a67fb949
-/
lemma FiniteIntersections.reindex_of_surjective {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (hfi : (t.reindex e).FiniteIntersections) (h : Surjective e) :
    t.FiniteIntersections :=
  fun x ↦ Set.Finite.of_preimage (hfi x) h

/--
@isnad1 id=tofun.0h6v.s5.7c889c810d9c from=translated src=- shape=74ce4195 vocab=60da38f9
-/
@[simp] lemma finiteIntersections_of_subsingleton [Subsingleton ιₜ] (t : TileSet ps ιₜ) :
    t.FiniteIntersections :=
  fun _ ↦ Set.subsingleton_of_subsingleton.finite

/--
@isnad1 id=tofun.0h7v.s6.7ed5645cd791 from=translated src=- shape=5077c659 vocab=8ebd2b98
-/
lemma Disjoint.finiteIntersections {t : TileSet ps ιₜ} (h : t.Disjoint) :
    t.FiniteIntersections :=
  fun _ ↦ Set.Subsingleton.finite (subsingleton_setOfPred_mem_iff_pairwise_disjoint.2 h _)

/-- Whether only finitely many tiles of `t` contain any point of `s`. -/
def FiniteIntersectionsOn : VarTileSetFunction (Set X) ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (s : Set X) (t : TileSet ps ιₜ) ↦ ∀ x ∈ s, {i | x ∈ t i}.Finite,
   by
     intro ιₜ ιₜ' f s t
     simp only [eq_iff_iff]
     refine forall₂_congr (fun x _ ↦ ?_)
     convert Set.finite_image_iff (Set.injOn_of_injective (EquivLike.injective f))
     exact Equiv.setOfPred_apply_symm_eq_image_setOfPred f fun i ↦ x ∈ t i,
   by
     intro ιₜ g s t _
     simp only [eq_iff_iff]
     refine ⟨fun h ↦ fun x ↦ by simpa using h (g • x), fun h ↦ fun x hx ↦ ?_⟩
     convert h (g⁻¹ • x) (Set.mem_smul_set_iff_inv_smul_mem.1 hx) using 2
     ext i
     exact mem_smul_apply_iff_smul_inv_mem⟩

/--
@isnad1 id=iff.0h7v.s6.8f6dbec5f365 from=translated src=- shape=0df24b79 vocab=5aeb33dd
-/
lemma finiteIntersectionsOn_iff {s : Set X} {t : TileSet ps ιₜ} :
    t.FiniteIntersectionsOn s ↔ ∀ x ∈ s, {i | x ∈ t i}.Finite :=
  Iff.rfl

/--
@isnad1 id=tofun.1h10v.s7.7a7f2587d53c from=translated src=- shape=eb3e1eb1 vocab=84588721
-/
lemma FiniteIntersectionsOn.reindex_of_injective {s : Set X} {t : TileSet ps ιₜ}
    (hfi : t.FiniteIntersectionsOn s) {e : ιₜ' → ιₜ} (h : Injective e) :
    (t.reindex e).FiniteIntersectionsOn s :=
  fun x hx ↦ Set.Finite.preimage (Set.injOn_of_injective h) (hfi x hx)

/--
@isnad1 id=tofun.0h11v.s7.1a8bcbab0769 from=translated src=- shape=6afe415b vocab=60b44740
-/
lemma FiniteIntersectionsOn.reindex_of_embeddingLike {s : Set X} {t : TileSet ps ιₜ}
    (hfi : t.FiniteIntersectionsOn s) (e : F) : (t.reindex e).FiniteIntersectionsOn s :=
  FiniteIntersectionsOn.reindex_of_injective hfi (EmbeddingLike.injective _)

/--
@isnad1 id=tofun.1h10v.s7.e0622192f1b0 from=translated src=- shape=04631f47 vocab=e56e6178
-/
lemma FiniteIntersectionsOn.reindex_of_surjective {s : Set X} {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (hfi : (t.reindex e).FiniteIntersectionsOn s) (h : Surjective e) :
    t.FiniteIntersectionsOn s :=
  fun x hx ↦ Set.Finite.of_preimage (hfi x hx) h

/--
@isnad1 id=tofun.0h7v.s6.ba6895354dd3 from=translated src=- shape=8416b16d vocab=d25ebedc
-/
@[simp] lemma finiteIntersectionsOn_of_subsingleton [Subsingleton ιₜ] (s : Set X)
    (t : TileSet ps ιₜ) : t.FiniteIntersectionsOn s :=
  fun _ _ ↦ Set.subsingleton_of_subsingleton.finite

/--
@isnad1 id=tofun.1h9v.s6.292cd6a44f7f from=translated src=- shape=f1970390 vocab=68b1eec6
-/
lemma FiniteIntersectionsOn.subset {s₁ s₂ : Set X} {t : TileSet ps ιₜ}
    (hfi : t.FiniteIntersectionsOn s₂) (hs : s₁ ⊆ s₂) :
    t.FiniteIntersectionsOn s₁ :=
  fun x hx ↦ hfi x (Set.mem_of_mem_of_subset hx hs)

/--
@isnad1 id=tofun.0h6v.s6.e28df8c2805a from=translated src=- shape=4b62c92e vocab=a7db05e8
-/
@[simp] lemma finiteIntersectionsOn_empty (t : TileSet ps ιₜ) :
    t.FiniteIntersectionsOn ∅ := by
  simp [TileSet.FiniteIntersectionsOn]

/--
@isnad1 id=iff.0h6v.s6.9c5ee23204d3 from=translated src=- shape=6398d2b8 vocab=d213ad23
-/
@[simp] lemma finiteIntersectionsOn_univ_iff {t : TileSet ps ιₜ} :
    t.FiniteIntersectionsOn Set.univ ↔ t.FiniteIntersections := by
  simp [TileSet.FiniteIntersections, TileSet.FiniteIntersectionsOn]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=tofun.0h8v.s6.cff25078a8c6 from=translated src=- shape=deee955e vocab=7b5b7270
-/
lemma DisjointOn.finiteIntersectionsOn {s : Set X} {t : TileSet ps ιₜ}
    (h : t.DisjointOn s) : t.FiniteIntersectionsOn s := by
  refine fun x hx ↦ Set.Subsingleton.finite fun i hi j hj ↦ ?_
  by_contra hij
  have h' := h hij
  revert h'
  simp only [imp_false, Set.not_disjoint_iff]
  refine ⟨x, ?_⟩
  simp only [Set.mem_ofPred_eq] at hi hj
  simp [hx, hi, hj]

/--
@isnad1 id=tofun.0h8v.s6.50196915058c from=translated src=- shape=a52daa99 vocab=effa72fa
-/
lemma FiniteIntersections.finiteIntersectionsOn (s : Set X) {t : TileSet ps ιₜ}
    (hfi : t.FiniteIntersections) : t.FiniteIntersectionsOn s :=
  fun _ _ ↦ hfi _

/-- Whether only finitely many distinct tiles of `t` contain any point. -/
def FiniteDistinctIntersections : TileSetFunction ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦ ∀ x, {pt | pt ∈ t ∧ x ∈ pt}.Finite,
   by simp,
   by
     intro ιₜ g t _
     simp only [eq_iff_iff]
     refine ⟨fun h ↦ fun x ↦ ?_, fun h ↦ fun x ↦ ?_⟩
     · convert h (g • x) using 0
       convert (Set.finite_image_iff (Set.injOn_of_injective (MulAction.injective
         (β := PlacedTile ps) g))).symm using 2
       simp [← Set.preimage_smul_inv, mem_smul_iff_smul_inv_mem,
         PlacedTile.mem_inv_smul_iff_smul_mem]
     · convert h (g⁻¹ • x) using 0
       convert Set.finite_image_iff (Set.injOn_of_injective (MulAction.injective
         (β := PlacedTile ps) g)) using 2
       simp [← Set.preimage_smul_inv, mem_smul_iff_smul_inv_mem]⟩

/--
@isnad1 id=iff.0h6v.s7.8da9651415f3 from=translated src=- shape=b768195a vocab=09c06a4e
-/
lemma finiteDistinctIntersections_iff {t : TileSet ps ιₜ} :
    t.FiniteDistinctIntersections ↔ ∀ x, {pt | pt ∈ t ∧ x ∈ pt}.Finite :=
  Iff.rfl

/--
@isnad1 id=tofun.0h9v.s6.29a29a605d3a from=translated src=- shape=1060e0d4 vocab=45cefab2
-/
lemma FiniteDistinctIntersections.reindex {t : TileSet ps ιₜ}
    (hfi : t.FiniteDistinctIntersections) {e : ιₜ' → ιₜ} :
    (t.reindex e).FiniteDistinctIntersections := by
  refine fun x ↦ Set.Finite.subset (hfi x) ?_
  simp only [Set.ofPred_subset_ofPred, and_imp]
  exact fun _ h hx ↦ ⟨mem_of_mem_reindex h, hx⟩

/--
@isnad1 id=tofun.1h9v.s6.f78ef4073e02 from=translated src=- shape=bf68470f vocab=f8232536
-/
lemma FiniteDistinctIntersections.reindex_of_surjective {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (hfi : (t.reindex e).FiniteDistinctIntersections) (h : Surjective e) :
    t.FiniteDistinctIntersections := by
  intro x
  convert hfi x using 4
  exact (mem_reindex_iff_of_surjective h).symm

/--
@isnad1 id=tofun.0h7v.s6.9b311763bad0 from=translated src=- shape=5077c659 vocab=47dc580f
-/
lemma FiniteIntersections.finiteDistinctIntersections {t : TileSet ps ιₜ}
    (h : t.FiniteIntersections) : t.FiniteDistinctIntersections := by
  intro x
  convert Set.Finite.image t (h x)
  ext pt
  simp only [Set.mem_ofPred_eq, Set.mem_image, TileSet.mem_def]
  refine ⟨fun ⟨⟨i, hi⟩, hx⟩ ↦ ?_, fun ⟨i, ⟨hx, hi⟩⟩ ↦ ?_⟩
  · subst hi
    exact ⟨i, hx, rfl⟩
  · subst hi
    exact ⟨⟨i, rfl⟩, hx⟩

/--
@isnad1 id=tofun.0h6v.s5.407686e598e6 from=translated src=- shape=74ce4195 vocab=d8a994c8
-/
@[simp] lemma finiteDistinctIntersections_of_subsingleton [Subsingleton ιₜ] (t : TileSet ps ιₜ) :
    t.FiniteDistinctIntersections :=
  FiniteIntersections.finiteDistinctIntersections (finiteIntersections_of_subsingleton t)

/--
@isnad1 id=tofun.0h7v.s6.df4e512603a6 from=translated src=- shape=5077c659 vocab=597d4f4d
-/
lemma Disjoint.finiteDistinctIntersections {t : TileSet ps ιₜ}
    (h : t.Disjoint) : t.FiniteDistinctIntersections :=
  FiniteIntersections.finiteDistinctIntersections (Disjoint.finiteIntersections h)

/-- Whether only finitely many distinct tiles of `t` contain any point of `s`. -/
def FiniteDistinctIntersectionsOn : VarTileSetFunction (Set X) ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (s : Set X) (t : TileSet ps ιₜ) ↦ ∀ x ∈ s, {pt | pt ∈ t ∧ x ∈ pt}.Finite,
   by simp,
   by
     intro ιₜ g s t _
     simp only [eq_iff_iff]
     refine ⟨fun h ↦ fun x hx ↦ ?_, fun h ↦ fun x hx ↦ ?_⟩
     · convert h (g • x) (by simp [hx]) using 0
       convert (Set.finite_image_iff (Set.injOn_of_injective (MulAction.injective
         (β := PlacedTile ps) g))).symm using 2
       simp [← Set.preimage_smul_inv, mem_smul_iff_smul_inv_mem,
         PlacedTile.mem_inv_smul_iff_smul_mem]
     · convert h (g⁻¹ • x) (Set.mem_smul_set_iff_inv_smul_mem.1 hx) using 0
       convert Set.finite_image_iff (Set.injOn_of_injective (MulAction.injective
         (β := PlacedTile ps) g)) using 2
       simp [← Set.preimage_smul_inv, mem_smul_iff_smul_inv_mem]⟩

/--
@isnad1 id=iff.0h7v.s7.9501e9f2484b from=translated src=- shape=75b65051 vocab=b7367cbc
-/
lemma finiteDistinctIntersectionsOn_iff {s : Set X} {t : TileSet ps ιₜ} :
    t.FiniteDistinctIntersectionsOn s ↔ ∀ x ∈ s, {pt | pt ∈ t ∧ x ∈ pt}.Finite :=
  Iff.rfl

/--
@isnad1 id=tofun.0h10v.s7.bd1230c2b36d from=translated src=- shape=36906f3d vocab=31658615
-/
lemma FiniteDistinctIntersectionsOn.reindex {s : Set X} {t : TileSet ps ιₜ}
    (hfi : t.FiniteDistinctIntersectionsOn s) {e : ιₜ' → ιₜ} :
    (t.reindex e).FiniteDistinctIntersectionsOn s := by
  refine fun x hx ↦ Set.Finite.subset (hfi x hx) ?_
  simp only [Set.ofPred_subset_ofPred, and_imp]
  exact fun _ h hx ↦ ⟨mem_of_mem_reindex h, hx⟩

/--
@isnad1 id=tofun.1h10v.s7.896455684931 from=translated src=- shape=04631f47 vocab=763bfa64
-/
lemma FiniteDistinctIntersectionsOn.reindex_of_surjective {s : Set X} {t : TileSet ps ιₜ}
    {e : ιₜ' → ιₜ} (hfi : (t.reindex e).FiniteDistinctIntersectionsOn s) (h : Surjective e) :
    t.FiniteDistinctIntersectionsOn s := by
  intro x
  convert hfi x using 5
  exact (mem_reindex_iff_of_surjective h).symm

/--
@isnad1 id=tofun.0h8v.s6.3064392d160f from=translated src=- shape=deee955e vocab=2dfa6376
-/
lemma FiniteIntersectionsOn.finiteDistinctIntersectionsOn {s : Set X} {t : TileSet ps ιₜ}
    (h : t.FiniteIntersectionsOn s) : t.FiniteDistinctIntersectionsOn s := by
  intro x hx
  convert Set.Finite.image t (h x hx)
  ext pt
  simp only [Set.mem_ofPred_eq, Set.mem_image, TileSet.mem_def]
  refine ⟨fun ⟨⟨i, hi⟩, hx⟩ ↦ ?_, fun ⟨i, ⟨hx, hi⟩⟩ ↦ ?_⟩
  · subst hi
    exact ⟨i, hx, rfl⟩
  · subst hi
    exact ⟨⟨i, rfl⟩, hx⟩

/--
@isnad1 id=tofun.0h7v.s6.3bc3355a416c from=translated src=- shape=8416b16d vocab=f3735c8d
-/
@[simp] lemma finiteDistinctIntersectionsOn_of_subsingleton [Subsingleton ιₜ] (s : Set X)
    (t : TileSet ps ιₜ) : t.FiniteDistinctIntersectionsOn s :=
  FiniteIntersectionsOn.finiteDistinctIntersectionsOn (finiteIntersectionsOn_of_subsingleton s t)

/--
@isnad1 id=tofun.1h9v.s6.f7befc5daadc from=translated src=- shape=f1970390 vocab=38057674
-/
lemma FiniteDistinctIntersectionsOn.subset {s₁ s₂ : Set X} {t : TileSet ps ιₜ}
    (hfi : t.FiniteDistinctIntersectionsOn s₂) (hs : s₁ ⊆ s₂) :
    t.FiniteDistinctIntersectionsOn s₁ :=
  fun x hx ↦ hfi x (Set.mem_of_mem_of_subset hx hs)

/--
@isnad1 id=tofun.0h6v.s6.e6c6e928b260 from=translated src=- shape=4b62c92e vocab=b5c38e9d
-/
@[simp] lemma finiteDistinctIntersectionsOn_empty (t : TileSet ps ιₜ) :
    t.FiniteDistinctIntersectionsOn ∅ := by
  simp [TileSet.FiniteDistinctIntersectionsOn]

/--
@isnad1 id=iff.0h6v.s6.829c98c4dd71 from=translated src=- shape=6398d2b8 vocab=d21c4c88
-/
@[simp] lemma finiteDistinctIntersectionsOn_univ_iff {t : TileSet ps ιₜ} :
    t.FiniteDistinctIntersectionsOn Set.univ ↔ t.FiniteDistinctIntersections := by
  simp [TileSet.FiniteDistinctIntersections, TileSet.FiniteDistinctIntersectionsOn]

/--
@isnad1 id=tofun.0h8v.s6.c122fb7bc8ee from=translated src=- shape=deee955e vocab=eff18092
-/
lemma DisjointOn.finiteDistinctIntersectionsOn {s : Set X} {t : TileSet ps ιₜ}
    (h : t.DisjointOn s) : t.FiniteDistinctIntersectionsOn s :=
  FiniteIntersectionsOn.finiteDistinctIntersectionsOn (DisjointOn.finiteIntersectionsOn h)

/--
@isnad1 id=tofun.0h8v.s6.27eb1837e14a from=translated src=- shape=a52daa99 vocab=bb3db7d4
-/
lemma FiniteDistinctIntersections.finiteDistinctIntersectionsOn (s : Set X) {t : TileSet ps ιₜ}
    (hfi : t.FiniteDistinctIntersections) : t.FiniteDistinctIntersectionsOn s :=
  fun _ _ ↦ hfi _

end TileSet

end DiscreteTiling

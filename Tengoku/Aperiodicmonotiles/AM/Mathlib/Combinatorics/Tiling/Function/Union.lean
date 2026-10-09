/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Tengoku.Aperiodicmonotiles.AM.Mathlib.Combinatorics.Tiling.Function.Basic
import Tengoku

/-!
# Union properties for tiles

This file defines properties of unions of tiles in a discrete context.

## Main definitions

* `t.UnionEq s`: A `VarTileSetFunction` for whether the union of the tiles of `t` is the
set `s`.

* `t.UnionEqUniv`: A `TileSetFunction` for whether the union of the tiles of `t` is the
whole of `X`.

## References

* [Branko Grünbaum and G. C. Shephard, *Tilings and Patterns*][GrunbaumShephard1987]
-/

noncomputable section

namespace DiscreteTiling

open Function
open scoped Pointwise

variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ ιₜ' : Type*}

namespace TileSet

/-- Whether the union of the tiles of `t` is the set `s`. -/
def UnionEq : VarTileSetFunction (Set X) ps Prop ⊤ :=
  ⟨fun {ιₜ : Type*} (s : Set X) (t : TileSet ps ιₜ) ↦ (⋃ i, (t i : Set X)) = s,
   by
     intro ιₜ ιₜ' f s t
     simp only [eq_iff_iff]
     convert Iff.rfl
     exact f.symm.iSup_comp.symm,
   by
     simp [TileSet.smul_apply, ← Set.smul_set_iUnion]⟩

/--
@isnad1 id=iff.0h7v.s6.9ec9dc71652f from=translated src=- shape=18ddcddd vocab=07ed4775
-/
lemma unionEq_iff {t : TileSet ps ιₜ} {s : Set X} : t.UnionEq s ↔ (⋃ i, (t i : Set X)) = s :=
  Iff.rfl

/--
@isnad1 id=iff.0h7v.s7.f67c2408430a from=translated src=- shape=16dcc56e vocab=8bdb93c5
-/
lemma unionEq_iff' {t : TileSet ps ιₜ} {s : Set X} :
    t.UnionEq s ↔ (⋃ pt ∈ t, (pt : Set X)) = s := by
  rw [unionEq_iff, union_of_mem_eq_iUnion]

/--
@isnad1 id=iff.0h9v.s6.99360cef4490 from=translated src=- shape=c22f527a vocab=ed578ff9
-/
@[simp] lemma UnionEq.exists_mem_iff {t : TileSet ps ιₜ} {s : Set X} (h : t.UnionEq s) {x : X} :
    (∃ i, x ∈ t i) ↔ x ∈ s := by
  rw [← unionEq_iff'.1 h]
  simp

/--
@isnad1 id=iff.0h9v.s7.90348b7385eb from=translated src=- shape=d3392d4a vocab=580e2546
-/
lemma UnionEq.exists_mem_mem_iff {t : TileSet ps ιₜ} {s : Set X} (h : t.UnionEq s) {x : X} :
    (∃ pt ∈ t, x ∈ pt) ↔ x ∈ s := by
  rw [← unionEq_iff'.1 h]
  simp

/--
@isnad1 id=iff.1h9v.s7.fc778790e5d8 from=translated src=- shape=873d3360 vocab=85a02e30
-/
@[simp] lemma unionEq_reindex_iff_of_surjective {t : TileSet ps ιₜ} {s : Set X} {e : ιₜ' → ιₜ}
    (h : Surjective e) : (t.reindex e).UnionEq s ↔ t.UnionEq s :=
  (h.iUnion_comp (fun i ↦ (t i : Set X))).congr_left

/--
@isnad1 id=iff.0h8v.s7.03cd9d36c4c5 from=translated src=- shape=b8c7de1a vocab=e15dff24
-/
lemma unionEq_smul_set_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    t.UnionEq (g • s) ↔ (g⁻¹ • t).UnionEq s := by
  nth_rewrite 1 [← one_smul G t]
  rw [← mul_inv_cancel g, mul_smul, VarTileSetFunction.smul_iff]
  exact Subgroup.mem_top _

/--
@isnad1 id=iff.0h8v.s7.ed7e9c27c0c1 from=translated src=- shape=e4460160 vocab=e15dff24
-/
lemma unionEq_smul_tileSet_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    (g • t).UnionEq s ↔ t.UnionEq (g⁻¹ • s) := by
  nth_rewrite 2 [← one_smul G t]
  rw [← inv_mul_cancel g, mul_smul, VarTileSetFunction.smul_iff]
  exact Subgroup.mem_top _

/--
@isnad1 id=tofun.0h6v.s6.a865f36915ce from=translated src=- shape=6c8892b1 vocab=53fc68a2
-/
@[simp] lemma unionEq_empty [IsEmpty ιₜ] (t : TileSet ps ιₜ) : t.UnionEq ∅ := by
  simp [unionEq_iff]

/-- Whether the union of the tiles of `t` is the whole of `X`. -/
def UnionEqUniv : TileSetFunction ps Prop ⊤ := (UnionEq.toTileSetFunction Set.univ).ofLE (by simp)

/--
@isnad1 id=iff.0h6v.s6.bab6d3ee58a9 from=translated src=- shape=b0826efc vocab=bca63ead
-/
lemma unionEqUniv_iff {t : TileSet ps ιₜ} : t.UnionEqUniv ↔ (⋃ i, (t i : Set X)) = Set.univ :=
  Iff.rfl

/--
@isnad1 id=iff.0h6v.s7.7cbbfbcd5ce6 from=translated src=- shape=e255d460 vocab=822fb307
-/
lemma unionEqUniv_iff' {t : TileSet ps ιₜ} :
    t.UnionEqUniv ↔ (⋃ pt ∈ t, (pt : Set X)) = Set.univ := by
  rw [unionEqUniv_iff, union_of_mem_eq_iUnion]

/--
@isnad1 id=iff.0h6v.s6.d07f96330795 from=translated src=- shape=343a49be vocab=3c2c92bd
-/
lemma unionEqUniv_iff_unionEq {t : TileSet ps ιₜ} : t.UnionEqUniv ↔ t.UnionEq Set.univ :=
  Iff.rfl

/--
@isnad1 id=ex.0h8v.s6.1c38148d01ac from=translated src=- shape=85d12a7a vocab=38ccc32a
-/
lemma UnionEqUniv.exists_mem {t : TileSet ps ιₜ} (h : t.UnionEqUniv) (x : X) :
    ∃ i, x ∈ t i := by
  rw [unionEqUniv_iff_unionEq] at h
  rw [UnionEq.exists_mem_iff h]
  exact Set.mem_univ _

/--
@isnad1 id=ex.0h8v.s6.c100865f9ab3 from=translated src=- shape=c4757f1b vocab=4e9a4ef9
-/
lemma UnionEqUniv.exists_mem_mem {t : TileSet ps ιₜ} (h : t.UnionEqUniv) (x : X) :
    ∃ pt ∈ t, x ∈ pt := by
  rw [unionEqUniv_iff_unionEq] at h
  rw [UnionEq.exists_mem_mem_iff h]
  exact Set.mem_univ _

/--
@isnad1 id=iff.1h8v.s6.722960e57222 from=translated src=- shape=06ff962e vocab=927ba5a1
-/
@[simp] lemma unionEqUniv_reindex_iff_of_surjective {t : TileSet ps ιₜ} {e : ιₜ' → ιₜ}
    (h : Surjective e) : (t.reindex e).UnionEqUniv ↔ t.UnionEqUniv :=
  unionEq_reindex_iff_of_surjective h

end TileSet

end DiscreteTiling

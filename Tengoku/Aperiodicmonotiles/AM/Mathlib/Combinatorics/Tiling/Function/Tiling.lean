/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Tengoku.Aperiodicmonotiles.AM.Mathlib.Combinatorics.Tiling.Function.Disjoint
import Tengoku.Aperiodicmonotiles.AM.Mathlib.Combinatorics.Tiling.Function.Union

/-!
# Tilings

This file defines when tiles in a discrete context make a tiling of the whole space or part thereof.

## Main definitions

* `t.IsTilingOf s`: A `VarTileSetFunction` for whether `t` is a tiling of the set `s`.

* `t.IsTiling`: A `TileSetFunction` for whether `t` is a tiling of `X`.

## References

* [Branko Grünbaum and G. C. Shephard, *Tilings and Patterns*][GrunbaumShephard1987]
-/

noncomputable section

namespace DiscreteTiling

open Function
open scoped Pointwise

variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ : Type*}

namespace TileSet

/-- Whether `t` is a tiling of the set `s`. -/
def IsTilingOf : VarTileSetFunction (Set X) ps Prop ⊤ :=
  (TileSet.Disjoint.toVarTileSetFunction (Set X)).comp₂ UnionEq (· ∧ ·)

/--
@isnad1 id=iff.0h7v.s7.4828fc186c29 from=translated src=- shape=a426c93e vocab=5aaa61e7
-/
lemma isTilingOf_iff {t : TileSet ps ιₜ} {s : Set X} : t.IsTilingOf s ↔
    (Pairwise fun i j ↦ Disjoint (t i : Set X) (t j)) ∧ (⋃ i, (t i : Set X)) = s :=
  Iff.rfl

/--
@isnad1 id=iff.0h7v.s7.c6a368d902ce from=translated src=- shape=d2a6302a vocab=a7cb3724
-/
lemma isTilingOf_iff' {t : TileSet ps ιₜ} {s : Set X} : t.IsTilingOf s ↔
    t.Disjoint ∧ t.UnionEq s :=
  Iff.rfl

/--
@isnad1 id=tofun.0h8v.s6.459fa67f91f6 from=translated src=- shape=aa260909 vocab=a59fb0b5
-/
lemma IsTilingOf.disjoint {t : TileSet ps ιₜ} {s : Set X} (h : t.IsTilingOf s) :
    t.Disjoint :=
  And.left h

/--
@isnad1 id=tofun.0h8v.s6.8eaf39f31634 from=translated src=- shape=dc276e07 vocab=fda865b0
-/
lemma IsTilingOf.unionEq {t : TileSet ps ιₜ} {s : Set X} (h : t.IsTilingOf s) :
    t.UnionEq s :=
  And.right h

/--
@isnad1 id=iff.1h7v.s8.24d21737fdf9 from=translated src=- shape=c1eccfb6 vocab=0aaf7611
-/
lemma isTilingOf_iff_of_injective {t : TileSet ps ιₜ} {s : Set X} (h : Injective t) :
    t.IsTilingOf s ↔ ((t : Set (PlacedTile ps)).Pairwise fun x y ↦ Disjoint (x : Set X) y) ∧
      (⋃ pt ∈ t, (pt : Set X)) = s := by
  rw [isTilingOf_iff, ← TileSet.disjoint_iff, ← coeSet_disjoint_iff_disjoint_of_injective h,
    union_of_mem_eq_iUnion]

/--
@isnad1 id=iff.0h8v.s7.344d8ee7ecbf from=translated src=- shape=b8c7de1a vocab=ab8e02d9
-/
lemma isTilingOf_smul_set_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    t.IsTilingOf (g • s) ↔ (g⁻¹ • t).IsTilingOf s := by
  nth_rewrite 1 [← one_smul G t]
  rw [← mul_inv_cancel g, mul_smul, VarTileSetFunction.smul_iff]
  exact Subgroup.mem_top _

/--
@isnad1 id=iff.0h8v.s7.aba8c99d1470 from=translated src=- shape=e4460160 vocab=ab8e02d9
-/
lemma isTilingOf_smul_tileSet_iff {s : Set X} {t : TileSet ps ιₜ} {g : G} :
    (g • t).IsTilingOf s ↔ t.IsTilingOf (g⁻¹ • s) := by
  nth_rewrite 2 [← one_smul G t]
  rw [← inv_mul_cancel g, mul_smul, VarTileSetFunction.smul_iff]
  exact Subgroup.mem_top _

/--
@isnad1 id=tofun.0h6v.s6.20d088a2344b from=translated src=- shape=6c8892b1 vocab=569569e0
-/
@[simp] lemma isTilingOf_empty [IsEmpty ιₜ] (t : TileSet ps ιₜ) : t.IsTilingOf ∅ := by
  simp [isTilingOf_iff, Subsingleton.pairwise]

/-- Whether `t` is a tiling of the whole of `X`. -/
def IsTiling : TileSetFunction ps Prop ⊤ := TileSet.Disjoint.comp₂ (UnionEqUniv) (· ∧ ·)

/--
@isnad1 id=iff.0h6v.s7.70dced86a05a from=translated src=- shape=b50ba3ed vocab=85435599
-/
lemma isTiling_iff {t : TileSet ps ιₜ} : t.IsTiling ↔
    (Pairwise fun i j ↦ Disjoint (t i : Set X) (t j)) ∧ (⋃ i, (t i : Set X)) = Set.univ :=
  Iff.rfl

/--
@isnad1 id=iff.0h6v.s6.25f9bee32263 from=translated src=- shape=6f45e6c6 vocab=95118a87
-/
lemma isTiling_iff' {t : TileSet ps ιₜ} : t.IsTiling ↔ t.Disjoint ∧ t.UnionEqUniv :=
  Iff.rfl

/--
@isnad1 id=iff.1h6v.s7.e8a3d278cd05 from=translated src=- shape=aab3f308 vocab=1a00d3ab
-/
lemma isTiling_iff_of_injective {t : TileSet ps ιₜ} (h : Injective t) :
    t.IsTiling ↔ ((t : Set (PlacedTile ps)).Pairwise fun x y ↦ Disjoint (x : Set X) y) ∧
      (⋃ pt ∈ t, (pt : Set X)) = Set.univ := by
  rw [isTiling_iff, ← TileSet.disjoint_iff, ← coeSet_disjoint_iff_disjoint_of_injective h,
    union_of_mem_eq_iUnion]

/--
@isnad1 id=tofun.0h7v.s6.e6533a141f7f from=translated src=- shape=5077c659 vocab=62dc6fdb
-/
lemma IsTiling.disjoint {t : TileSet ps ιₜ} (h : t.IsTiling) : t.Disjoint :=
  And.left h

/--
@isnad1 id=tofun.0h7v.s6.6c74b6ae4704 from=translated src=- shape=5077c659 vocab=5e2bd551
-/
lemma IsTiling.unionEqUniv {t : TileSet ps ιₜ} (h : t.IsTiling) : t.UnionEqUniv :=
  And.right h

/--
@isnad1 id=tofun.0h8v.s6.7d3990444aae from=translated src=- shape=aa260909 vocab=c7c4a5ec
-/
lemma IsTilingOf.finiteIntersections {t : TileSet ps ιₜ} {s : Set X} (h : t.IsTilingOf s) :
    t.FiniteIntersections :=
  Disjoint.finiteIntersections (IsTilingOf.disjoint h)

/--
@isnad1 id=tofun.0h7v.s6.a32d383616da from=translated src=- shape=5077c659 vocab=9f101c3e
-/
lemma IsTiling.finiteIntersections {t : TileSet ps ιₜ} (h : t.IsTiling) :
    t.FiniteIntersections :=
  Disjoint.finiteIntersections (IsTiling.disjoint h)

/--
@isnad1 id=tofun.0h8v.s6.5184ec8a025e from=translated src=- shape=aa260909 vocab=0a4af1b0
-/
lemma IsTilingOf.finiteDistinctIntersections {t : TileSet ps ιₜ} {s : Set X}
    (h : t.IsTilingOf s) : t.FiniteDistinctIntersections :=
  FiniteIntersections.finiteDistinctIntersections (IsTilingOf.finiteIntersections h)

/--
@isnad1 id=tofun.0h7v.s6.a7265ce02107 from=translated src=- shape=5077c659 vocab=f883fbee
-/
lemma IsTiling.finiteDistinctIntersections {t : TileSet ps ιₜ}
    (h : t.IsTiling) : t.FiniteDistinctIntersections :=
  FiniteIntersections.finiteDistinctIntersections (IsTiling.finiteIntersections h)

end TileSet

end DiscreteTiling

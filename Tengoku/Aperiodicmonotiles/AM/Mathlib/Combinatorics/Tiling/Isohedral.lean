/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Tengoku.Aperiodicmonotiles.AM.Mathlib.Combinatorics.Tiling.Function.Disjoint
import Tengoku.Aperiodicmonotiles.AM.Mathlib.Combinatorics.Tiling.Function.Union
import Tengoku

/-!
# Isohedral numbers of tilings and protosets

This file defines the action of a tiling's symmetry group on the tiles of that tiling, and
isohedral numbers of tilings and protosets in a discrete context.

The isohedral number of a tiling is the number of orbits of tiles under the action of its
symmetry group.  We define this for an arbitrary `TileSet`.  The isohedral number of a protoset
(possibly with matching rules) is the minimum of the isohedral numbers of tilings by that
protoset (that satisfy those matching rules).

## Main definitions

* `t.isohedralNumber`: A `TileSetFunction` for the isohedral number of `t`, as a
`Cardinal`.

* `t.isohedralNumberNat`: A `TileSetFunction` for the isohedral number of `t`, as a
natural number.

* `Protoset.isohedralNumber`: The isohedral number of a protoset, as a `Cardinal`.

* `Protoset.isohedralNumberNat`: The isohedral number of a protoset, as a natural number.

## References

* [Branko Grünbaum and G. C. Shephard, *Tilings and Patterns*][GrunbaumShephard1987]
-/

noncomputable section

namespace DiscreteTiling

open Function
open scoped Cardinal Pointwise

variable {G X ιₚ ιₜ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}

namespace TileSet

instance (t : TileSet ps ιₜ) : SMul t.symmetryGroup (t : Set (PlacedTile ps)) where
  smul g pt := ⟨(g : G) • ↑pt, smul_mem_of_mem_of_mem_symmetryGroup g.property pt.property⟩

/--
@isnad1 id=eq.0h8v.s9.002609457262 from=translated src=- shape=53dc928f vocab=06da2411
-/
lemma coe_symmetryGroup_smul (t : TileSet ps ιₜ) (g : t.symmetryGroup)
    (pt : (t : Set (PlacedTile ps))) : ((g • pt : (t : Set (PlacedTile ps))) : PlacedTile ps) =
      g • (pt : PlacedTile ps) :=
  rfl

instance (t : TileSet ps ιₜ) : MulAction t.symmetryGroup (t : Set (PlacedTile ps)) where
  __ : SMul t.symmetryGroup (t : Set (PlacedTile ps)) := inferInstance
  one_smul pt := by
    simp [Subtype.ext_iff, coe_symmetryGroup_smul]
  mul_smul x y pt := by
    simp [Subtype.ext_iff, coe_symmetryGroup_smul, mul_smul]

/--
@isnad1 id=iff.0h9v.s9.240911395af6 from=translated src=- shape=77e42a81 vocab=06da2411
-/
lemma mem_smul_symmetryGroup_iff {t : TileSet ps ιₜ} {g : t.symmetryGroup}
    {pt : (t : Set (PlacedTile ps))} {x : X} :
    x ∈ ((g • pt : (t : Set (PlacedTile ps))) : PlacedTile ps) ↔ x ∈ g • (pt : PlacedTile ps) :=
  Iff.rfl

/--
@isnad1 id=iff.0h9v.s9.27cb07e58774 from=translated src=- shape=4eb104f5 vocab=06da2411
-/
lemma smul_mem_smul_symmetryGroup_iff {t : TileSet ps ιₜ} (g : t.symmetryGroup)
    {pt : (t : Set (PlacedTile ps))} {x : X} :
    g • x ∈ ((g • pt : (t : Set (PlacedTile ps))) : PlacedTile ps) ↔
      x ∈ (pt : PlacedTile ps) := by
  simp [mem_smul_symmetryGroup_iff, Subgroup.smul_def]

/--
@isnad1 id=iff.0h9v.s9.3170ec123675 from=translated src=- shape=39b2a479 vocab=5a6e6381
-/
lemma mem_smul_symmetryGroup_iff_smul_inv_mem {t : TileSet ps ιₜ} (g : t.symmetryGroup)
    {pt : (t : Set (PlacedTile ps))} {x : X} :
    x ∈ ((g • pt : (t : Set (PlacedTile ps))) : PlacedTile ps) ↔
      g⁻¹ • x ∈ (pt : PlacedTile ps) := by
  simp_rw [mem_smul_symmetryGroup_iff, Subgroup.smul_def, Subgroup.coe_inv,
           PlacedTile.mem_smul_iff_smul_inv_mem]

/--
@isnad1 id=iff.0h9v.s9.6ef87456f395 from=translated src=- shape=28f3f0d9 vocab=5a6e6381
-/
lemma mem_inv_smul_symmetryGroup_iff_smul_mem {t : TileSet ps ιₜ} (g : t.symmetryGroup)
    {pt : (t : Set (PlacedTile ps))} {x : X} :
    x ∈ ((g⁻¹ • pt : (t : Set (PlacedTile ps))) : PlacedTile ps) ↔
      g • x ∈ (pt : PlacedTile ps) := by
  simp_rw [mem_smul_symmetryGroup_iff, Subgroup.smul_def, Subgroup.coe_inv,
           PlacedTile.mem_inv_smul_iff_smul_mem]

/-- An equivalence between the orbits of tiles in a `TileSet` acted on by a group element and the
orbits in the original `TileSet`. -/
def smulOrbitEquiv (g : G) (t : TileSet ps ιₜ) :
    MulAction.orbitRel.Quotient (g • t).symmetryGroup
      ((g • t : TileSet ps ιₜ) : Set (PlacedTile ps)) ≃
        MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps)) where
  toFun pt := Quotient.liftOn' pt
    (fun x ↦ ⟦⟨g⁻¹ • ↑x, mem_smul_iff_smul_inv_mem.1 x.property⟩⟧)
    (fun x y h ↦ by
      convert Quotient.eq''.2 ?_
      rw [MulAction.orbitRel_apply] at h ⊢
      simp only [MulAction.mem_orbit_iff, Subtype.exists, Subtype.ext_iff] at h
      simp only [MulAction.mem_orbit_iff, Subtype.exists, Subtype.ext_iff]
      rcases h with ⟨a, ha, haa⟩
      change a • (y : PlacedTile ps) = x at haa
      refine ⟨g⁻¹ * a * g, mem_symmetryGroup_smul_iff'.1 ha, ?_⟩
      change (g⁻¹ * a * g) • (g⁻¹ • (y : PlacedTile ps)) = g⁻¹ • ↑x
      simpa [mul_smul] using haa)
  invFun pt := Quotient.liftOn' pt
    (fun x ↦ ⟦⟨g • ↑x, (smul_mem_smul_iff g).2 x.property⟩⟧)
    (fun x y h ↦ by
      convert Quotient.eq''.2 ?_
      rw [MulAction.orbitRel_apply] at h ⊢
      simp only [MulAction.mem_orbit_iff, Subtype.exists, Subtype.ext_iff] at h
      simp only [MulAction.mem_orbit_iff, Subtype.exists, Subtype.ext_iff]
      rcases h with ⟨a, ha, haa⟩
      change a • (y : PlacedTile ps) = x at haa
      refine ⟨g * a * g⁻¹, (mem_symmetryGroup_smul_iff g).2 ha, ?_⟩
      change (g * a * g⁻¹) • (g • (y : PlacedTile ps)) = g • ↑x
      simpa [mul_smul] using haa)
  left_inv := by
    intro x
    induction x using Quotient.inductionOn'
    simp only [Quotient.liftOn'_mk'']
    convert rfl
    simp
  right_inv := by
    intro x
    induction x using Quotient.inductionOn'
    simp only [Quotient.liftOn'_mk'']
    convert rfl
    simp

/-- The number of orbits of tiles under the action of the symmetry group of a `TileSet`. This
definition actually uses the set of tiles, but it does not matter if there are duplicate tiles
because duplicate tiles are always equivalent under the symmetry group when considered to act by
the combination of a group element and a permutation of the index type. -/
def isohedralNumber : TileSetFunction ps Cardinal ⊤ :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦
    #(MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))),
  by
    refine fun {ιₜ ιₜ'} (f t) ↦
      Cardinal.eq.2 ⟨Quotient.congr (Equiv.setCongr (by simp)) fun x y ↦ ?_⟩
    simp_rw [MulAction.orbitRel_apply]
    simp only [MulAction.mem_orbit_iff, Subtype.exists, symmetryGroup_reindex,
               Equiv.setCongr_apply, Subtype.ext_iff]
    exact Iff.rfl,
  fun {ιₜ g} (t _) ↦ Cardinal.eq.2 ⟨smulOrbitEquiv g t⟩⟩

/--
@isnad1 id=eq.0h6v.s7.178061eca2a1 from=translated src=- shape=8f589a37 vocab=62893608
-/
lemma isohedralNumber_eq_card (t : TileSet ps ιₜ) :
    t.isohedralNumber = #(MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))) :=
  rfl

/--
@isnad1 id=iff.0h6v.s6.7eb9e938232a from=translated src=- shape=f8cea536 vocab=a1278f74
-/
lemma isohedralNumber_le_one_iff {t : TileSet ps ιₜ} :
    t.isohedralNumber ≤ 1 ↔ MulAction.IsPretransitive t.symmetryGroup
    (t : Set (PlacedTile ps)) := by
  rw [isohedralNumber_eq_card, Cardinal.le_one_iff_subsingleton,
      MulAction.pretransitive_iff_subsingleton_quotient]

/--
@isnad1 id=iff.0h6v.s6.28856ab0db4a from=translated src=- shape=9f7249d7 vocab=9b9fe59d
-/
lemma isohedralNumber_ne_zero_iff (t : TileSet ps ιₜ) : t.isohedralNumber ≠ 0 ↔ Nonempty ιₜ := by
  rw [isohedralNumber_eq_card, Cardinal.mk_ne_zero_iff, nonempty_quotient_iff,
      Set.nonempty_coe_sort, coeSet_apply, Set.range_nonempty_iff_nonempty]

/--
@isnad1 id=iff.0h6v.s6.ee0e50615c5b from=translated src=- shape=9f7249d7 vocab=57d65c3e
-/
lemma isohedralNumber_eq_zero_iff (t : TileSet ps ιₜ) : t.isohedralNumber = 0 ↔ IsEmpty ιₜ := by
  rw [← not_iff_not, not_isEmpty_iff]
  exact t.isohedralNumber_ne_zero_iff

/--
@isnad1 id=iff.0h6v.s6.f82ad32ec452 from=translated src=- shape=4e576dd1 vocab=93222df1
-/
lemma isohedralNumber_eq_one_iff {t : TileSet ps ιₜ} :
    t.isohedralNumber = 1
      ↔ Nonempty ιₜ ∧ MulAction.IsPretransitive t.symmetryGroup (t : Set (PlacedTile ps)) := by
  refine ⟨fun h ↦ ⟨t.isohedralNumber_ne_zero_iff.1 ?_, isohedralNumber_le_one_iff.1 h.le⟩,
          fun ⟨hn, ht⟩ ↦ (le_antisymm
            (isohedralNumber_le_one_iff.2 ht)
            (Cardinal.one_le_iff_ne_zero.2 (t.isohedralNumber_ne_zero_iff.2 hn)))⟩
  simp [h]

/--
@isnad1 id=iff.0h6v.s7.f41fae8b62e6 from=translated src=- shape=c29c7cf1 vocab=d87f6f19
-/
lemma aleph0_le_isohedralNumber_iff {t : TileSet ps ιₜ} :
    ℵ₀ ≤ t.isohedralNumber ↔
      Infinite (MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))) := by
  rw [Cardinal.infinite_iff, isohedralNumber_eq_card]

/--
@isnad1 id=iff.0h6v.s7.a47bbeddc333 from=translated src=- shape=1f162124 vocab=4e581e82
-/
lemma isohedralNumber_lt_aleph0_iff {t : TileSet ps ιₜ} :
    t.isohedralNumber < ℵ₀ ↔
      Finite (MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))) := by
  rw [isohedralNumber_eq_card, Cardinal.lt_aleph0_iff_finite]

/-- The number of orbits of tiles under the action of the symmetry group of a `TileSet`, as a
natural number; zero if infinite. -/
def isohedralNumberNat : TileSetFunction ps ℕ ⊤ := isohedralNumber.comp Cardinal.toNat

/--
@isnad1 id=eq.0h6v.s7.fbeaf1a1f513 from=translated src=- shape=8f589a37 vocab=f99f7523
-/
lemma isohedralNumberNat_eq_card (t : TileSet ps ιₜ) :
    t.isohedralNumberNat =
      Nat.card (MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))) :=
  rfl

/--
@isnad1 id=iff.0h6v.s6.83cb84106fea from=translated src=- shape=4e576dd1 vocab=2a6e82a0
-/
lemma isohedralNumberNat_eq_one_iff {t : TileSet ps ιₜ} :
    t.isohedralNumberNat = 1
      ↔ Nonempty ιₜ ∧ MulAction.IsPretransitive t.symmetryGroup (t : Set (PlacedTile ps)) := by
  rw [← isohedralNumber_eq_one_iff]
  simp [isohedralNumberNat]

/--
@isnad1 id=iff.0h6v.s7.4f9434bd66e7 from=translated src=- shape=53aee561 vocab=9074624d
-/
lemma isohedralNumberNat_eq_zero_iff {t : TileSet ps ιₜ} :
    t.isohedralNumberNat = 0 ↔ IsEmpty ιₜ ∨
      Infinite (MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))) := by
  simp [isohedralNumberNat, isohedralNumber_eq_zero_iff, aleph0_le_isohedralNumber_iff]

/-- The symmetry group also acts on pairs of a tile and a point in that tile. -/
def subMulActionTilePoint (t : TileSet ps ιₜ) :
    SubMulAction t.symmetryGroup (Prod (t : Set (PlacedTile ps)) X) where
  carrier := {x | x.2 ∈ (x.1 : PlacedTile ps)}
  smul_mem' g x h := by
    rcases x with ⟨pt, x⟩
    simp only [Prod.smul_mk, Set.mem_ofPred_eq, coe_symmetryGroup_smul, Subgroup.smul_def] at h ⊢
    exact (PlacedTile.smul_mem_smul_iff ↑g).2 h

instance (t : TileSet ps ιₜ) : MulAction t.symmetryGroup
    {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)} :=
  SubMulAction.SMulMemClass.toMulAction (S' := subMulActionTilePoint t)

/--
@isnad1 id=eq.0h8v.s10.528aa3b9bea5 from=translated src=- shape=078b8725 vocab=f6c92e50
-/
lemma coe_smul_tilePoint {t : TileSet ps ιₜ} (g : t.symmetryGroup)
    (x : {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}) :
    ((g • x : {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}) : Prod _ _) =
      g • (x : Prod (t : Set (PlacedTile ps)) X) :=
  rfl

/-- Map from the quotient by the action of the symmetry group on pairs of a tile and a point in
that tile to the quotient by the action on tiles. -/
def quotientPlacedTileOfquotientTilePoint (t : TileSet ps ιₜ) :
    MulAction.orbitRel.Quotient t.symmetryGroup
      {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)} →
        MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps)) :=
  Subtype.val ∘
  Setoid.comapQuotientEquiv _ _ ∘
  Quot.mapRight (MulAction.orbitRel_le_fst _ _ _) ∘
  Subtype.val ∘
  Setoid.comapQuotientEquiv _ _ ∘
  (Quotient.congrRight <| Setoid.ext_iff.1 <|
    SubMulAction.orbitRel_of_subMul t.subMulActionTilePoint)

/-- Map from the quotient by the action of the symmetry group on pairs of a tile and a point in
that tile to the quotient by the action on points. -/
def quotientPointOfquotientTilePoint (t : TileSet ps ιₜ) :
    MulAction.orbitRel.Quotient t.symmetryGroup
      {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)} →
        MulAction.orbitRel.Quotient t.symmetryGroup X :=
  Subtype.val ∘
  Setoid.comapQuotientEquiv _ _ ∘
  Quot.mapRight (MulAction.orbitRel_le_snd _ _ _) ∘
  Subtype.val ∘
  Setoid.comapQuotientEquiv _ _ ∘
  (Quotient.congrRight <| Setoid.ext_iff.1 <|
    SubMulAction.orbitRel_of_subMul t.subMulActionTilePoint)

/--
@isnad1 id=eq.0h7v.s9.f2c03778ee3a from=translated src=- shape=0b08be3e vocab=d20fc48d
-/
@[simp] lemma quotientPlacedTileOfquotientTilePoint_apply_mk {t : TileSet ps ιₜ}
    (x : {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}) :
    t.quotientPlacedTileOfquotientTilePoint ⟦x⟧ = ⟦(Subtype.val x).1⟧ :=
  rfl

/--
@isnad1 id=eq.0h7v.s9.a67a4a9125e9 from=translated src=- shape=f0b2c966 vocab=8b27b837
-/
@[simp] lemma quotientPointOfquotientTilePoint_apply_mk {t : TileSet ps ιₜ}
    (x : {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}) :
      t.quotientPointOfquotientTilePoint ⟦x⟧ = ⟦(Subtype.val x).2⟧ :=
  rfl

/--
@isnad1 id=surjecti.1h6v.s8.e40903f695be from=translated src=- shape=488b4d1a vocab=3c83de6a
-/
lemma surjective_quotientPlacedTileOfquotientTilePoint {t : TileSet ps ιₜ}
    (h : ∀ i, (t i : Set X).Nonempty) :
    Surjective t.quotientPlacedTileOfquotientTilePoint := by
  intro x
  induction x using Quotient.inductionOn' with
  | h pt =>
    rcases pt with ⟨pt, i, rfl⟩
    obtain ⟨x, hx⟩ := h i
    exact ⟨⟦⟨(⟨t i, apply_mem _ _⟩, x), hx⟩⟧, rfl⟩

/--
@isnad1 id=surjecti.0h7v.s8.d39eb60902b4 from=translated src=- shape=afd3fff9 vocab=fa04fd4c
-/
lemma surjective_quotientPointOfquotientTilePoint {t : TileSet ps ιₜ} (h : t.UnionEqUniv) :
    Surjective t.quotientPointOfquotientTilePoint := by
  intro x
  induction x using Quotient.inductionOn' with
  | h p =>
    obtain ⟨pt, hpt, hp⟩ := UnionEqUniv.exists_mem_mem h p
    exact ⟨⟦⟨(⟨pt, hpt⟩, p), hp⟩⟧, rfl⟩

/--
@isnad1 id=eq.0h7v.s10.3f42facb56f0 from=translated src=- shape=a8dcbcf0 vocab=d65aa277
-/
lemma preimage_quotientPlacedTileOfquotientTilePoint_eq_range {t : TileSet ps ιₜ}
    (pt : (t : Set (PlacedTile ps))) : t.quotientPlacedTileOfquotientTilePoint ⁻¹' {⟦pt⟧} =
      Set.range (fun x : {x // x ∈ (pt : PlacedTile ps)} ↦ ⟦⟨(pt, x), x.property⟩⟧) := by
  refine Set.Subset.antisymm (fun x h ↦ ?_) (Set.range_subset_iff.2 fun x ↦ (Set.mem_singleton _))
  rw [Set.mem_preimage] at h
  induction x using Quotient.inductionOn' with
  | h pt' =>
    rcases pt' with ⟨⟨pt', x⟩, hx⟩
    simp only [quotientPlacedTileOfquotientTilePoint_apply_mk, Set.mem_singleton_iff] at h
    rw [← @Quotient.mk''_eq_mk, Quotient.eq''] at h
    rcases h with ⟨g, rfl⟩
    dsimp only at hx
    rw [mem_smul_symmetryGroup_iff_smul_inv_mem] at hx
    refine ⟨⟨g⁻¹ • x, hx⟩, ?_⟩
    simp only
    rw [← @Quotient.mk''_eq_mk, Quotient.eq'', MulAction.orbitRel_apply]
    refine ⟨g⁻¹, Subtype.ext_iff.2 ?_⟩
    simp [coe_smul_tilePoint]

/--
@isnad1 id=eq.0h7v.s10.3da7f14fd29e from=translated src=- shape=40d8af5c vocab=9d932820
-/
lemma preimage_quotientPointOfquotientTilePoint_eq_range {t : TileSet ps ιₜ} (x : X) :
    t.quotientPointOfquotientTilePoint ⁻¹' {⟦x⟧} =
      Set.range (fun pt : {pt // pt ∈ t ∧ x ∈ pt} ↦
        ⟦⟨(⟨pt, pt.property.1⟩, x), pt.property.2⟩⟧) := by
  refine Set.Subset.antisymm (fun y h ↦ ?_) (Set.range_subset_iff.2 fun y ↦ (Set.mem_singleton _))
  rw [Set.mem_preimage] at h
  induction y using Quotient.inductionOn' with
  | h pt' =>
    rcases pt' with ⟨⟨pt', y⟩, hy⟩
    simp only [quotientPointOfquotientTilePoint_apply_mk, Set.mem_singleton_iff] at h
    rw [← @Quotient.mk''_eq_mk, Quotient.eq''] at h
    rcases h with ⟨g, rfl⟩
    dsimp only at hy
    rw [← mem_inv_smul_symmetryGroup_iff_smul_mem] at hy
    refine ⟨⟨(g⁻¹ • pt' : (t : Set (PlacedTile ps))),
             (g⁻¹ • pt' : (t : Set (PlacedTile ps))).property, hy⟩, ?_⟩
    simp only
    rw [← @Quotient.mk''_eq_mk, Quotient.eq'', MulAction.orbitRel_apply]
    refine ⟨g⁻¹, Subtype.ext_iff.2 ?_⟩
    simp [coe_smul_tilePoint]

/--
@isnad1 id=finite.1h7v.s9.69d4cdcfcf8c from=translated src=- shape=592c8ed1 vocab=52f37aee
-/
lemma finite_preimage_quotientPlacedTileOfquotientTilePoint {t : TileSet ps ιₜ}
    {pt : (t : Set (PlacedTile ps))} (h : ((pt : PlacedTile ps) : Set X).Finite) :
    (t.quotientPlacedTileOfquotientTilePoint ⁻¹' {⟦pt⟧}).Finite := by
  have := h.to_subtype
  rw [preimage_quotientPlacedTileOfquotientTilePoint_eq_range]
  exact Set.finite_range _

/--
@isnad1 id=finite.0h8v.s9.a3b7f45a23f2 from=translated src=- shape=0445a89d vocab=d13b1c33
-/
lemma finite_preimage_quotientPointOfquotientTilePoint {t : TileSet ps ιₜ} (x : X)
    (h : t.FiniteDistinctIntersectionsOn {x}) :
    (t.quotientPointOfquotientTilePoint ⁻¹' {⟦x⟧}).Finite := by
  have hf := (h x (Set.mem_singleton _)).to_subtype
  rw [Set.coe_ofPred] at hf
  rw [preimage_quotientPointOfquotientTilePoint_eq_range]
  exact Set.finite_range _

/--
@isnad1 id=finite.2h6v.s8.e172f16e295f from=translated src=- shape=016848c4 vocab=cfc9284d
-/
lemma finite_quotient_tilePoint_of_isohedralNumber_lt_aleph0 {t : TileSet ps ιₜ}
    (h : t.isohedralNumber < ℵ₀) (hf : ∀ i, (t i : Set X).Finite) :
    Finite (MulAction.orbitRel.Quotient t.symmetryGroup
      {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}) := by
  rw [← Set.finite_univ_iff, ← Set.preimage_univ (f := t.quotientPlacedTileOfquotientTilePoint),
    ← Set.biUnion_preimage_singleton]
  rw [isohedralNumber_lt_aleph0_iff] at h
  refine Finite.Set.finite_biUnion _ _ fun pt _ ↦ ?_
  induction pt using Quotient.inductionOn' with
  | h pt =>
    rw [@Quotient.mk''_eq_mk]
    refine finite_preimage_quotientPlacedTileOfquotientTilePoint ?_
    rcases pt with ⟨pt, i, rfl⟩
    exact hf i

/--
@isnad1 id=lt.2h6v.s8.88b2c9c01f96 from=translated src=- shape=7383dcdf vocab=f92d2cde
-/
lemma isohedralNumber_lt_aleph0_of_finite_quotient_tilePoint {t : TileSet ps ιₜ}
    (hf : Finite (MulAction.orbitRel.Quotient t.symmetryGroup
      {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}))
    (hn : ∀ i, (t i : Set X).Nonempty) : t.isohedralNumber < ℵ₀ := by
  rw [isohedralNumber_lt_aleph0_iff]
  rw [← Set.finite_univ_iff] at hf ⊢
  exact Set.Finite.of_surjOn t.quotientPlacedTileOfquotientTilePoint
    (Set.surjOn_univ.2 (surjective_quotientPlacedTileOfquotientTilePoint hn)) hf

end TileSet

namespace Protoset

variable {H : Subgroup G}

variable (ιₜ) in
/-- The minimum number of orbits of tiles in any `TileSet ps ιₜ` that satisfies the property `p`. -/
def isohedralNumber (p : TileSetFunction ps Prop H) : Cardinal :=
  ⨅ (t : {x : TileSet ps ιₜ // p x}), TileSet.isohedralNumber (t : TileSet ps ιₜ)

/--
@isnad1 id=iff.0h7v.s6.80d44fd48e4e from=translated src=- shape=90fe6e4a vocab=3dca7b43
-/
lemma isohedralNumber_eq_zero_iff {p : TileSetFunction ps Prop H} :
    isohedralNumber ιₜ p = 0 ↔ IsEmpty ιₜ ∨ ∀ t : TileSet ps ιₜ, ¬ p t := by
  simp_rw [isohedralNumber, Cardinal.iInf_eq_zero_iff, TileSet.isohedralNumber_eq_zero_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases h with h | ⟨⟨_, _⟩, hi⟩
    · exact Or.inr ((isEmpty_subtype _).1 h)
    · exact Or.inl hi
  · rcases h with h | h
    · simp only [isEmpty_subtype, h, Subtype.exists, exists_prop, and_true]
      rw [← not_exists]
      exact (Classical.em _).symm
    · simp [h, isEmpty_subtype]

/--
@isnad1 id=iff.0h7v.s6.ebf7b1ceea1e from=translated src=- shape=c433e15f vocab=988e6a80
-/
lemma isohedralNumber_ne_zero_iff {p : TileSetFunction ps Prop H} :
    isohedralNumber ιₜ p ≠ 0 ↔ Nonempty ιₜ ∧ ∃ t : TileSet ps ιₜ, p t := by
  simp [isohedralNumber_eq_zero_iff, not_or]

/--
@isnad1 id=iff.1h8v.s7.3ab70ff665fb from=translated src=- shape=90996530 vocab=8c955077
-/
lemma le_isohedralNumber_iff {p : TileSetFunction ps Prop H} {c : Cardinal} (h : c ≠ 0) :
    c ≤ isohedralNumber ιₜ p ↔
      (∃ t : TileSet ps ιₜ, p t) ∧ ∀ t : TileSet ps ιₜ, p t → c ≤ t.isohedralNumber := by
  rw [isohedralNumber]
  by_cases he : ∃ t : TileSet ps ιₜ, p t
  · simp only [he, true_and]
    rcases he with ⟨xt, hpxt⟩
    have : Nonempty {t : TileSet ps ιₜ // p t} := ⟨xt, hpxt⟩
    rw [le_ciInf_iff']
    exact ⟨fun h ↦ fun t ht ↦ h ⟨t, ht⟩, fun h ⟨t, ht⟩ ↦ h t ht⟩
  · simp only [not_exists] at he
    simp only [he, exists_false, IsEmpty.forall_iff, implies_true, and_true, iff_false, not_le,
      iInf]
    rw [← pos_iff_ne_zero] at h
    convert h
    convert Cardinal.sInf_empty
    simpa [isEmpty_subtype] using he

/--
@isnad1 id=iff.0h7v.s7.f9cabf9f9589 from=translated src=- shape=53c8edf2 vocab=acd3c88c
-/
lemma isohedralNumber_eq_one_iff {p : TileSetFunction ps Prop H} :
    isohedralNumber ιₜ p = 1 ↔ Nonempty ιₜ ∧ ∃ t : TileSet ps ιₜ, p t
      ∧ MulAction.IsPretransitive t.symmetryGroup (t : Set (PlacedTile ps)) := by
  rw [isohedralNumber, iInf]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases Set.eq_empty_or_nonempty (Set.range fun (t : {x : TileSet ps ιₜ // p x}) ↦
      TileSet.isohedralNumber (t : TileSet ps ιₜ)) with he | hn
    · simp [he] at h
    · have h' := csInf_mem hn
      simp only [h, Set.mem_range, Subtype.exists,
        TileSet.isohedralNumber_eq_one_iff] at h'
      rcases h' with ⟨t, hp, hni, hm⟩
      exact ⟨hni, t, hp, hm⟩
  · rcases h with ⟨hn, t, hp, ht⟩
    have hi := TileSet.isohedralNumber_eq_one_iff.2 ⟨hn, ht⟩
    refine IsLeast.csInf_eq ⟨?_, ?_⟩
    · change TileSet.isohedralNumber
        ((⟨t, hp⟩ : {x : TileSet ps ιₜ // p x}) : TileSet ps ιₜ) = 1 at hi
      rw [← hi]
      exact Set.mem_range_self _
    · intro c
      rw [Set.mem_range, Cardinal.one_le_iff_ne_zero]
      rintro ⟨t', rfl⟩
      rwa [TileSet.isohedralNumber_ne_zero_iff]

variable (ιₜ) in
/-- The minimum number of orbits of tiles in any `TileSet ps ιₜ` that satisfies the property `p`,
as a natural number; zero if infinite or if no such `TileSet` exists. -/
def isohedralNumberNat (p : TileSetFunction ps Prop H) : ℕ :=
  Cardinal.toNat <| isohedralNumber ιₜ p

/--
@isnad1 id=iff.0h7v.s7.15db1b247577 from=translated src=- shape=53c8edf2 vocab=71d141d6
-/
lemma isohedralNumberNat_eq_one_iff {p : TileSetFunction ps Prop H} :
    isohedralNumberNat ιₜ p = 1 ↔ Nonempty ιₜ ∧ ∃ t : TileSet ps ιₜ, p t
      ∧ MulAction.IsPretransitive t.symmetryGroup (t : Set (PlacedTile ps)) := by
  rw [← isohedralNumber_eq_one_iff]
  simp [isohedralNumberNat]

end Protoset

end DiscreteTiling

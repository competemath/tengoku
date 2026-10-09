/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Tengoku.Aperiodicmonotiles.AM.Mathlib.Combinatorics.Tiling.TileSet
import Tengoku

/-!
# Cardinality in tilings

This file defines a type for the number of copies of each possible tile in a `TileSet`.

## Main definitions

* `TileSetCard ps`: A number of each image of tiles from the protoset `ps`.

## References

* [Branko Grünbaum and G. C. Shephard, *Tilings and Patterns*][GrunbaumShephard1987]
-/

noncomputable section

namespace DiscreteTiling

open Function
open scoped Cardinal Pointwise

variable {G X ιₚ : Type*} [Group G] [MulAction G X]

variable {ps : Protoset G X ιₚ} {ιₜ E F : Type*}
universe u v
variable {ιᵤ ιᵤ' : Type u} [EquivLike E ιᵤ' ιᵤ] [FunLike F ιᵤ' ιᵤ] [EmbeddingLike F ιᵤ' ιᵤ]

variable (ps) in
/-- A `TileSetCard ps` associates a `Cardinal` to each `PlacedTile ps`. This is a separate
definition rather than just using plain functions because of the action by `G`. The main
definition used for tilings is `TileSet`, which uses indexed families; this definition is
intended for use cases where it is convenient for `TileSet`s related by reindexing to be
equal. -/
@[ext] structure TileSetCard where
  /-- The number of each tile. Use the coercion to a function rather than using `tilesCard`
      directly. -/
  tilesCard : PlacedTile ps → Cardinal.{v}

namespace TileSetCard

instance : Inhabited (TileSetCard ps) := ⟨⟨0⟩⟩

instance : CoeFun (TileSetCard ps) (fun _ ↦ PlacedTile ps → Cardinal) where
  coe := tilesCard

attribute [coe] tilesCard

/--
@isnad1 id=eq.0h5v.s5.1b2ff6ec9290 from=translated src=- shape=d721f256 vocab=0aed15b3
-/
lemma coe_mk (t) : (⟨t⟩ : TileSetCard ps) = t := rfl

/--
@isnad1 id=iff.0h6v.s6.606662088586 from=translated src=- shape=063ebd7c vocab=82f0820a
-/
@[simp, norm_cast] lemma coe_inj {t₁ t₂ : TileSetCard ps} :
    (t₁ : PlacedTile ps → Cardinal) = t₂ ↔ t₁ = t₂ :=
  TileSetCard.ext_iff.symm

/--
@isnad1 id=injectiv.0h4v.s5.b94567190a49 from=translated src=- shape=0aa8f46a vocab=37c24c74
-/
lemma coe_injective :
    Injective (TileSetCard.tilesCard : TileSetCard ps → PlacedTile ps → Cardinal) :=
  fun _ _ ↦ coe_inj.1

instance : Max (TileSetCard ps) :=
  ⟨fun t₁ t₂ ↦ ⟨↑t₁ ⊔ ↑t₂⟩⟩

/--
@isnad1 id=eq.0h6v.s7.42c1228c48d6 from=translated src=- shape=612df5f1 vocab=dc31248a
-/
lemma coe_sup (t₁ t₂ : TileSetCard ps) :
    (t₁ ⊔ t₂ : TileSetCard ps) = (t₁ : PlacedTile ps → Cardinal) ⊔ ↑t₂ :=
  rfl

instance : Min (TileSetCard ps) :=
  ⟨fun t₁ t₂ ↦ ⟨↑t₁ ⊓ ↑t₂⟩⟩

/--
@isnad1 id=eq.0h6v.s7.031e26b7b375 from=translated src=- shape=612df5f1 vocab=85927aa5
-/
lemma coe_inf (t₁ t₂ : TileSetCard ps) :
    (t₁ ⊓ t₂ : TileSetCard ps) = (t₁ : PlacedTile ps → Cardinal) ⊓ ↑t₂ :=
  rfl

instance : PartialOrder (TileSetCard ps) :=
  PartialOrder.lift _ coe_injective

instance : DistribLattice (TileSetCard ps) :=
  coe_injective.distribLattice _ Iff.rfl Iff.rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/--
@isnad1 id=iff.0h6v.s6.0be6b103f4f7 from=translated src=- shape=a1297163 vocab=50c8a7d3
-/
lemma le_def {t₁ t₂ : TileSetCard ps} : t₁ ≤ t₂ ↔ ∀ i, t₁ i ≤ t₂ i :=
  Iff.rfl

instance : MulAction G (TileSetCard ps) where
  smul g t := ⟨fun pt ↦ t (g⁻¹ • pt)⟩
  one_smul t := TileSetCard.ext <| funext <| fun pt ↦ by
    change t _ = _
    simp
  mul_smul g₁ g₂ t := TileSetCard.ext <| funext <| fun pt ↦ by
    change t _ = t _
    convert rfl using 2
    rw [mul_inv_rev, mul_smul]

/--
@isnad1 id=eq.0h7v.s7.2b61a4a3b936 from=translated src=- shape=548c32e3 vocab=69e50104
-/
lemma smul_apply (g : G) (t : TileSetCard ps) (pt : PlacedTile ps) : (g • t) pt = t (g⁻¹ • pt) :=
  rfl

end TileSetCard

namespace TileSet

/-- The number of each tile in the `TileSet`. -/
protected def card (t : TileSet ps ιₜ) : TileSetCard ps :=
  ⟨fun pt ↦ #(t ⁻¹' {pt})⟩

/--
@isnad1 id=eq.0h7v.s6.c5ab688d035a from=translated src=- shape=fa37ee1d vocab=f002d347
-/
lemma card_apply (t : TileSet ps ιₜ) (pt : PlacedTile ps) : t.card pt = #(t ⁻¹' {pt}) :=
  rfl

/--
@isnad1 id=le.1h8v.s6.0b3d418f3837 from=translated src=- shape=9479610a vocab=7dbe106c
-/
lemma card_reindex_le_of_injective (t : TileSet ps ιᵤ) {f : ιᵤ' → ιᵤ} (hf : Injective f) :
    (t.reindex f).card ≤ t.card := by
  simp_rw [TileSetCard.le_def, card_apply, TileSet.coe_reindex, Set.preimage_comp]
  exact fun _ ↦ Cardinal.mk_preimage_of_injective _ _ hf

/--
@isnad1 id=le.0h9v.s6.3f65d4465ad5 from=translated src=- shape=68b18f01 vocab=f3077ccd
-/
lemma card_reindex_le_of_embeddingLike (t : TileSet ps ιᵤ) (f : F) : (t.reindex f).card ≤ t.card :=
  t.card_reindex_le_of_injective (EmbeddingLike.injective f)

/--
@isnad1 id=le.1h8v.s6.37701b669d75 from=translated src=- shape=3bcc0c3a vocab=0e0d4894
-/
lemma card_le_card_reindex_of_surjective (t : TileSet ps ιᵤ) {f : ιᵤ' → ιᵤ} (hf : Surjective f) :
    t.card ≤ (t.reindex f).card := by
  simp_rw [TileSetCard.le_def, card_apply, TileSet.coe_reindex, Set.preimage_comp]
  refine fun pt ↦ Cardinal.mk_preimage_of_subset_range _ _ ?_
  simp [Set.range_eq_univ.2 hf]

/--
@isnad1 id=eq.1h8v.s6.58117c590d1e from=translated src=- shape=9479610a vocab=652e181c
-/
lemma card_reindex_of_bijective (t : TileSet ps ιᵤ) {f : ιᵤ' → ιᵤ} (hf : Bijective f) :
    (t.reindex f).card = t.card :=
  le_antisymm (t.card_reindex_le_of_injective hf.injective)
              (t.card_le_card_reindex_of_surjective hf.surjective)

/--
@isnad1 id=eq.0h9v.s6.936bf10ec93a from=translated src=- shape=9ebdc66f vocab=7554d5b9
-/
@[simp] lemma card_reindex_of_equivLike (t : TileSet ps ιᵤ) (f : E) : (t.reindex f).card = t.card :=
  t.card_reindex_of_bijective (EquivLike.bijective f)

/--
@isnad1 id=iff.0h8v.s6.09cfa3c32e45 from=translated src=- shape=78624596 vocab=a456dd4d
-/
lemma card_eq_iff_exists_reindex_eq {t₁ : TileSet ps ιᵤ} {t₂ : TileSet ps ιᵤ'} :
    t₁.card = t₂.card ↔ ∃ e : ιᵤ' ≃ ιᵤ, t₁.reindex e = t₂ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · simp_rw [TileSetCard.ext_iff, funext_iff, card_apply, Cardinal.eq] at h
    refine ⟨Equiv.ofPreimageEquiv fun pt ↦ (h pt).some.symm, ?_⟩
    simp_rw [TileSet.ext_iff, funext_iff, reindex_apply, Equiv.ofPreimageEquiv_map, implies_true]
  · rintro ⟨e, rfl⟩
    rw [card_reindex_of_equivLike]

/--
@isnad1 id=eq.0h7v.s7.d7241884579d from=translated src=- shape=b3814169 vocab=15499041
-/
lemma card_smul (g : G) (t : TileSet ps ιₜ) : (g • t).card = g • (t.card) := by
  refine TileSetCard.ext <| funext fun pt ↦ ?_
  simp_rw [TileSetCard.smul_apply, card_apply, smul_coe, Set.preimage_comp, Set.preimage_smul,
    Set.smul_set_singleton]

end TileSet

end DiscreteTiling

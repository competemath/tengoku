/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Tengoku

/-!
# Tilings

This file defines some basic concepts related to tilings in a discrete context.

As definitions relating to tilings mostly are meaningful also for collections of tiles that may
overlap or may not cover the whole space, and such collections of tiles are also often of
interest when working with tilings, our formal definitions are generally made for indexed
families of tiles rather than having a specific type limited to a particular notion of tilings,
and further restrictions on such a family are given as hypotheses where needed. Since
collections of possibly overlapping tiles can be of interest, including the case where two tiles
coincide, we work with indexed families rather than sets (as usual, if a set of tiles is more
convenient in a particular case, it may be considered as a family indexed by itself).

## Main definitions

* `TileSet ps ιₜ`: An indexed family of images of tiles from the protoset `ps`.

* `TileSet.symmetryGroup`: The group of symmetries preserving a `TileSet` up to permutation of the
indices.

## References

* [Branko Grünbaum and G. C. Shephard, *Tilings and Patterns*][GrunbaumShephard1987]
-/

noncomputable section

namespace DiscreteTiling

open Function
open scoped Pointwise

variable {G X ιₚ : Type*} [Group G] [MulAction G X]

variable {ps : Protoset G X ιₚ} {ι ιₜ ιₜ' ιₜ'' ιₜ''' E E' F : Type*} {ιₜι ιₜ'ι : ι → Type*}
variable [EquivLike E ιₜ' ιₜ] [EquivLike E' ιₜ'' ιₜ'] [FunLike F ιₜ' ιₜ] [EmbeddingLike F ιₜ' ιₜ]

variable (ps ιₜ) in
/-- A `TileSet ps ιₜ` is an indexed family of `PlacedTile ps`. This is a separate definition
rather than just using plain functions to facilitate defining associated API that can be used
with dot notation. -/
@[ext] structure TileSet where
  /-- The tiles in the family. Use the coercion to a function rather than using `tiles`
      directly. -/
  tiles : ιₜ → PlacedTile ps

namespace TileSet

instance [IsEmpty ιₜ] : Unique (TileSet ps ιₜ) where
  default := ⟨isEmptyElim⟩
  uniq _ := TileSet.ext <| funext isEmptyElim

instance : CoeFun (TileSet ps ιₜ) (fun _ ↦ ιₜ → PlacedTile ps) where
  coe := tiles

attribute [coe] tiles

/--
@isnad1 id=eq.0h6v.s6.abeaa6c50043 from=translated src=- shape=8ebb8b52 vocab=85df7c3b
-/
lemma coe_mk (t) : (⟨t⟩ : TileSet ps ιₜ) = t := rfl

/--
@isnad1 id=iff.0h7v.s6.878deb642809 from=translated src=- shape=2727e182 vocab=d71086f3
-/
@[simp, norm_cast] lemma coe_inj {t₁ t₂ : TileSet ps ιₜ} :
    (t₁ : ιₜ → PlacedTile ps) = t₂ ↔ t₁ = t₂ :=
  TileSet.ext_iff.symm

/--
@isnad1 id=injectiv.0h5v.s5.9aabc842913a from=translated src=- shape=adfe3a9a vocab=b37b2bb7
-/
lemma coe_injective : Injective (TileSet.tiles : TileSet ps ιₜ → ιₜ → PlacedTile ps) :=
  fun _ _ ↦ coe_inj.1

/-- Coercion from a `TileSet` to a set of tiles (losing information about the presence of
duplicate tiles in the `TileSet`). Use the coercion rather than using `coeSet` directly. -/
@[coe] def coeSet (t : TileSet ps ιₜ) : Set (PlacedTile ps) := Set.range t

instance : CoeOut (TileSet ps ιₜ) (Set (PlacedTile ps)) where
  coe := coeSet

instance : Membership (PlacedTile ps) (TileSet ps ιₜ) where
  mem t pt := pt ∈ (t : Set (PlacedTile ps))

/--
@isnad1 id=iff.0h7v.s6.f5117f8738da from=translated src=- shape=5e77dd53 vocab=1bec05c4
-/
@[simp] lemma mem_coeSet {pt : PlacedTile ps} {t : TileSet ps ιₜ} :
    pt ∈ (t : Set (PlacedTile ps)) ↔ pt ∈ t :=
  Iff.rfl

/--
@isnad1 id=eq.0h6v.s6.e0e3b2652585 from=translated src=- shape=1372ab10 vocab=cb0f509a
-/
lemma coeSet_apply (t : TileSet ps ιₜ) : t = Set.range t := rfl

/--
@isnad1 id=iff.0h7v.s6.8411f9165a33 from=translated src=- shape=07af467b vocab=cb66e77a
-/
protected lemma mem_def {pt : PlacedTile ps} {t : TileSet ps ιₜ} : pt ∈ t ↔ ∃ i, t i = pt :=
  Iff.rfl

/--
@isnad1 id=mem.0h7v.s6.0a97d3acb87e from=translated src=- shape=36d97de7 vocab=cb66e77a
-/
lemma apply_mem (t : TileSet ps ιₜ) (i : ιₜ) : t i ∈ t := Set.mem_range_self i

/--
@isnad1 id=iff.0h7v.s6.c6d79f078183 from=translated src=- shape=e2f7aaac vocab=cb66e77a
-/
@[simp] lemma exists_mem_iff {t : TileSet ps ιₜ} {f : PlacedTile ps → Prop} :
    (∃ pt ∈ t, f pt) ↔ ∃ i, f (t i) := by
  simp_rw [← mem_coeSet, coeSet_apply, Set.exists_range_iff]

/--
@isnad1 id=iff.0h7v.s6.55807f57fa18 from=translated src=- shape=b6ef1a6e vocab=cb66e77a
-/
@[simp] lemma forall_mem_iff {t : TileSet ps ιₜ} {f : PlacedTile ps → Prop} :
    (∀ pt ∈ t, f pt) ↔ ∀ i, f (t i) := by
  simp_rw [← mem_coeSet, coeSet_apply, Set.forall_mem_range]

/--
@isnad1 id=eq.0h6v.s7.784142ebbb67 from=translated src=- shape=be9e30c0 vocab=eda1d42d
-/
lemma union_of_mem_eq_iUnion (t : TileSet ps ιₜ) : ⋃ pt ∈ t, (pt : Set X) = ⋃ i, (t i : Set X) := by
  ext x
  simp

/--
@isnad1 id=nonempty.1h7v.s6.e53a0f69170c from=translated src=- shape=4288c9df vocab=083c325e
-/
lemma nonempty_apply_of_forall_nonempty (t : TileSet ps ιₜ) (h : ∀ i, (ps i : Set X).Nonempty)
    (i : ιₜ) : (t i : Set X).Nonempty :=
  PlacedTile.coe_nonempty_iff.2 (h _)

/--
@isnad1 id=nonempty.2h7v.s6.843909ebeb56 from=translated src=- shape=d7bd8208 vocab=579dbbc1
-/
lemma nonempty_of_forall_nonempty (t : TileSet ps ιₜ) (h : ∀ i, (ps i : Set X).Nonempty)
    {pt : PlacedTile ps} (hpt : pt ∈ t) : (pt : Set X).Nonempty := by
  rcases hpt with ⟨i, rfl⟩
  exact t.nonempty_apply_of_forall_nonempty h _

/--
@isnad1 id=finite.1h7v.s6.f05afb814321 from=translated src=- shape=4288c9df vocab=9e8c8461
-/
lemma finite_apply_of_forall_finite (t : TileSet ps ιₜ) (h : ∀ i, (ps i : Set X).Finite) (i : ιₜ) :
    (t i : Set X).Finite :=
  PlacedTile.coe_finite_iff.2 (h _)

/--
@isnad1 id=finite.2h7v.s6.6791e0876e64 from=translated src=- shape=d7bd8208 vocab=c1a1f398
-/
lemma finite_of_forall_finite (t : TileSet ps ιₜ) (h : ∀ i, (ps i : Set X).Finite)
    {pt : PlacedTile ps} (hpt : pt ∈ t) : (pt : Set X).Finite := by
  rcases hpt with ⟨i, rfl⟩
  exact t.finite_apply_of_forall_finite h _

/-- Reindex a `TileSet` by composition with a function on index types (typically an equivalence
for it to literally be reindexing, though not required to be one in this definition). -/
def reindex (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) : TileSet ps ιₜ' where
  tiles := ↑t ∘ f

/--
@isnad1 id=eq.0h8v.s6.c0177e99f033 from=translated src=- shape=a88b2802 vocab=3f7960af
-/
@[simp] lemma coe_reindex (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) : t.reindex f = ↑t ∘ f := rfl

/--
@isnad1 id=eq.0h9v.s6.825c98293018 from=translated src=- shape=9ce3f1fd vocab=4d8713e3
-/
@[simp] lemma reindex_apply (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) (i : ιₜ') :
    t.reindex f i = t (f i) :=
  rfl

/--
@isnad1 id=eq.0h6v.s5.159190953b9d from=translated src=- shape=a4c1d3c3 vocab=19c21bed
-/
@[simp] lemma reindex_id (t : TileSet ps ιₜ) : t.reindex id = t := rfl

/--
@isnad1 id=iff.1h8v.s6.2a33c1c29bec from=translated src=- shape=a7ddf4d7 vocab=f2c071b9
-/
@[simp] lemma injective_reindex_iff_injective {t : TileSet ps ιₜ} {f : ιₜ' → ιₜ}
    (ht : Injective t) : Injective (↑t ∘ f) ↔ Injective f :=
  ht.of_comp_iff _

/--
@isnad1 id=injectiv.1h9v.s6.f85e8e64b934 from=translated src=- shape=8c18265d vocab=6ad962b7
-/
lemma injective_reindex_of_embeddingLike {t : TileSet ps ιₜ} (f : F) (ht : Injective t) :
    Injective (t.reindex f) :=
  (injective_reindex_iff_injective ht).2 <| EmbeddingLike.injective f

/--
@isnad1 id=eq.0h10v.s6.74727c3c269e from=translated src=- shape=d7a735fb vocab=1cfbac21
-/
@[simp] lemma reindex_reindex (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) (f' : ιₜ'' → ιₜ') :
    (t.reindex f).reindex f' = t.reindex (f ∘ f') :=
  rfl

/--
@isnad1 id=iff.1h9v.s6.e0e0a1358094 from=translated src=- shape=1260653a vocab=76f98365
-/
@[simp] lemma reindex_eq_reindex_iff_of_surjective {t₁ t₂ : TileSet ps ιₜ} {f : ιₜ' → ιₜ}
    (h : Surjective f) : t₁.reindex f = t₂.reindex f ↔ t₁ = t₂ := by
  refine ⟨fun he ↦ TileSet.ext <| funext <| h.forall.2 fun i ↦ ?_,
          fun he ↦ congrArg₂ _ he rfl⟩
  simp_rw [← reindex_apply, he]

/--
@isnad1 id=iff.0h10v.s6.bc38558f2323 from=translated src=- shape=7724253d vocab=7dbc9879
-/
@[simp] lemma reindex_eq_reindex_iff_of_equivLike {t₁ t₂ : TileSet ps ιₜ} (f : E) :
    t₁.reindex f = t₂.reindex f ↔ t₁ = t₂ :=
  reindex_eq_reindex_iff_of_surjective (EquivLike.surjective f)

/--
@isnad1 id=iff.1h12v.s7.1dae9bfb2130 from=translated src=- shape=61105e29 vocab=04ce7387
-/
@[simp] lemma reindex_comp_eq_reindex_comp_iff_of_surjective {t₁ t₂ : TileSet ps ιₜ}
    {f₁ f₂ : ιₜ' → ιₜ} {f : ιₜ'' → ιₜ'} (h : Surjective f) :
    t₁.reindex (f₁ ∘ f) = t₂.reindex (f₂ ∘ f) ↔ t₁.reindex f₁ = t₂.reindex f₂ := by
  rw [← reindex_reindex, ← reindex_reindex, reindex_eq_reindex_iff_of_surjective h]

/--
@isnad1 id=iff.0h13v.s7.e4cec7db2063 from=translated src=- shape=9e2a1ce8 vocab=1a707dd6
-/
@[simp] lemma reindex_comp_eq_reindex_comp_iff_of_equivLike {t₁ t₂ : TileSet ps ιₜ}
    {f₁ f₂ : ιₜ' → ιₜ} (f : E') :
    t₁.reindex (f₁ ∘ f) = t₂.reindex (f₂ ∘ f) ↔ t₁.reindex f₁ = t₂.reindex f₂ :=
  reindex_comp_eq_reindex_comp_iff_of_surjective (EquivLike.surjective f)

/--
@isnad1 id=iff.1h10v.s6.f68b247e19f7 from=translated src=- shape=db808dd7 vocab=04ce7387
-/
@[simp] lemma reindex_comp_eq_reindex_iff_of_surjective {t₁ t₂ : TileSet ps ιₜ} {f₁ : ιₜ → ιₜ}
    {f : ιₜ' → ιₜ} (h : Surjective f) :
    t₁.reindex (f₁ ∘ f) = t₂.reindex f ↔ t₁.reindex f₁ = t₂ := by
  rw [← reindex_reindex, reindex_eq_reindex_iff_of_surjective h]

/--
@isnad1 id=iff.0h11v.s7.a3ad8416c448 from=translated src=- shape=1c0b804b vocab=1a707dd6
-/
@[simp] lemma reindex_comp_eq_reindex_iff_of_equivLike {t₁ t₂ : TileSet ps ιₜ} {f₁ : ιₜ → ιₜ}
    (f : E) : t₁.reindex (f₁ ∘ f) = t₂.reindex f ↔ t₁.reindex f₁ = t₂ :=
  reindex_comp_eq_reindex_iff_of_surjective (EquivLike.surjective f)

/--
@isnad1 id=iff.1h10v.s6.b9f3cf1058da from=translated src=- shape=4f3705fc vocab=04ce7387
-/
@[simp] lemma reindex_eq_reindex_comp_iff_of_surjective {t₁ t₂ : TileSet ps ιₜ} {f₁ : ιₜ → ιₜ}
    {f : ιₜ' → ιₜ} (h : Surjective f) :
    t₁.reindex f = t₂.reindex (f₁ ∘ f) ↔ t₁ = t₂.reindex f₁ := by
  rw [← reindex_reindex, reindex_eq_reindex_iff_of_surjective h]

/--
@isnad1 id=iff.0h11v.s7.e74a262e0015 from=translated src=- shape=4e7032ab vocab=1a707dd6
-/
@[simp] lemma reindex_eq_reindex_comp_iff_of_equivLike {t₁ t₂ : TileSet ps ιₜ} {f₁ : ιₜ → ιₜ}
    (f : E) : t₁.reindex f = t₂.reindex (f₁ ∘ f) ↔ t₁ = t₂.reindex f₁ :=
  reindex_eq_reindex_comp_iff_of_surjective (EquivLike.surjective f)

/--
@isnad1 id=eq.0h8v.s6.ae8c7d6c10ec from=translated src=- shape=64ec84ee vocab=0037b89f
-/
lemma coeSet_reindex_eq_range_comp (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) :
    (t.reindex f : Set (PlacedTile ps)) = Set.range (t ∘ f) :=
  rfl

/--
@isnad1 id=le.0h8v.s6.373688ad3b26 from=translated src=- shape=d7fb8b52 vocab=dc5180e3
-/
lemma coeSet_reindex_subset (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) :
    (t.reindex f : Set (PlacedTile ps)) ⊆ t := Set.range_comp_subset_range f t

/--
@isnad1 id=mem.1h9v.s6.3d2a19ce3e1c from=translated src=- shape=76590e85 vocab=81dc4639
-/
lemma mem_of_mem_reindex {t : TileSet ps ιₜ} {f : ιₜ' → ιₜ} {pt : PlacedTile ps}
    (h : pt ∈ t.reindex f) : pt ∈ t :=
  Set.mem_of_mem_of_subset h <| t.coeSet_reindex_subset f

/--
@isnad1 id=iff.0h9v.s6.8e1999253ffa from=translated src=- shape=708e9796 vocab=cdc16578
-/
lemma mem_reindex_iff {t : TileSet ps ιₜ} {f : ιₜ' → ιₜ} {pt : PlacedTile ps} :
    pt ∈ (t.reindex f) ↔ ∃ i, t (f i) = pt :=
  Set.mem_range

/--
@isnad1 id=eq.1h8v.s6.1f2bb5bb0757 from=translated src=- shape=3fc3d2e6 vocab=452cd9c4
-/
@[simp] lemma coeSet_reindex_of_surjective (t : TileSet ps ιₜ) {f : ιₜ' → ιₜ} (h : Surjective f) :
    (t.reindex f : Set (PlacedTile ps)) = t :=
  h.range_comp _

/--
@isnad1 id=eq.0h9v.s6.ccd2c1a01fba from=translated src=- shape=f0cffe6a vocab=47637543
-/
@[simp] lemma coeSet_reindex_of_equivLike (t : TileSet ps ιₜ) (f : E) :
    (t.reindex f : Set (PlacedTile ps)) = t :=
  t.coeSet_reindex_of_surjective <| EquivLike.surjective f

/--
@isnad1 id=iff.1h9v.s6.f673e89a5fc8 from=translated src=- shape=25ee982d vocab=7f26c096
-/
@[simp] lemma mem_reindex_iff_of_surjective {t : TileSet ps ιₜ} {f : ιₜ' → ιₜ} {pt : PlacedTile ps}
    (h : Surjective f) : pt ∈ t.reindex f ↔ pt ∈ t :=
  iff_of_eq <| congrArg (pt ∈ ·) <| t.coeSet_reindex_of_surjective h

/--
@isnad1 id=iff.0h10v.s7.5694a98f8f4d from=translated src=- shape=b9dfddcc vocab=de404086
-/
@[simp] lemma mem_reindex_iff_of_equivLike {t : TileSet ps ιₜ} (f : E) {pt : PlacedTile ps} :
    pt ∈ t.reindex f ↔ pt ∈ t :=
  mem_reindex_iff_of_surjective <| EquivLike.surjective f

/-- If two `TileSet`s have the same set of tiles and no duplicate tiles, this equivalence maps
one index type to the other. -/
def equivOfCoeSetEqOfInjective {t₁ : TileSet ps ιₜ} {t₂ : TileSet ps ιₜ'}
    (h : (t₁ : Set (PlacedTile ps)) = t₂) (h₁ : Injective t₁) (h₂ : Injective t₂) : ιₜ' ≃ ιₜ :=
  ((Equiv.ofInjective t₂ h₂).trans (Equiv.cast (congrArg _ h.symm))).trans
    (Equiv.ofInjective t₁ h₁).symm

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.3h8v.s7.444a055bdf25 from=translated src=- shape=c65a67e4 vocab=c29e3ee1
-/
@[simp] lemma reindex_equivOfCoeSetEqOfInjective {t₁ : TileSet ps ιₜ} {t₂ : TileSet ps ιₜ'}
    (h : (t₁ : Set (PlacedTile ps)) = t₂) (h₁ : Injective t₁) (h₂ : Injective t₂) :
    t₁.reindex (equivOfCoeSetEqOfInjective h h₁ h₂) = t₂ := by
  ext i : 2
  simp only [equivOfCoeSetEqOfInjective, Equiv.coe_trans, reindex_apply, comp_apply,
    Equiv.ofInjective_apply, Equiv.cast_apply]
  erw [Equiv.apply_ofInjective_symm h₁]
  rw [Subtype.coe_eq_iff]
  simp_rw [coeSet_apply] at h
  refine ⟨h ▸ Set.mem_range_self _, ?_⟩
  rw [cast_eq_iff_heq, Subtype.heq_iff_coe_eq]
  simp [h]

instance : MulAction G (TileSet ps ιₜ) where
  smul g t := ⟨(g • ·) ∘ ↑t⟩
  one_smul _ := TileSet.ext <| funext <| fun _ ↦ one_smul _ _
  mul_smul _ _ _ := TileSet.ext <| funext <| fun _ ↦ mul_smul _ _ _

/--
@isnad1 id=eq.0h7v.s7.c392d60ddef0 from=translated src=- shape=9e0fabe0 vocab=dc9b251e
-/
lemma smul_coe (g : G) (t : TileSet ps ιₜ) : (g • t : TileSet ps ιₜ) = (g • ·) ∘ ↑t := rfl

/--
@isnad1 id=eq.0h8v.s7.faf4bd164a8b from=translated src=- shape=07cb35e4 vocab=b2b761a3
-/
lemma smul_apply (g : G) (t : TileSet ps ιₜ) (i : ιₜ) : (g • t) i = g • (t i) := rfl

/--
@isnad1 id=iff.0h9v.s7.7347a6d4fc21 from=translated src=- shape=98934393 vocab=7c0417bb
-/
@[simp] lemma smul_mem_smul_apply_iff (g : G) {x : X} {t : TileSet ps ιₜ} {i : ιₜ} :
    g • x ∈ (g • t) i ↔ x ∈ t i :=
  PlacedTile.smul_mem_smul_iff g

/--
@isnad1 id=iff.0h9v.s7.0e9003c9c485 from=translated src=- shape=a676b93b vocab=69d2a550
-/
lemma mem_smul_apply_iff_smul_inv_mem {g : G} {x : X} {t : TileSet ps ιₜ} {i : ιₜ} :
    x ∈ (g • t) i ↔ g⁻¹ • x ∈ t i :=
  PlacedTile.mem_smul_iff_smul_inv_mem

/--
@isnad1 id=iff.0h9v.s7.0c0e5f015b1b from=translated src=- shape=3189499f vocab=69d2a550
-/
lemma mem_inv_smul_apply_iff_smul_mem {g : G} {x : X} {t : TileSet ps ιₜ} {i : ιₜ} :
    x ∈ (g⁻¹ • t) i ↔ g • x ∈ t i :=
  PlacedTile.mem_inv_smul_iff_smul_mem

/--
@isnad1 id=eq.0h9v.s7.f6bf82a7a8fc from=translated src=- shape=842d2546 vocab=efc95d9b
-/
@[simp] lemma smul_reindex (g : G) (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) :
    g • (t.reindex f) = (g • t).reindex f :=
  rfl

/--
@isnad1 id=iff.0h7v.s7.45a1f4d114a0 from=translated src=- shape=d4340cc8 vocab=e9807267
-/
@[simp] lemma injective_smul_iff (g : G) {t : TileSet ps ιₜ} : Injective (g • t) ↔ Injective t :=
  Injective.of_comp_iff (MulAction.injective g) t

/--
@isnad1 id=eq.0h7v.s7.ef9aa3b6daf9 from=translated src=- shape=e0798478 vocab=1f4919e2
-/
@[simp] lemma coeSet_smul (g : G) (t : TileSet ps ιₜ) :
    (g • t : TileSet ps ιₜ) = g • (t : Set (PlacedTile ps)) := by
  simp [coeSet_apply, smul_coe, Set.range_comp]

/--
@isnad1 id=iff.0h8v.s7.d3379405d129 from=translated src=- shape=0fec122e vocab=63fc3e71
-/
@[simp] lemma smul_mem_smul_iff {pt : PlacedTile ps} (g : G) {t : TileSet ps ιₜ} :
    g • pt ∈ g • t ↔ pt ∈ t := by
  rw [← mem_coeSet, ← mem_coeSet, coeSet_smul, Set.smul_mem_smul_set_iff]

/--
@isnad1 id=iff.0h8v.s7.2a67b981b387 from=translated src=- shape=2d5e83d9 vocab=06005a56
-/
lemma mem_smul_iff_smul_inv_mem {pt : PlacedTile ps} {g : G} {t : TileSet ps ιₜ} :
    pt ∈ g • t ↔ g⁻¹ • pt ∈ t := by
  simp_rw [← mem_coeSet, coeSet_smul, Set.mem_smul_set_iff_inv_smul_mem]

/--
@isnad1 id=iff.0h8v.s7.19befeb8f5f0 from=translated src=- shape=c85781b3 vocab=06005a56
-/
lemma mem_inv_smul_iff_smul_mem {pt : PlacedTile ps} {g : G} {t : TileSet ps ιₜ} :
    pt ∈ g⁻¹ • t ↔ g • pt ∈ t := by
  simp_rw [← mem_coeSet, coeSet_smul, Set.mem_inv_smul_set_iff]

/--
@isnad1 id=eq.0h9v.s7.deebc35ade6b from=translated src=- shape=fea17fed vocab=784823c2
-/
@[simp] lemma smul_inter_smul (g : G) (t : TileSet ps ιₜ) (s : Set X) (i : ιₜ) :
    g • s ∩ (g • t) i = g • (s ∩ t i) := by
  simp [smul_apply, Set.smul_set_inter]

/-- The action of both a group element and a permutation of the index type on a `TileSet`, used
in defining the symmetry group. -/
instance : MulAction (G × Equiv.Perm ιₜ) (TileSet ps ιₜ) where
  smul g t := (g.fst • t).reindex g.snd.symm
  one_smul _ := TileSet.ext <| funext <| fun _ ↦ one_smul _ _
  mul_smul g h t := TileSet.ext <| funext <| fun i ↦ by
    change (g.1 * h.1) • t ((g.2 * h.2)⁻¹ i) = g.1 • h.1 • t (h.2⁻¹ (g.2⁻¹ i))
    simp [mul_smul]

/--
@isnad1 id=eq.0h8v.s8.43a8594052c4 from=translated src=- shape=00260388 vocab=004dc06c
-/
lemma smul_prod_eq_reindex (g : G) (f : Equiv.Perm ιₜ) (t : TileSet ps ιₜ) :
    (g, f) • t = (g • t).reindex f.symm :=
  rfl

/--
@isnad1 id=eq.0h9v.s7.e8df756fabfb from=translated src=- shape=acb4bbc9 vocab=3515f0b5
-/
lemma smul_prod_apply (g : G) (f : Equiv.Perm ιₜ) (t : TileSet ps ιₜ) (i : ιₜ) :
    ((g, f) • t) i = g • t (f.symm i) :=
  rfl

/--
@isnad1 id=eq.0h7v.s7.0a9368f09fee from=translated src=- shape=e77a9025 vocab=71d6aa34
-/
@[simp] lemma smul_prod_one (g : G) (t : TileSet ps ιₜ) : (g, (1 : Equiv.Perm ιₜ)) • t = g • t :=
  rfl

/--
@isnad1 id=eq.0h7v.s7.5ef8047cf6ef from=translated src=- shape=847ee5f5 vocab=fe2ed543
-/
@[simp] lemma smul_prod_refl (g : G) (t : TileSet ps ιₜ) :
    (g, (Equiv.refl ιₜ : Equiv.Perm ιₜ)) • t = g • t :=
  rfl

/-- The symmetry group of a `TileSet ps ιₜ` is the subgroup of `G` that preserves the tiles up to
permutation of the indices. -/
def symmetryGroup (t : TileSet ps ιₜ) : Subgroup G :=
  (MulAction.stabilizer (G × Equiv.Perm ιₜ) t).map (MonoidHom.fst _ _)

/-- A group element is in the symmetry group if and only if there is a permutation of the indices
such that mapping by the group element and that permutation preserves the `TileSet`.
@isnad1 id=iff.0h7v.s7.d252cad884c5 from=translated src=- shape=f703ba8d vocab=63cff0a5
-/
lemma mem_symmetryGroup_iff_exists {t : TileSet ps ιₜ} {g : G} :
    g ∈ t.symmetryGroup ↔ ∃ f : Equiv.Perm ιₜ, (g • t).reindex f = t := by
  simp_rw [symmetryGroup, Subgroup.mem_map, MulAction.mem_stabilizer_iff]
  change (∃ x : G × Equiv.Perm ιₜ, _ ∧ x.1 = g) ↔ _
  refine ⟨fun ⟨⟨g', f⟩, ⟨h, hg⟩⟩ ↦ ⟨f.symm, ?_⟩, fun ⟨f, h⟩ ↦ ⟨(g, f.symm), h, rfl⟩⟩
  dsimp only at hg
  subst hg
  exact h

/-- If `g` is in the symmetry group, the image of any tile under `g` is in `t`.
@isnad1 id=ex.1h8v.s7.2e2978926aac from=translated src=- shape=3f085432 vocab=906224d8
-/
lemma exists_smul_eq_of_mem_symmetryGroup {t : TileSet ps ιₜ} {g : G} (i : ιₜ)
    (hg : g ∈ t.symmetryGroup) : ∃ j, g • (t i) = t j := by
  rw [mem_symmetryGroup_iff_exists] at hg
  rcases hg with ⟨f, h⟩
  refine ⟨f.symm i, ?_⟩
  nth_rewrite 2 [← h]
  simp [TileSet.smul_apply]

/-- If `g` is in the symmetry group, every tile in `t` is the image under `g` of some tile in
`t`.
@isnad1 id=ex.1h8v.s7.51d2746d6545 from=translated src=- shape=1c7b25bd vocab=906224d8
-/
lemma exists_smul_eq_of_mem_symmetryGroup' {t : TileSet ps ιₜ} {g : G} (i : ιₜ)
    (hg : g ∈ t.symmetryGroup) : ∃ j, g • (t j) = t i := by
  rcases exists_smul_eq_of_mem_symmetryGroup i (inv_mem hg) with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  simp [← hj]

/-- If `g` is in the symmetry group, the image of any tile under `g` is in `t`.
@isnad1 id=mem.2h8v.s7.61eeec4f1241 from=translated src=- shape=81f36c10 vocab=8285c24f
-/
lemma smul_mem_of_mem_of_mem_symmetryGroup {t : TileSet ps ιₜ} {g : G} {pt : PlacedTile ps}
    (hg : g ∈ t.symmetryGroup) (hpt : pt ∈ t) : g • pt ∈ t := by
  rcases hpt with ⟨i, rfl⟩
  simp_rw [TileSet.mem_def, eq_comm]
  exact exists_smul_eq_of_mem_symmetryGroup i hg

/-- If `g` is in the symmetry group, every tile in `t` is the image under `g` of some tile in
`t`.
@isnad1 id=ex.2h8v.s7.1f67b635d9c5 from=translated src=- shape=b8a64427 vocab=8285c24f
-/
lemma exists_smul_eq_of_mem_of_mem_symmetryGroup {t : TileSet ps ιₜ} {g : G} {pt : PlacedTile ps}
    (hg : g ∈ t.symmetryGroup) (hpt : pt ∈ t) : ∃ pt' ∈ t, g • pt' = pt := by
  rcases hpt with ⟨i, rfl⟩
  rw [exists_mem_iff]
  exact exists_smul_eq_of_mem_symmetryGroup' i hg

/--
@isnad1 id=eq.0h6v.s5.ddede0dcbfa9 from=translated src=- shape=194da7d5 vocab=f1fffca1
-/
@[simp] lemma symmetryGroup_of_isEmpty [IsEmpty ιₜ] (t : TileSet ps ιₜ) : t.symmetryGroup = ⊤ := by
  ext g
  rw [mem_symmetryGroup_iff_exists]
  simp only [Subgroup.mem_top, iff_true]
  exact ⟨Equiv.refl _, Subsingleton.elim _ _⟩

/--
@isnad1 id=eq.0h9v.s6.fd7e35b41d98 from=translated src=- shape=f7d800e3 vocab=c987b89b
-/
@[simp] lemma symmetryGroup_reindex (t : TileSet ps ιₜ) (f : E) :
    (t.reindex f).symmetryGroup = t.symmetryGroup := by
  ext g
  simp_rw [mem_symmetryGroup_iff_exists]
  refine ⟨fun ⟨e, he⟩ ↦ ?_, fun ⟨e, he⟩ ↦ ?_⟩
  · refine ⟨((EquivLike.toEquiv f).symm.trans e).trans (EquivLike.toEquiv f), ?_⟩
    rw [← reindex_eq_reindex_iff_of_equivLike f, ← he]
    simp [comp_assoc]
  · refine ⟨((EquivLike.toEquiv f).trans e).trans (EquivLike.toEquiv f).symm, ?_⟩
    nth_rewrite 2 [← he]
    simp [← comp_assoc]

/--
@isnad1 id=eq.1h8v.s6.d11e2cd40194 from=translated src=- shape=43a98105 vocab=8485f580
-/
@[simp] lemma symmetryGroup_reindex_of_bijective (t : TileSet ps ιₜ) {f : ιₜ' → ιₜ}
    (h : Bijective f) : (t.reindex f).symmetryGroup = t.symmetryGroup :=
  t.symmetryGroup_reindex <| Equiv.ofBijective f h

/-- Mapping the `TileSet` by a group element acts on the symmetry group by conjugation.
@isnad1 id=eq.0h7v.s8.79cea5e39af2 from=translated src=- shape=c477f06c vocab=915bad58
-/
lemma symmetryGroup_smul (t : TileSet ps ιₜ) (g : G) :
    (g • t).symmetryGroup = (ConjAct.toConjAct g) • t.symmetryGroup := by
  simp_rw [← smul_prod_one, symmetryGroup, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  ext h
  simp only [Subgroup.mem_map, MulAction.mem_stabilizer_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, Prod.inv_mk, inv_one, Prod.exists, Prod.mk_mul_mk, one_mul, mul_one,
    MonoidHom.coe_fst, Prod.mk.injEq, exists_eq_right_right, exists_and_right, exists_eq_right,
    Subgroup.mem_smul_pointwise_iff_exists, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
  rw [exists_comm]
  convert Iff.rfl
  rw [exists_and_right]

/--
@isnad1 id=iff.0h8v.s7.7b24f684711e from=translated src=- shape=b1079e57 vocab=dd20d7e8
-/
lemma mem_symmetryGroup_smul_iff {t : TileSet ps ιₜ} (g : G) {g' : G} :
    g * g' * g⁻¹ ∈ (g • t).symmetryGroup ↔ g' ∈ t.symmetryGroup := by
  simp [symmetryGroup_smul, Subgroup.mem_smul_pointwise_iff_exists, ConjAct.smul_def]

/--
@isnad1 id=iff.0h8v.s7.5f83aa9e78f9 from=translated src=- shape=0265497c vocab=dd20d7e8
-/
lemma mem_symmetryGroup_smul_iff' {t : TileSet ps ιₜ} {g g' : G} :
    g' ∈ (g • t).symmetryGroup ↔ g⁻¹ * g' * g ∈ t.symmetryGroup := by
  convert mem_symmetryGroup_smul_iff g
  simp [mul_assoc]

/--
@isnad1 id=le.0h6v.s6.5d8503420908 from=translated src=- shape=7f933373 vocab=f20b2a3e
-/
lemma symmetryGroup_le_stabilizer_coeSet (t : TileSet ps ιₜ) :
    t.symmetryGroup ≤ MulAction.stabilizer G (t : Set (PlacedTile ps)) := by
  simp_rw [SetLike.le_def, mem_symmetryGroup_iff_exists, MulAction.mem_stabilizer_iff]
  rintro g ⟨f, hf⟩
  nth_rewrite 2 [← hf]
  simp

/--
@isnad1 id=eq.1h6v.s6.6da54d076273 from=translated src=- shape=dbccaa3c vocab=6308dcd1
-/
lemma symmetryGroup_eq_stabilizer_coeSet_of_injective (t : TileSet ps ιₜ) (h : Injective t) :
    t.symmetryGroup = MulAction.stabilizer G (t : Set (PlacedTile ps)) := by
  refine le_antisymm t.symmetryGroup_le_stabilizer_coeSet ?_
  simp_rw [SetLike.le_def, mem_symmetryGroup_iff_exists, MulAction.mem_stabilizer_iff]
  intro g hg
  rw [← coeSet_smul] at hg
  exact ⟨equivOfCoeSetEqOfInjective hg ((injective_smul_iff g).2 h) h, by simp⟩

/-- The disjoint union of two `TileSet`s, indexed by the sum of their index types. -/
protected def sum (t : TileSet ps ιₜ) (t' : TileSet ps ιₜ') : TileSet ps (ιₜ ⊕ ιₜ') where
  tiles := Sum.elim t.tiles t'.tiles

/--
@isnad1 id=eq.0h8v.s6.21112e45710b from=translated src=- shape=8d843300 vocab=6a15601a
-/
@[simp] lemma coe_sum (t : TileSet ps ιₜ) (t' : TileSet ps ιₜ') : t.sum t' = Sum.elim (↑t) (↑t') :=
  rfl

/--
@isnad1 id=eq.0h8v.s6.9b504daf9cf3 from=translated src=- shape=003268ec vocab=bff46a71
-/
@[simp] lemma coeSet_sum (t : TileSet ps ιₜ) (t' : TileSet ps ιₜ') :
    (t.sum t' : Set (PlacedTile ps)) = (↑t) ∪ (↑t') :=
  Set.Sum.elim_range _ _

/--
@isnad1 id=iff.0h9v.s7.a4cbe63de028 from=translated src=- shape=d683d0c4 vocab=50ccf343
-/
@[simp] lemma mem_sum {pt : PlacedTile ps} {t : TileSet ps ιₜ} {t' : TileSet ps ιₜ'} :
    pt ∈ t.sum t' ↔ pt ∈ t ∨ pt ∈ t' := by
  simp [← mem_coeSet]

/--
@isnad1 id=eq.0h12v.s7.9ea83611b6ed from=translated src=- shape=d45f60d8 vocab=20640e87
-/
lemma reindex_sum (t : TileSet ps ιₜ) (t' : TileSet ps ιₜ'') (f : ιₜ' → ιₜ) (f' : ιₜ''' → ιₜ'') :
    (t.sum t').reindex (Sum.map f f') = (t.reindex f).sum (t'.reindex f') :=
  TileSet.ext <| funext fun x ↦ Sum.recOn x (fun _ ↦ rfl) (fun _ ↦ rfl)

/--
@isnad1 id=eq.0h9v.s8.ab8b38f63d44 from=translated src=- shape=216daa33 vocab=0ed875a6
-/
lemma smul_sum (g : G) (t : TileSet ps ιₜ) (t' : TileSet ps ιₜ') :
    g • (t.sum t') = (g • t).sum (g • t') :=
  TileSet.ext <| funext fun x ↦ Sum.recOn x (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- The disjoint union of an indexed family of `TileSet`s, indexed by a sigma type. -/
protected def sigma (t : (i : ι) → TileSet ps (ιₜι i)) : TileSet ps (Σ i, ιₜι i) where
  tiles := Sigma.uncurry (fun i ↦ ↑(t i))

/--
@isnad1 id=eq.0h7v.s6.c5350f6ddeb3 from=translated src=- shape=b81acab2 vocab=bd2f7618
-/
@[simp] lemma coe_sigma (t : (i : ι) → TileSet ps (ιₜι i)) :
    TileSet.sigma t = Sigma.uncurry (fun i ↦ ↑(t i)) :=
  rfl

/--
@isnad1 id=eq.0h7v.s6.87d9c0fa9d4e from=translated src=- shape=ad589522 vocab=774dd739
-/
@[simp] lemma coeSet_sigma (t : (i : ι) → TileSet ps (ιₜι i)) :
    (TileSet.sigma t : Set (PlacedTile ps)) = ⋃ i, (t i : Set (PlacedTile ps)) :=
  Set.range_sigma_eq_iUnion_range _

/--
@isnad1 id=iff.0h8v.s7.ab49ddfedacb from=translated src=- shape=993b61ea vocab=0245762a
-/
lemma mem_sigma {pt : PlacedTile ps} {t : (i : ι) → TileSet ps (ιₜι i)} :
    pt ∈ TileSet.sigma t ↔ ∃ i, pt ∈ t i := by
  simp [← mem_coeSet]

/--
@isnad1 id=eq.0h9v.s7.1d6efb232171 from=translated src=- shape=d0715406 vocab=fbb0bd97
-/
lemma reindex_sigma (t : (i : ι) → TileSet ps (ιₜι i)) (f : (i : ι) → (ιₜ'ι i) → (ιₜι i)) :
    (TileSet.sigma t).reindex (Sigma.map id f) = TileSet.sigma fun i ↦ (t i).reindex (f i) :=
  rfl

/--
@isnad1 id=eq.0h8v.s8.61bc16d75387 from=translated src=- shape=0c773d5b vocab=71f23ed4
-/
lemma smul_sigma (g : G) (t : (i : ι) → TileSet ps (ιₜι i)) :
    g • TileSet.sigma t = TileSet.sigma (g • t) :=
  rfl

end TileSet

end DiscreteTiling

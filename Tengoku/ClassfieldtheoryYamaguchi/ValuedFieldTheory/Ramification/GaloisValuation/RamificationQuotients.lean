/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.GroupTheory.QuotientGroup.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Named quotients of antitone normal-subgroup filtrations

This module owns the opaque quotient carriers of a lower ramification
filtration and their construction, elimination, lifting, and mapping API.
Arithmetic Herbrand functions and valuation-action specializations live in
`RamificationTheory.GaloisValuation.Ramification`.
-/

noncomputable section

universe u v

namespace RamificationTheory
namespace DiscreteValuationField

/-- A generic antitone filtration by normal subgroups.  This interface contains
only the group-theoretic laws; arithmetic lower ramification filtrations are
canonical values constructed from valued extensions.-/
structure AntitoneNormalSubgroupFiltration (G : Type u) [Group G] where
  /-- The subgroup at each lower-filtration index.-/
  lower : ℕ → Subgroup G
  /-- Every subgroup in the lower filtration is normal.-/
  lower_normal : ∀ n : ℕ, (lower n).Normal
  /-- The lower filtration decreases as its index increases.-/
  antitone : ∀ {m n : ℕ}, m ≤ n → lower n ≤ lower m

namespace AntitoneNormalSubgroupFiltration

variable {G : Type u} [Group G] (F : AntitoneNormalSubgroupFiltration G)

/-- Provides the instance `lower_normal_instance`.
@isnad1 id=normal.0h3v.s4.7ac4f5ce6774 from=translated src=- shape=1f30a21f vocab=a183910e
-/
instance lower_normal_instance (n : ℕ) : (F.lower n).Normal :=
  F.lower_normal n

/-- The quotient by the `n`th lower ramification group.-/
def quotient (n : ℕ) : Type u :=
  G ⧸ F.lower n

/-- The subquotient `G_m / G_n`, used for ramification graded pieces when
`m ≤ n`.  The type is available for all `m,n`; under `m ≤ n`, `G_n` is a
subgroup of `G_m` by antitonicity.-/
def subquotient (m n : ℕ) : Type u :=
  F.lower m ⧸ (F.lower n).subgroupOf (F.lower m)

/-- The lower ramification graded piece `G_n/G_{n+1}`.-/
def gradedPiece (n : ℕ) : Type u :=
  F.subquotient n (n + 1)

/-- The inertia subgroup `G_0` of a lower ramification filtration.-/
abbrev inertiaSubgroup : Subgroup G :=
  F.lower 0

/-- States the theorem `lower_zero_eq_inertiaSubgroup`.
@isnad1 id=eq.0h2v.s4.cc77f8050042 from=translated src=- shape=85bd6e34 vocab=9d8c25b9
-/
theorem lower_zero_eq_inertiaSubgroup :
    F.lower 0 = F.inertiaSubgroup :=
  rfl

/-- The wild inertia subgroup `G_1` of a lower ramification filtration.-/
abbrev wildInertiaSubgroup : Subgroup G :=
  F.lower 1

/-- The tame quotient `G_0/G_1`.-/
def tameQuotient : Type u :=
  F.gradedPiece 0

/-- Provides the instance `inertiaSubgroup_normal`.
@isnad1 id=normal.0h2v.s4.871ec80ff474 from=translated src=- shape=ed10201d vocab=34e9ee18
-/
instance inertiaSubgroup_normal : F.inertiaSubgroup.Normal := by
  change (F.lower 0).Normal
  infer_instance

/-- Provides the instance `wildInertiaSubgroup_normal`.
@isnad1 id=normal.0h2v.s4.3d70f121b888 from=translated src=- shape=ed10201d vocab=6d0d824c
-/
instance wildInertiaSubgroup_normal : F.wildInertiaSubgroup.Normal := by
  change (F.lower 1).Normal
  infer_instance

/-- States the theorem `wildInertiaSubgroup_le_inertiaSubgroup`.
@isnad1 id=le.0h2v.s5.87a51235830d from=translated src=- shape=a5e9b6d0 vocab=2cbd3a72
-/
theorem wildInertiaSubgroup_le_inertiaSubgroup :
    F.wildInertiaSubgroup ≤ F.inertiaSubgroup :=
  F.antitone (Nat.zero_le 1)

/-- Provides the instance `wildInertiaSubgroup_subgroupOf_inertiaSubgroup_normal`.
@isnad1 id=normal.0h2v.s5.2ede047aa5c6 from=translated src=- shape=3a28a134 vocab=c5d6ba21
-/
instance wildInertiaSubgroup_subgroupOf_inertiaSubgroup_normal :
    ((F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup).Normal := by
  change ((F.lower 1).subgroupOf (F.lower 0)).Normal
  infer_instance

/-! ### Named quotient boundaries

The four ramification quotient carriers are opaque public objects.  Raw
`QuotientGroup` presentations occur only in the concrete equivalences and in
the implementation of the operations below. -/

/-- Provides the instance `quotientGroup`.-/
instance quotientGroup (n : ℕ) : Group (F.quotient n) := by
  change Group (G ⧸ F.lower n)
  infer_instance

/-- Provides the instance `subquotientGroup`.-/
instance subquotientGroup (m n : ℕ) : Group (F.subquotient m n) := by
  change Group
    (F.lower m ⧸ (F.lower n).subgroupOf (F.lower m))
  infer_instance

/-- Provides the instance `gradedPieceGroup`.-/
instance gradedPieceGroup (n : ℕ) : Group (F.gradedPiece n) := by
  change Group
    (F.lower n ⧸
      (F.lower (n + 1)).subgroupOf (F.lower n))
  infer_instance

/-- Provides the instance `tameQuotientGroup`.-/
instance tameQuotientGroup : Group F.tameQuotient := by
  change Group
    (F.inertiaSubgroup ⧸
      (F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup)
  infer_instance

/-- Concrete presentation of `G/G_n`.-/
def quotientConcreteMulEquiv (n : ℕ) :
    F.quotient n ≃* G ⧸ F.lower n :=
  MulEquiv.refl _

/-- Concrete presentation of `G_m/G_n`.-/
def subquotientConcreteMulEquiv (m n : ℕ) :
    F.subquotient m n ≃*
      F.lower m ⧸ (F.lower n).subgroupOf (F.lower m) :=
  MulEquiv.refl _

/-- The graded piece as its adjacent named subquotient.-/
def gradedPieceEquivSubquotient (n : ℕ) :
    F.gradedPiece n ≃* F.subquotient n (n + 1) :=
  MulEquiv.refl _

/-- Concrete presentation of `G_n/G_{n+1}`.-/
def gradedPieceConcreteMulEquiv (n : ℕ) :
    F.gradedPiece n ≃*
      F.lower n ⧸ (F.lower (n + 1)).subgroupOf (F.lower n) :=
  (F.gradedPieceEquivSubquotient n).trans
    (F.subquotientConcreteMulEquiv n (n + 1))

/-- The tame quotient as the zeroth named graded piece.-/
def tameQuotientEquivGradedPiece :
    F.tameQuotient ≃* F.gradedPiece 0 :=
  MulEquiv.refl _

/-- Concrete presentation of `G_0/G_1`.-/
def tameQuotientConcreteMulEquiv :
    F.tameQuotient ≃*
      F.inertiaSubgroup ⧸
        (F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup :=
  (F.tameQuotientEquivGradedPiece).trans
    (F.gradedPieceConcreteMulEquiv 0)

/-- Canonical projection to `G/G_n`.-/
def quotientMk (n : ℕ) : G →* F.quotient n :=
  (F.quotientConcreteMulEquiv n).symm.toMonoidHom.comp
    (QuotientGroup.mk' (F.lower n))

/-- States the theorem `quotientMk_apply`.
@isnad1 id=eq.0h4v.s9.cf9e93f160fb from=translated src=- shape=29f8b68e vocab=b759e443
-/
@[simp]
theorem quotientMk_apply (n : ℕ) (σ : G) :
    F.quotientConcreteMulEquiv n (F.quotientMk n σ) =
      QuotientGroup.mk' (F.lower n) σ :=
  rfl

/-- States the theorem `quotientMk_eq_one_iff`.
@isnad1 id=iff.0h4v.s7.55857dc0041d from=translated src=- shape=78d0c826 vocab=f9f8ab57
-/
@[simp]
theorem quotientMk_eq_one_iff (n : ℕ) (σ : G) :
    F.quotientMk n σ = 1 ↔ σ ∈ F.lower n := by
  constructor
  · intro h
    have h' := congrArg (F.quotientConcreteMulEquiv n) h
    rw [F.quotientMk_apply, map_one] at h'
    exact (QuotientGroup.eq_one_iff σ).1 h'
  · intro h
    apply (F.quotientConcreteMulEquiv n).injective
    rw [F.quotientMk_apply, map_one]
    exact (QuotientGroup.eq_one_iff σ).2 h

/-- States the theorem `quotientMk_eq_iff`.
@isnad1 id=iff.0h5v.s8.e77177bb23c1 from=translated src=- shape=6f6f88b7 vocab=549a3341
-/
@[simp]
theorem quotientMk_eq_iff (n : ℕ) (σ τ : G) :
    F.quotientMk n σ = F.quotientMk n τ ↔ σ / τ ∈ F.lower n := by
  constructor
  · intro h
    have h' := congrArg (F.quotientConcreteMulEquiv n) h
    rw [F.quotientMk_apply, F.quotientMk_apply] at h'
    exact QuotientGroup.eq_iff_div_mem.mp h'
  · intro h
    apply (F.quotientConcreteMulEquiv n).injective
    rw [F.quotientMk_apply, F.quotientMk_apply]
    exact QuotientGroup.eq_iff_div_mem.mpr h

/-- Eliminate a named ramification quotient through canonical
representatives.
@isnad1 id=var.0h6v.s7.ad7c476e1e93 from=translated src=- shape=1e6d6a1b vocab=09a87c99
-/
protected theorem quotient_inductionOn (n : ℕ)
    {motive : F.quotient n → Prop} (q : F.quotient n)
    (h : ∀ σ : G, motive (F.quotientMk n σ)) :
    motive q := by
  obtain ⟨σ, rfl⟩ :=
    ((F.quotientConcreteMulEquiv n).symm.surjective.comp
      (QuotientGroup.mk'_surjective (F.lower n))) q
  exact h σ

/-- Descend a homomorphism that kills the `n`th lower group.-/
def quotientLift {H : Type v} [Group H] (n : ℕ)
    (f : G →* H) (h : F.lower n ≤ f.ker) :
    F.quotient n →* H :=
  (QuotientGroup.lift (F.lower n) f h).comp
    (F.quotientConcreteMulEquiv n).toMonoidHom

/-- States the theorem `quotientLift_mk`.
@isnad1 id=eq.1h6v.s8.09d62c8e5484 from=translated src=- shape=d0902b7e vocab=4d340ebf
-/
@[simp]
theorem quotientLift_mk {H : Type v} [Group H] (n : ℕ)
    (f : G →* H) (h : F.lower n ≤ f.ker) (σ : G) :
    F.quotientLift n f h (F.quotientMk n σ) = f σ :=
  rfl

/-- Map between named ramification quotients induced by a group
homomorphism.-/
def quotientMap {H : Type v} [Group H]
    (E : AntitoneNormalSubgroupFiltration H) (n m : ℕ)
    (f : G →* H)
    (h : ∀ σ : G, σ ∈ F.lower n → f σ ∈ E.lower m) :
    F.quotient n →* E.quotient m :=
  F.quotientLift n ((E.quotientMk m).comp f) (by
    intro σ hσ
    rw [MonoidHom.mem_ker]
    exact (E.quotientMk_eq_one_iff m (f σ)).2 (h σ hσ))

/-- States the theorem `quotientMap_apply_mk`.
@isnad1 id=eq.1h8v.s9.e474b83fa52e from=translated src=- shape=14d25cfc vocab=e5d4b60b
-/
@[simp]
theorem quotientMap_apply_mk {H : Type v} [Group H]
    (E : AntitoneNormalSubgroupFiltration H) (n m : ℕ)
    (f : G →* H)
    (h : ∀ σ : G, σ ∈ F.lower n → f σ ∈ E.lower m) (σ : G) :
    F.quotientMap E n m f h (F.quotientMk n σ) =
      E.quotientMk m (f σ) :=
  rfl

/-- Canonical projection to `G_m/G_n`.-/
def subquotientMk (m n : ℕ) : F.lower m →* F.subquotient m n :=
  (F.subquotientConcreteMulEquiv m n).symm.toMonoidHom.comp
    (QuotientGroup.mk' ((F.lower n).subgroupOf (F.lower m)))

/-- States the theorem `subquotientMk_apply`.
@isnad1 id=eq.0h5v.s12.55ca490de82f from=translated src=- shape=a2908b7a vocab=45f9ca75
-/
@[simp]
theorem subquotientMk_apply (m n : ℕ) (σ : F.lower m) :
    F.subquotientConcreteMulEquiv m n (F.subquotientMk m n σ) =
      QuotientGroup.mk' ((F.lower n).subgroupOf (F.lower m)) σ :=
  rfl

/-- States the theorem `subquotientMk_eq_one_iff`.
@isnad1 id=iff.0h5v.s9.62a69fa68821 from=translated src=- shape=a2fbc530 vocab=3eeb2b58
-/
@[simp]
theorem subquotientMk_eq_one_iff (m n : ℕ) (σ : F.lower m) :
    F.subquotientMk m n σ = 1 ↔ (σ : G) ∈ F.lower n := by
  constructor
  · intro h
    have h' := congrArg (F.subquotientConcreteMulEquiv m n) h
    rw [F.subquotientMk_apply, map_one] at h'
    simpa [Subgroup.mem_subgroupOf] using
      ((QuotientGroup.eq_one_iff
        (N := (F.lower n).subgroupOf (F.lower m)) σ).1 h')
  · intro h
    apply (F.subquotientConcreteMulEquiv m n).injective
    rw [F.subquotientMk_apply, map_one]
    apply (QuotientGroup.eq_one_iff
      (N := (F.lower n).subgroupOf (F.lower m)) σ).2
    simpa [Subgroup.mem_subgroupOf] using h

/-- States the theorem `subquotientMk_eq_iff`.
@isnad1 id=iff.0h6v.s9.e9a68ddae91e from=translated src=- shape=51deba71 vocab=6b5ba6c5
-/
@[simp]
theorem subquotientMk_eq_iff (m n : ℕ) (σ τ : F.lower m) :
    F.subquotientMk m n σ = F.subquotientMk m n τ ↔
      ((σ / τ : F.lower m) : G) ∈ F.lower n := by
  constructor
  · intro h
    have h' := congrArg (F.subquotientConcreteMulEquiv m n) h
    rw [F.subquotientMk_apply, F.subquotientMk_apply] at h'
    simpa [Subgroup.mem_subgroupOf] using
      ((QuotientGroup.eq_iff_div_mem
        (N := (F.lower n).subgroupOf (F.lower m))
        (x := σ) (y := τ)).1 h')
  · intro h
    apply (F.subquotientConcreteMulEquiv m n).injective
    rw [F.subquotientMk_apply, F.subquotientMk_apply]
    apply (QuotientGroup.eq_iff_div_mem
      (N := (F.lower n).subgroupOf (F.lower m))
      (x := σ) (y := τ)).2
    simpa [Subgroup.mem_subgroupOf] using h

/-- Eliminate a named ramification subquotient.
@isnad1 id=var.0h7v.s8.5b4814612025 from=translated src=- shape=46eca992 vocab=7bbd8a2a
-/
protected theorem subquotient_inductionOn (m n : ℕ)
    {motive : F.subquotient m n → Prop} (q : F.subquotient m n)
    (h : ∀ σ : F.lower m, motive (F.subquotientMk m n σ)) :
    motive q := by
  obtain ⟨σ, rfl⟩ :=
    ((F.subquotientConcreteMulEquiv m n).symm.surjective.comp
      (QuotientGroup.mk'_surjective
        ((F.lower n).subgroupOf (F.lower m)))) q
  exact h σ

/-- Descend a homomorphism from `G_m` that kills the copy of `G_n`.-/
def subquotientLift {H : Type v} [Group H] (m n : ℕ)
    (f : F.lower m →* H)
    (h : (F.lower n).subgroupOf (F.lower m) ≤ f.ker) :
    F.subquotient m n →* H :=
  (QuotientGroup.lift
    ((F.lower n).subgroupOf (F.lower m)) f h).comp
      (F.subquotientConcreteMulEquiv m n).toMonoidHom

/-- States the theorem `subquotientLift_mk`.
@isnad1 id=eq.1h7v.s10.cdadd55a7739 from=translated src=- shape=147bbaf5 vocab=44e1fa5e
-/
@[simp]
theorem subquotientLift_mk {H : Type v} [Group H] (m n : ℕ)
    (f : F.lower m →* H)
    (h : (F.lower n).subgroupOf (F.lower m) ≤ f.ker)
    (σ : F.lower m) :
    F.subquotientLift m n f h (F.subquotientMk m n σ) = f σ :=
  rfl

/-- Map between named subquotients induced by a homomorphism of their upper
groups which sends the lower relation into the target lower group.-/
def subquotientMap {H : Type v} [Group H]
    (E : AntitoneNormalSubgroupFiltration H)
    (m n p q : ℕ) (f : F.lower m →* E.lower p)
    (h : ∀ σ : F.lower m, (σ : G) ∈ F.lower n →
      ((f σ : E.lower p) : H) ∈ E.lower q) :
    F.subquotient m n →* E.subquotient p q :=
  F.subquotientLift m n ((E.subquotientMk p q).comp f) (by
    intro σ hσ
    rw [MonoidHom.mem_ker]
    exact (E.subquotientMk_eq_one_iff p q (f σ)).2 (h σ hσ))

/-- States the theorem `subquotientMap_apply_mk`.
@isnad1 id=eq.1h10v.s11.487b5d005d56 from=translated src=- shape=d2b7ca3a vocab=fe2865ee
-/
@[simp]
theorem subquotientMap_apply_mk {H : Type v} [Group H]
    (E : AntitoneNormalSubgroupFiltration H)
    (m n p q : ℕ) (f : F.lower m →* E.lower p)
    (h : ∀ σ : F.lower m, (σ : G) ∈ F.lower n →
      ((f σ : E.lower p) : H) ∈ E.lower q)
    (σ : F.lower m) :
    F.subquotientMap E m n p q f h (F.subquotientMk m n σ) =
      E.subquotientMk p q (f σ) :=
  rfl

/-- Canonical projection to `G_n/G_{n+1}`.-/
def gradedPieceMk (n : ℕ) : F.lower n →* F.gradedPiece n :=
  (F.gradedPieceConcreteMulEquiv n).symm.toMonoidHom.comp
    (QuotientGroup.mk'
      ((F.lower (n + 1)).subgroupOf (F.lower n)))

/-- States the theorem `gradedPieceMk_apply`.
@isnad1 id=eq.0h4v.s12.14387b260ccb from=translated src=- shape=b7f560dc vocab=250edc5c
-/
@[simp]
theorem gradedPieceMk_apply (n : ℕ) (σ : F.lower n) :
    F.gradedPieceConcreteMulEquiv n (F.gradedPieceMk n σ) =
      QuotientGroup.mk'
        ((F.lower (n + 1)).subgroupOf (F.lower n)) σ :=
  rfl

/-- States the theorem `gradedPieceMk_eq_one_iff`.
@isnad1 id=iff.0h4v.s9.49ee21e916bf from=translated src=- shape=8aa18d90 vocab=dff88081
-/
@[simp]
theorem gradedPieceMk_eq_one_iff (n : ℕ) (σ : F.lower n) :
    F.gradedPieceMk n σ = 1 ↔ (σ : G) ∈ F.lower (n + 1) := by
  constructor
  · intro h
    have h' := congrArg (F.gradedPieceConcreteMulEquiv n) h
    rw [F.gradedPieceMk_apply, map_one] at h'
    simpa [Subgroup.mem_subgroupOf] using
      ((QuotientGroup.eq_one_iff
        (N := (F.lower (n + 1)).subgroupOf (F.lower n)) σ).1 h')
  · intro h
    apply (F.gradedPieceConcreteMulEquiv n).injective
    rw [F.gradedPieceMk_apply, map_one]
    apply (QuotientGroup.eq_one_iff
      (N := (F.lower (n + 1)).subgroupOf (F.lower n)) σ).2
    simpa [Subgroup.mem_subgroupOf] using h

/-- States the theorem `gradedPieceMk_eq_iff`.
@isnad1 id=iff.0h5v.s9.c8e85f8393d0 from=translated src=- shape=b47d4903 vocab=59308e26
-/
@[simp]
theorem gradedPieceMk_eq_iff (n : ℕ) (σ τ : F.lower n) :
    F.gradedPieceMk n σ = F.gradedPieceMk n τ ↔
      ((σ / τ : F.lower n) : G) ∈ F.lower (n + 1) := by
  constructor
  · intro h
    have h' := congrArg (F.gradedPieceConcreteMulEquiv n) h
    rw [F.gradedPieceMk_apply, F.gradedPieceMk_apply] at h'
    simpa [Subgroup.mem_subgroupOf] using
      ((QuotientGroup.eq_iff_div_mem
        (N := (F.lower (n + 1)).subgroupOf (F.lower n))
        (x := σ) (y := τ)).1 h')
  · intro h
    apply (F.gradedPieceConcreteMulEquiv n).injective
    rw [F.gradedPieceMk_apply, F.gradedPieceMk_apply]
    apply (QuotientGroup.eq_iff_div_mem
      (N := (F.lower (n + 1)).subgroupOf (F.lower n))
      (x := σ) (y := τ)).2
    simpa [Subgroup.mem_subgroupOf] using h

/-- Eliminate a named graded piece.
@isnad1 id=var.0h6v.s8.f59a571a607f from=translated src=- shape=b6975401 vocab=e0b3a2ae
-/
protected theorem gradedPiece_inductionOn (n : ℕ)
    {motive : F.gradedPiece n → Prop} (q : F.gradedPiece n)
    (h : ∀ σ : F.lower n, motive (F.gradedPieceMk n σ)) :
    motive q := by
  obtain ⟨σ, rfl⟩ :=
    ((F.gradedPieceConcreteMulEquiv n).symm.surjective.comp
      (QuotientGroup.mk'_surjective
        ((F.lower (n + 1)).subgroupOf (F.lower n)))) q
  exact h σ

/-- Descend a homomorphism from `G_n` that kills `G_{n+1}`.-/
def gradedPieceLift {H : Type v} [Group H] (n : ℕ)
    (f : F.lower n →* H)
    (h : (F.lower (n + 1)).subgroupOf (F.lower n) ≤ f.ker) :
    F.gradedPiece n →* H :=
  (QuotientGroup.lift
    ((F.lower (n + 1)).subgroupOf (F.lower n)) f h).comp
      (F.gradedPieceConcreteMulEquiv n).toMonoidHom

/-- States the theorem `gradedPieceLift_mk`.
@isnad1 id=eq.1h6v.s10.891f15b81a4d from=translated src=- shape=05c9e010 vocab=6ed2089c
-/
@[simp]
theorem gradedPieceLift_mk {H : Type v} [Group H] (n : ℕ)
    (f : F.lower n →* H)
    (h : (F.lower (n + 1)).subgroupOf (F.lower n) ≤ f.ker)
    (σ : F.lower n) :
    F.gradedPieceLift n f h (F.gradedPieceMk n σ) = f σ :=
  rfl

/-- Map between named graded pieces.-/
def gradedPieceMap {H : Type v} [Group H]
    (E : AntitoneNormalSubgroupFiltration H) (n m : ℕ)
    (f : F.lower n →* E.lower m)
    (h : ∀ σ : F.lower n, (σ : G) ∈ F.lower (n + 1) →
      ((f σ : E.lower m) : H) ∈ E.lower (m + 1)) :
    F.gradedPiece n →* E.gradedPiece m :=
  F.gradedPieceLift n ((E.gradedPieceMk m).comp f) (by
    intro σ hσ
    rw [MonoidHom.mem_ker]
    exact (E.gradedPieceMk_eq_one_iff m (f σ)).2 (h σ hσ))

/-- States the theorem `gradedPieceMap_apply_mk`.
@isnad1 id=eq.1h8v.s11.853aeb228769 from=translated src=- shape=ca988fb5 vocab=4e887558
-/
@[simp]
theorem gradedPieceMap_apply_mk {H : Type v} [Group H]
    (E : AntitoneNormalSubgroupFiltration H) (n m : ℕ)
    (f : F.lower n →* E.lower m)
    (h : ∀ σ : F.lower n, (σ : G) ∈ F.lower (n + 1) →
      ((f σ : E.lower m) : H) ∈ E.lower (m + 1))
    (σ : F.lower n) :
    F.gradedPieceMap E n m f h (F.gradedPieceMk n σ) =
      E.gradedPieceMk m (f σ) :=
  rfl

/-- Canonical projection to `G_0/G_1`.-/
def tameQuotientMk : F.inertiaSubgroup →* F.tameQuotient :=
  F.tameQuotientConcreteMulEquiv.symm.toMonoidHom.comp
    (QuotientGroup.mk'
      ((F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup))

/-- States the theorem `tameQuotientMk_apply`.
@isnad1 id=eq.0h3v.s11.eaf37c6c0f4c from=translated src=- shape=382c1fa2 vocab=9ddccb2d
-/
@[simp]
theorem tameQuotientMk_apply (σ : F.inertiaSubgroup) :
    F.tameQuotientConcreteMulEquiv (F.tameQuotientMk σ) =
      QuotientGroup.mk'
        ((F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup) σ :=
  rfl

/-- States the theorem `tameQuotientMk_eq_one_iff`.
@isnad1 id=iff.0h3v.s8.1dfa8a10ccc1 from=translated src=- shape=50c99bc8 vocab=4c9b6fef
-/
@[simp]
theorem tameQuotientMk_eq_one_iff (σ : F.inertiaSubgroup) :
    F.tameQuotientMk σ = 1 ↔ (σ : G) ∈ F.wildInertiaSubgroup := by
  constructor
  · intro h
    have h' := congrArg F.tameQuotientConcreteMulEquiv h
    rw [F.tameQuotientMk_apply, map_one] at h'
    simpa [Subgroup.mem_subgroupOf] using
      ((QuotientGroup.eq_one_iff
        (N := (F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup) σ).1 h')
  · intro h
    apply F.tameQuotientConcreteMulEquiv.injective
    rw [F.tameQuotientMk_apply, map_one]
    apply (QuotientGroup.eq_one_iff
      (N := (F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup) σ).2
    simpa [Subgroup.mem_subgroupOf] using h

/-- States the theorem `tameQuotientMk_eq_iff`.
@isnad1 id=iff.0h4v.s9.68e55149b30a from=translated src=- shape=3a617c18 vocab=a4915a7c
-/
@[simp]
theorem tameQuotientMk_eq_iff (σ τ : F.inertiaSubgroup) :
    F.tameQuotientMk σ = F.tameQuotientMk τ ↔
      ((σ / τ : F.inertiaSubgroup) : G) ∈ F.wildInertiaSubgroup := by
  constructor
  · intro h
    have h' := congrArg F.tameQuotientConcreteMulEquiv h
    rw [F.tameQuotientMk_apply, F.tameQuotientMk_apply] at h'
    simpa [Subgroup.mem_subgroupOf] using
      ((QuotientGroup.eq_iff_div_mem
        (N := (F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup)
        (x := σ) (y := τ)).1 h')
  · intro h
    apply F.tameQuotientConcreteMulEquiv.injective
    rw [F.tameQuotientMk_apply, F.tameQuotientMk_apply]
    apply (QuotientGroup.eq_iff_div_mem
      (N := (F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup)
      (x := σ) (y := τ)).2
    simpa [Subgroup.mem_subgroupOf] using h

/-- Eliminate the named tame quotient.
@isnad1 id=var.0h5v.s8.f663689b4113 from=translated src=- shape=33303487 vocab=1157bd68
-/
protected theorem tameQuotient_inductionOn
    {motive : F.tameQuotient → Prop} (q : F.tameQuotient)
    (h : ∀ σ : F.inertiaSubgroup, motive (F.tameQuotientMk σ)) :
    motive q := by
  obtain ⟨σ, rfl⟩ :=
    (F.tameQuotientConcreteMulEquiv.symm.surjective.comp
      (QuotientGroup.mk'_surjective
        ((F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup))) q
  exact h σ

/-- Descend an inertia homomorphism which kills wild inertia.-/
def tameQuotientLift {H : Type v} [Group H]
    (f : F.inertiaSubgroup →* H)
    (h : (F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup ≤ f.ker) :
    F.tameQuotient →* H :=
  (QuotientGroup.lift
    ((F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup) f h).comp
      F.tameQuotientConcreteMulEquiv.toMonoidHom

/-- States the theorem `tameQuotientLift_mk`.
@isnad1 id=eq.1h5v.s10.ecf3ed5c4fe7 from=translated src=- shape=57660744 vocab=945c1e46
-/
@[simp]
theorem tameQuotientLift_mk {H : Type v} [Group H]
    (f : F.inertiaSubgroup →* H)
    (h : (F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup ≤ f.ker)
    (σ : F.inertiaSubgroup) :
    F.tameQuotientLift f h (F.tameQuotientMk σ) = f σ :=
  rfl

/-- Map between named tame quotients.-/
def tameQuotientMap {H : Type v} [Group H]
    (E : AntitoneNormalSubgroupFiltration H)
    (f : F.inertiaSubgroup →* E.inertiaSubgroup)
    (h : ∀ σ : F.inertiaSubgroup, (σ : G) ∈ F.wildInertiaSubgroup →
      ((f σ : E.inertiaSubgroup) : H) ∈ E.wildInertiaSubgroup) :
    F.tameQuotient →* E.tameQuotient :=
  F.tameQuotientLift (E.tameQuotientMk.comp f) (by
    intro σ hσ
    rw [MonoidHom.mem_ker]
    exact (E.tameQuotientMk_eq_one_iff (f σ)).2 (h σ hσ))

/-- States the theorem `tameQuotientMap_apply_mk`.
@isnad1 id=eq.1h6v.s11.887932569f10 from=translated src=- shape=1f40f73f vocab=81d574b6
-/
@[simp]
theorem tameQuotientMap_apply_mk {H : Type v} [Group H]
    (E : AntitoneNormalSubgroupFiltration H)
    (f : F.inertiaSubgroup →* E.inertiaSubgroup)
    (h : ∀ σ : F.inertiaSubgroup, (σ : G) ∈ F.wildInertiaSubgroup →
      ((f σ : E.inertiaSubgroup) : H) ∈ E.wildInertiaSubgroup)
    (σ : F.inertiaSubgroup) :
    F.tameQuotientMap E f h (F.tameQuotientMk σ) =
      E.tameQuotientMk (f σ) :=
  rfl

/-- Provides the instance `quotientFinite`.
@isnad1 id=finite.0h3v.s4.9b2bc390bbb6 from=translated src=- shape=de9b95d8 vocab=199346ce
-/
instance quotientFinite [Finite G] (n : ℕ) : Finite (F.quotient n) :=
  Finite.of_surjective (F.quotientMk n) fun q =>
    F.quotient_inductionOn n
      (motive := fun q => ∃ σ, F.quotientMk n σ = q) q
      (fun σ => ⟨σ, rfl⟩)

end AntitoneNormalSubgroupFiltration

end DiscreteValuationField
end RamificationTheory

/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Geometry.FiniteRank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The rank calculus over a base set

Blueprint `sources/group_configuration/01-universal-domain.tex`, `def:closures`
and `lem:rank` ((R0)–(R10)).

For a base set `C ⊆ K` the matroid `rkMatroid k C` is the algebraic-independence
matroid of `K` over the subfield `k(C)`.  Its closure operator is
`S ↦ racl k (C ∪ S)` (`rkMatroid_closure_eq`), and a set is independent iff no
member lies in the closure of `C` together with the other members
(`rkMatroid_indep_iff`); in particular the matroid depends on `C` only through
`racl k C` (`rkMatroid_congr`).  The rank of a set `X` over `C` is
`erk k C X := (rkMatroid k C).eRk X`, an extended natural number (the
transcendence degree of `k(C, X)` over `k(C)`), finite for finite `X`.
Independence `IndepOver k C A B` ("`A ⫝_C B`") means that every finite subset
of `A` has the same rank over `C ∪ B` as over `C`.

The one substantial lemma is the tower law `erk_union_eq`
(`erk k C (X ∪ Y) = erk k C X + erk k (C ∪ X) Y`), proved by exhibiting a basis
of `X ∪ Y` over `C` as the disjoint union of a basis of `X` over `C` and a basis
of `Y` over `C ∪ X`.  Everything else in `lem:rank` is bookkeeping in `ℕ∞`.

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** the set-based rank and independence calculus, including finite character,
the tower law, closure invariance, symmetry, transitivity, independent closure
intersection and independent base change, is proved over arbitrary fields.
The set-rank/transcendence-degree bridge supplies the locus dimension lemmas;
no group configuration or extraction theorem is proved here.
-/

namespace GroupConfig

open AclGeom IntermediateField Matroid Set

noncomputable section

variable (k : Type*) {K : Type*} [Field k] [Field K] [Algebra k K]

/-! ### The matroid over a base set -/

/-- The algebraic-independence matroid of `K` over the subfield `k(C)`.-/
abbrev rkMatroid (C : Set K) : Matroid K :=
  AlgebraicIndependent.matroid (↥(adjoin k C)) K

/--
@isnad1 id=eq.0h3v.s5.edc539bf5b9e from=translated src=- shape=32300d1e vocab=1190384f
-/
@[simp]
theorem rkMatroid_ground (C : Set K) : (rkMatroid k C).E = univ := rfl

/-- The closure operator of `rkMatroid k C` is `S ↦ racl k (C ∪ S)`.
@isnad1 id=eq.0h4v.s6.8139bdc9dcec from=translated src=- shape=b73b2ecd vocab=c2aa340c
-/
theorem rkMatroid_closure_eq (C S : Set K) :
    (rkMatroid k C).closure S = (racl k (C ∪ S) : Set K) := by
  change (AlgebraicIndependent.matroid (↥(adjoin k C)) K).closure S = _
  rw [algebraicMatroid_closure_eq_racl (k := ↥(adjoin k C)) S]
  ext x
  simp only [SetLike.mem_coe]
  exact mem_racl_adjoin_base_iff

/--
@isnad1 id=iff.0h5v.s6.268701953743 from=translated src=- shape=eb32357a vocab=bf784370
-/
theorem mem_rkMatroid_closure_iff {C S : Set K} {x : K} :
    x ∈ (rkMatroid k C).closure S ↔ x ∈ racl k (C ∪ S) := by
  rw [rkMatroid_closure_eq, SetLike.mem_coe]

/-- Independence over `C`: no member lies in the closure of `C` and the other
members.
@isnad1 id=iff.0h4v.s6.800bd7bb6614 from=translated src=- shape=a018341d vocab=0994ccb1
-/
theorem rkMatroid_indep_iff {C S : Set K} :
    (rkMatroid k C).Indep S ↔ ∀ x ∈ S, x ∉ racl k (C ∪ (S \ {x})) := by
  rw [indep_iff_forall_notMem_closure_sdiff']
  simp only [rkMatroid_ground, subset_univ, true_and, mem_rkMatroid_closure_iff]

/-- The matroid over `C` depends only on `racl k C`.
@isnad1 id=eq.1h4v.s6.951f729cb14c from=translated src=- shape=02861b78 vocab=5cf86b57
-/
theorem rkMatroid_congr {C C' : Set K} (h : racl k C = racl k C') :
    rkMatroid k C = rkMatroid k C' := by
  refine Matroid.ext_closure fun X ↦ ?_
  rw [rkMatroid_closure_eq, rkMatroid_closure_eq, ← racl_union_left (k := k) C X, h,
    racl_union_left]

/-- Independence over a smaller base set is implied by independence over a
larger one.
@isnad1 id=indep.2h5v.s6.26828ce23460 from=translated src=- shape=b4b56f5e vocab=d3cc3086
-/
theorem rkMatroid_indep_of_subset_base {C C' S : Set K} (hCC' : C ⊆ C')
    (hS : (rkMatroid k C').Indep S) : (rkMatroid k C).Indep S := by
  rw [rkMatroid_indep_iff] at hS ⊢
  intro x hx hmem
  exact hS x hx (racl_mono (union_subset_union_left _ hCC') hmem)

/-- The closure of a basis of `X` over `C` contains `X`.
@isnad1 id=le.1h5v.s6.b31964b63b97 from=translated src=- shape=834f5c3a vocab=8a19d907
-/
theorem subset_racl_of_isBasis' {C X I : Set K} (hI : (rkMatroid k C).IsBasis' I X) :
    X ⊆ racl k (C ∪ I) := by
  have h := hI.closure_eq_closure
  rw [rkMatroid_closure_eq, rkMatroid_closure_eq] at h
  rw [h]
  exact subset_union_right.trans (subset_racl k (C ∪ X))

/-! ### Rank of a set over a base set -/

/-- The rank of `X ⊆ K` over the base set `C`: the transcendence degree of
`k(C, X)` over `k(C)`, as an extended natural number.-/
def erk (C X : Set K) : ℕ∞ := (rkMatroid k C).eRk X

/--
@isnad1 id=le.0h4v.s5.3dfc0d62eb8d from=translated src=- shape=4915690e vocab=b5cd1b70
-/
theorem erk_le_encard (C X : Set K) : erk k C X ≤ X.encard :=
  (rkMatroid k C).eRk_le_encard X

/--
@isnad1 id=lt.1h4v.s5.f1a100dfcfdf from=translated src=- shape=25c24cce vocab=404154f1
-/
theorem erk_lt_top {X : Set K} (hX : X.Finite) (C : Set K) : erk k C X < ⊤ :=
  (erk_le_encard k C X).trans_lt hX.encard_lt_top

/--
@isnad1 id=ne.1h4v.s5.8159277c121d from=translated src=- shape=25c24cce vocab=16915e7a
-/
theorem erk_ne_top {X : Set K} (hX : X.Finite) (C : Set K) : erk k C X ≠ ⊤ :=
  (erk_lt_top k hX C).ne

/-- Monotonicity in the set.
@isnad1 id=le.1h5v.s5.c737722c49bd from=translated src=- shape=21dbb16d vocab=668aa691
-/
theorem erk_mono {X Y : Set K} (C : Set K) (h : X ⊆ Y) : erk k C X ≤ erk k C Y :=
  (rkMatroid k C).eRk_mono h

/-- The rank over `C` depends only on `racl k C`.
@isnad1 id=eq.1h5v.s6.1461f98c6bf9 from=translated src=- shape=23352516 vocab=f30ce441
-/
theorem erk_congr_base {C C' : Set K} (h : racl k C = racl k C') (X : Set K) :
    erk k C X = erk k C' X := by
  unfold erk
  rw [rkMatroid_congr k h]

/-- (R2): the rank over `C` is the rank over `racl k C`.
@isnad1 id=eq.0h4v.s6.a48023a6b27b from=translated src=- shape=0dd335ef vocab=96d2c101
-/
theorem erk_racl_base (C X : Set K) : erk k (racl k C) X = erk k C X :=
  erk_congr_base k (racl_racl k C) X

/-- Adjoining elements of `racl k C` to the base does not change ranks.
@isnad1 id=eq.1h5v.s6.1f3463f0250c from=translated src=- shape=95f88f42 vocab=3a5a872c
-/
theorem erk_base_union_of_subset_racl {C S : Set K} (hS : S ⊆ racl k C) (X : Set K) :
    erk k (C ∪ S) X = erk k C X := by
  refine erk_congr_base k ?_ X
  refine le_antisymm (racl_le_of_subset_racl (union_subset (subset_racl k C) hS)) ?_
  exact racl_mono subset_union_left

/-- (R3): monotonicity in the base.
@isnad1 id=le.1h5v.s5.e285fdbcc8a5 from=translated src=- shape=2b3e6635 vocab=668aa691
-/
theorem erk_base_mono {C C' : Set K} (h : C ⊆ C') (X : Set K) :
    erk k C' X ≤ erk k C X := by
  obtain ⟨J, hJ⟩ := (rkMatroid k C').exists_isBasis' X
  unfold erk
  rw [← hJ.encard_eq_eRk]
  exact (rkMatroid_indep_of_subset_base k h hJ.indep).encard_le_eRk_of_subset hJ.subset

/-- The rank of the closure.
@isnad1 id=eq.0h4v.s6.644692609230 from=translated src=- shape=765a3092 vocab=c3fe275c
-/
theorem erk_racl (C X : Set K) : erk k C (racl k (C ∪ X)) = erk k C X := by
  unfold erk
  rw [← rkMatroid_closure_eq, eRk_closure_eq]

/-- A set inside the closure of `C ∪ X` contributes nothing to the rank over `C`.
@isnad1 id=eq.1h5v.s6.687edbb36c68 from=translated src=- shape=444f26a9 vocab=3a5a872c
-/
theorem erk_union_eq_of_subset_racl {C X Y : Set K} (hY : Y ⊆ racl k (C ∪ X)) :
    erk k C (X ∪ Y) = erk k C X := by
  refine le_antisymm ?_ (erk_mono k C subset_union_left)
  calc erk k C (X ∪ Y) ≤ erk k C (racl k (C ∪ X)) :=
        erk_mono k C (union_subset (subset_union_right.trans (subset_racl k (C ∪ X))) hY)
    _ = erk k C X := erk_racl k C X

/-- (R2): rank zero over `C` means containment in `racl k C`.
@isnad1 id=iff.0h4v.s6.bc84816d6391 from=translated src=- shape=4b771ee0 vocab=04b9a369
-/
theorem erk_eq_zero_iff {C X : Set K} : erk k C X = 0 ↔ X ⊆ racl k C := by
  have h0 : (rkMatroid k C).eRk X = 0 ↔ X ⊆ (rkMatroid k C).loops :=
    eRk_eq_zero_iff (subset_univ X)
  unfold erk
  rw [h0, ← closure_empty, rkMatroid_closure_eq, union_empty]

/--
@isnad1 id=eq.1h4v.s6.ee4624b70064 from=translated src=- shape=1605b1f9 vocab=04b9a369
-/
theorem erk_eq_zero_of_subset_racl {C X : Set K} (h : X ⊆ racl k C) : erk k C X = 0 :=
  (erk_eq_zero_iff k).2 h

/--
@isnad1 id=iff.0h4v.s6.9021cec67083 from=translated src=- shape=785a5b0b vocab=29594b38
-/
theorem erk_singleton_eq_zero_iff {C : Set K} {x : K} :
    erk k C {x} = 0 ↔ x ∈ racl k C := by
  rw [erk_eq_zero_iff, singleton_subset_iff, SetLike.mem_coe]

/--
@isnad1 id=eq.0h3v.s5.6a8bf5d27d3a from=translated src=- shape=dfe41a0a vocab=6fafe8af
-/
theorem erk_empty (C : Set K) : erk k C ∅ = 0 :=
  erk_eq_zero_of_subset_racl k (empty_subset _)

/--
@isnad1 id=eq.0h5v.s6.c9fb5b7df536 from=translated src=- shape=3d7cfbb8 vocab=9e0ae36b
-/
theorem erk_union_comm (C X Y : Set K) : erk k C (X ∪ Y) = erk k C (Y ∪ X) := by
  rw [union_comm]

/-- Subadditivity.
@isnad1 id=le.0h5v.s6.c8046afe9471 from=translated src=- shape=9438396e vocab=2e14742d
-/
theorem erk_union_le (C X Y : Set K) : erk k C (X ∪ Y) ≤ erk k C X + erk k C Y :=
  (rkMatroid k C).eRk_union_le_eRk_add_eRk X Y

/-- Submodularity.
@isnad1 id=le.0h5v.s6.ce6c8968d2aa from=translated src=- shape=d09f93fe vocab=4ac47fe6
-/
theorem erk_inter_add_erk_union_le (C X Y : Set K) :
    erk k C (X ∩ Y) + erk k C (X ∪ Y) ≤ erk k C X + erk k C Y :=
  (rkMatroid k C).eRk_inter_add_eRk_union_le X Y

/-! ### The tower law -/

/-- A basis of `Y` over `C ∪ X` is disjoint from `X`.
@isnad1 id=disjoint.1h6v.s6.a42c385ba17b from=translated src=- shape=b625a4f2 vocab=c56e9510
-/
theorem disjoint_of_isBasis'_union {C X Y J : Set K}
    (hJ : (rkMatroid k (C ∪ X)).IsBasis' J Y) : Disjoint X J := by
  rw [disjoint_right]
  intro e heJ heX
  have hind := (rkMatroid_indep_iff k).1 hJ.indep e heJ
  exact hind (subset_racl k _ (mem_union_left _ (mem_union_right _ heX)))

/-- (R1), the tower law: the rank of `X ∪ Y` over `C` is the rank of `X` over
`C` plus the rank of `Y` over `C ∪ X`.
@isnad1 id=eq.0h5v.s6.a74f1a5ee4aa from=translated src=- shape=613654bf vocab=46bbc628
-/
theorem erk_union_eq (C X Y : Set K) :
    erk k C (X ∪ Y) = erk k C X + erk k (C ∪ X) Y := by
  obtain ⟨I, hI⟩ := (rkMatroid k C).exists_isBasis' X
  obtain ⟨J, hJ⟩ := (rkMatroid k (C ∪ X)).exists_isBasis' Y
  have hdisjIJ : Disjoint I J := (disjoint_of_isBasis'_union k hJ).mono_left hI.subset
  -- `J` is independent over `C`.
  have hJC : (rkMatroid k C).Indep J :=
    rkMatroid_indep_of_subset_base k subset_union_left hJ.indep
  -- `I ∪ J` is independent over `C`.
  have hIJ : (rkMatroid k C).Indep (I ∪ J) := by
    rw [hI.indep.union_indep_iff_forall_notMem_closure_right hJC]
    intro e he hmem
    rw [mem_rkMatroid_closure_iff] at hmem
    have hJe := (rkMatroid_indep_iff k).1 hJ.indep e he.1
    refine hJe (racl_mono ?_ hmem)
    rw [union_assoc]
    exact union_subset_union_right C (union_subset_union_left _ hI.subset)
  -- `X ∪ Y` lies in the closure of `I ∪ J` over `C`.
  have hX : X ⊆ racl k (C ∪ I) := subset_racl_of_isBasis' k hI
  have hY : Y ⊆ racl k (C ∪ X ∪ J) := subset_racl_of_isBasis' k hJ
  have hXY : X ∪ Y ⊆ (rkMatroid k C).closure (I ∪ J) := by
    rw [rkMatroid_closure_eq]
    have h1 : (racl k (C ∪ I) : Set K) ⊆ racl k (C ∪ (I ∪ J)) := by
      rw [SetLike.coe_subset_coe]
      exact racl_mono (union_subset_union_right C subset_union_left)
    have h2 : (racl k (C ∪ X ∪ J) : Set K) ⊆ racl k (C ∪ (I ∪ J)) := by
      rw [SetLike.coe_subset_coe]
      refine racl_le_of_subset_racl ?_
      refine union_subset (union_subset ?_ ?_) ?_
      · exact subset_union_left.trans (subset_racl k _)
      · exact hX.trans h1
      · exact (subset_union_right.trans subset_union_right).trans (subset_racl k _)
    exact union_subset (hX.trans h1) (hY.trans h2)
  have hbasis : (rkMatroid k C).IsBasis' (I ∪ J) (X ∪ Y) :=
    (isBasis_iff_indep_subset_closure.2
      ⟨hIJ, union_subset_union hI.subset hJ.subset, hXY⟩).isBasis'
  unfold erk
  rw [← hbasis.encard_eq_eRk, ← hI.encard_eq_eRk, ← hJ.encard_eq_eRk]
  exact encard_union_eq hdisjIJ

/-- Cancellation in `ℕ∞`: if `x ≤ x'`, `y ≤ y'`, `x + y = x' + y'` and `x', y'`
are finite, then `x = x'` and `y = y'`.-/
private theorem ENat.eq_of_add_eq_add_of_le {x x' y y' : ℕ∞} (hx : x ≤ x') (hy : y ≤ y')
    (hx' : x' ≠ ⊤) (hy' : y' ≠ ⊤) (h : x + y = x' + y') : x = x' ∧ y = y' := by
  constructor
  · refine le_antisymm hx ?_
    have h1 : x' + y' ≤ x + y' := h ▸ add_le_add_right hy x
    exact (ENat.add_le_add_iff_right hy').1 h1
  · refine le_antisymm hy ?_
    have h1 : x' + y' ≤ x' + y := h ▸ add_le_add_left hx y
    exact (ENat.add_le_add_iff_left hx').1 h1

/-- The relative rank over a larger base, from the ranks of unions
(subtraction-free form of the tower law).
@isnad1 id=eq.2h5v.s6.89548b6be66b from=translated src=- shape=bdcfcfb6 vocab=10cff067
-/
theorem erk_base_union_eq_of_erk_union_eq {C X Y : Set K} (hX : X.Finite)
    (h : erk k C (X ∪ Y) = erk k C X + erk k C Y) :
    erk k (C ∪ X) Y = erk k C Y := by
  have h1 := erk_union_eq k C X Y
  rw [h] at h1
  exact le_antisymm (erk_base_mono k subset_union_left Y)
    ((ENat.add_le_add_iff_left (erk_ne_top k hX C)).1 h1.le)

/-! ### Finite character of the base -/

/-- Finite character of the base: the rank of a finite set over `C ∪ B` is
attained over `C ∪ b` for some finite `b ⊆ B`.
@isnad1 id=ex.1h5v.s6.338a8e7e1d86 from=translated src=- shape=5c5ede6c vocab=46e5dd05
-/
theorem exists_finite_subset_erk_union_eq {X : Set K} (hX : X.Finite) (C B : Set K) :
    ∃ b ⊆ B, b.Finite ∧ erk k (C ∪ b) X = erk k (C ∪ B) X := by
  classical
  obtain ⟨J, hJ⟩ := (rkMatroid k (C ∪ B)).exists_isBasis' X
  have hXcl : X ⊆ racl k (C ∪ B ∪ J) := subset_racl_of_isBasis' k hJ
  -- For each `x ∈ X` choose a finite generating set.
  choose T hTsub hTmem using fun x : X ↦ exists_finset_racl (hXcl x.2)
  have : Fintype X := hX.fintype
  let b : Set K := ⋃ x : X, ((T x : Set K) ∩ B)
  have hbB : b ⊆ B := iUnion_subset fun x ↦ inter_subset_right
  have hbfin : b.Finite := finite_iUnion fun x ↦ (T x).finite_toSet.subset inter_subset_left
  refine ⟨b, hbB, hbfin, le_antisymm ?_ (erk_base_mono k (union_subset_union_right C hbB) X)⟩
  -- `X ⊆ racl k (C ∪ b ∪ J)`, so the rank of `X` over `C ∪ b` is at most `J.encard`.
  have hXb : X ⊆ racl k (C ∪ b ∪ J) := by
    intro x hx
    have hT : (T ⟨x, hx⟩ : Set K) ⊆ C ∪ b ∪ J := by
      intro y hy
      rcases hTsub ⟨x, hx⟩ hy with (hyC | hyB) | hyJ
      · exact mem_union_left _ (mem_union_left _ hyC)
      · exact mem_union_left _ (mem_union_right _ (mem_iUnion.2 ⟨⟨x, hx⟩, hy, hyB⟩))
      · exact mem_union_right _ hyJ
    exact racl_mono hT (hTmem ⟨x, hx⟩)
  calc erk k (C ∪ b) X ≤ erk k (C ∪ b) (racl k (C ∪ b ∪ J)) := erk_mono k _ hXb
    _ = erk k (C ∪ b) J := erk_racl k _ J
    _ ≤ J.encard := erk_le_encard k _ J
    _ = erk k (C ∪ B) X := by unfold erk; exact hJ.encard_eq_eRk

/-! ### Independence of sets over a base -/

/-- `A ⫝_C B`: every finite subset of `A` has the same rank over `C ∪ B` as
over `C` (blueprint `def:closures`(4)).-/
def IndepOver (C A B : Set K) : Prop :=
  ∀ ⦃a : Set K⦄, a ⊆ A → a.Finite → erk k (C ∪ B) a = erk k C a

variable {k}

/--
@isnad1 id=eq.3h6v.s6.b130833e7086 from=translated src=- shape=564babc4 vocab=5cd2d880
-/
theorem IndepOver.erk_eq {C A B : Set K} (h : IndepOver k C A B) {a : Set K}
    (ha : a ⊆ A) (hfin : a.Finite) : erk k (C ∪ B) a = erk k C a :=
  h ha hfin

/-- (R0): independence passes to subsets on the left.
@isnad1 id=indepove.2h6v.s6.201751b00d4f from=translated src=- shape=47f0cb29 vocab=7345f16e
-/
theorem IndepOver.mono_left {C A A' B : Set K} (h : IndepOver k C A B) (hA : A' ⊆ A) :
    IndepOver k C A' B :=
  fun _ ha hfin ↦ h (ha.trans hA) hfin

/-- (R0): independence passes to subsets on the right.
@isnad1 id=indepove.2h6v.s6.02e8783e89e8 from=translated src=- shape=8dd2a0b5 vocab=7345f16e
-/
theorem IndepOver.mono_right {C A B B' : Set K} (h : IndepOver k C A B) (hB : B' ⊆ B) :
    IndepOver k C A B' := by
  intro a ha hfin
  refine le_antisymm (erk_base_mono k subset_union_left a) ?_
  calc erk k C a = erk k (C ∪ B) a := (h ha hfin).symm
    _ ≤ erk k (C ∪ B') a := erk_base_mono k (union_subset_union_right C hB) a

/-- (R0): finite character on both sides.
@isnad1 id=iff.0h5v.s6.75e5c5bba3c1 from=translated src=- shape=dd310d77 vocab=5cd2d880
-/
theorem indepOver_iff_forall_finite {C A B : Set K} :
    IndepOver k C A B ↔
      ∀ ⦃a : Set K⦄, a ⊆ A → a.Finite → ∀ ⦃b : Set K⦄, b ⊆ B → b.Finite →
        erk k (C ∪ b) a = erk k C a := by
  constructor
  · intro h a ha hfin b hb _
    exact (h.mono_right hb) ha hfin
  · intro h a ha hfin
    obtain ⟨b, hbB, hbfin, hb⟩ := exists_finite_subset_erk_union_eq k hfin C B
    rw [← hb]
    exact h ha hfin hbB hbfin

/-- Independence over `C` is independence over `racl k C`.
@isnad1 id=indepove.1h5v.s6.5ec87ddbed5d from=translated src=- shape=4fd4506c vocab=13d209e8
-/
theorem IndepOver.of_racl_base {C A B : Set K} (h : IndepOver k C A B) :
    IndepOver k (racl k C) A B := by
  intro a ha hfin
  rw [erk_racl_base, erk_congr_base k (racl_union_left (k := k) C B) a]
  exact h ha hfin

/-- Over `C`, a set is independent from `B` iff `racl k (C ∪ A)` is.
@isnad1 id=iff.0h5v.s6.a5a9cf53b3e9 from=translated src=- shape=aaf1f9af vocab=b152ac51
-/
theorem indepOver_racl_left_iff {C A B : Set K} :
    IndepOver k C (racl k (C ∪ A)) B ↔ IndepOver k C A B := by
  refine ⟨fun h ↦ h.mono_left (subset_union_right.trans (subset_racl k _)), fun h ↦ ?_⟩
  intro a' ha' hfin'
  classical
  -- Each element of `a'` is algebraic over `C` and a finite part of `A`.
  choose T hTsub hTmem using fun x : a' ↦ exists_finset_racl (ha' x.2)
  have : Fintype a' := hfin'.fintype
  let a : Set K := ⋃ x : a', ((T x : Set K) ∩ A)
  have haA : a ⊆ A := iUnion_subset fun x ↦ inter_subset_right
  have hafin : a.Finite := finite_iUnion fun x ↦ (T x).finite_toSet.subset inter_subset_left
  have ha'cl : a' ⊆ racl k (C ∪ a) := by
    intro x hx
    have hT : (T ⟨x, hx⟩ : Set K) ⊆ C ∪ a := by
      intro y hy
      rcases hTsub ⟨x, hx⟩ hy with hyC | hyA
      · exact mem_union_left _ hyC
      · exact mem_union_right _ (mem_iUnion.2 ⟨⟨x, hx⟩, hy, hyA⟩)
    exact racl_mono hT (hTmem ⟨x, hx⟩)
  have hCB : a' ⊆ racl k (C ∪ B ∪ a) :=
    ha'cl.trans (racl_mono (union_subset_union_left a subset_union_left))
  -- Compare the two tower decompositions of `erk (a ∪ a')`.
  have h1 : erk k C (a ∪ a') = erk k C a' + erk k (C ∪ a') a := by
    rw [union_comm a a']; exact erk_union_eq k C a' a
  have h2 : erk k (C ∪ B) (a ∪ a') = erk k (C ∪ B) a' + erk k (C ∪ B ∪ a') a := by
    rw [union_comm a a']; exact erk_union_eq k (C ∪ B) a' a
  have h3 : erk k C (a ∪ a') = erk k C a := erk_union_eq_of_subset_racl k ha'cl
  have h4 : erk k (C ∪ B) (a ∪ a') = erk k (C ∪ B) a := erk_union_eq_of_subset_racl k hCB
  have h5 : erk k (C ∪ B) a = erk k C a := h haA hafin
  have hle1 : erk k (C ∪ B) a' ≤ erk k C a' := erk_base_mono k subset_union_left a'
  have hle2 : erk k (C ∪ B ∪ a') a ≤ erk k (C ∪ a') a :=
    erk_base_mono k (union_subset_union_left a' subset_union_left) a
  have heq : erk k (C ∪ B) a' + erk k (C ∪ B ∪ a') a = erk k C a' + erk k (C ∪ a') a := by
    rw [← h2, ← h1, h3, h4, h5]
  exact (ENat.eq_of_add_eq_add_of_le hle1 hle2 (erk_ne_top k hfin' C)
    (erk_ne_top k hafin _) heq).1

/-- (R6): independence only depends on the closure of `C ∪ A`.
@isnad1 id=iff.1h6v.s6.3d7d397b48d6 from=translated src=- shape=afe6c505 vocab=e28934c2
-/
theorem indepOver_congr_left {C A A' B : Set K} (h : racl k (C ∪ A') = racl k (C ∪ A)) :
    IndepOver k C A B ↔ IndepOver k C A' B := by
  rw [← indepOver_racl_left_iff (A := A), ← indepOver_racl_left_iff (A := A'), h]

/-- (R6): independence only depends on the closure of `C ∪ B` (right-hand form).
@isnad1 id=iff.0h5v.s6.b0bb0a69d3f9 from=translated src=- shape=f288552a vocab=b152ac51
-/
theorem indepOver_racl_right_iff {C A B : Set K} :
    IndepOver k C A (racl k (C ∪ B)) ↔ IndepOver k C A B := by
  have hbase : racl k (C ∪ (racl k (C ∪ B) : Set K)) = racl k (C ∪ B) := by
    rw [racl_union_right, ← union_assoc, union_self]
  constructor
  · intro h a ha hfin
    have h' := h ha hfin
    rwa [erk_congr_base k hbase a] at h'
  · intro h a ha hfin
    rw [erk_congr_base k hbase a]
    exact h ha hfin

/-- (R4): symmetry of independence.
@isnad1 id=indepove.1h5v.s5.04667fd93430 from=translated src=- shape=1a8df9a3 vocab=8829969b
-/
theorem IndepOver.symm {C A B : Set K} (h : IndepOver k C A B) : IndepOver k C B A := by
  intro b hb hbfin
  obtain ⟨a, haA, hafin, ha⟩ := exists_finite_subset_erk_union_eq k hbfin C A
  rw [← ha]
  have hab : erk k (C ∪ b) a = erk k C a := (h.mono_right hb) haA hafin
  have h1 : erk k C (a ∪ b) = erk k C a + erk k (C ∪ a) b := erk_union_eq k C a b
  have h2 : erk k C (a ∪ b) = erk k C b + erk k (C ∪ b) a := by
    rw [union_comm a b]; exact erk_union_eq k C b a
  have h3 : erk k C a + erk k (C ∪ a) b = erk k C a + erk k C b := by
    rw [← h1, h2, hab, add_comm]
  exact le_antisymm (erk_base_mono k subset_union_left b)
    ((ENat.add_le_add_iff_left (erk_ne_top k hafin C)).1 h3.symm.le)

/--
@isnad1 id=iff.0h5v.s5.603317c96978 from=translated src=- shape=456d81ac vocab=8829969b
-/
theorem indepOver_comm {C A B : Set K} : IndepOver k C A B ↔ IndepOver k C B A :=
  ⟨IndepOver.symm, IndepOver.symm⟩

/-- (R5): transitivity.
@isnad1 id=iff.0h6v.s6.1ef2dec429d9 from=translated src=- shape=cac70905 vocab=ffe8f99f
-/
theorem indepOver_union_right_iff {C A B D : Set K} :
    IndepOver k C A (B ∪ D) ↔ IndepOver k C A B ∧ IndepOver k (C ∪ B) A D := by
  constructor
  · intro h
    refine ⟨h.mono_right subset_union_left, fun a ha hfin ↦ ?_⟩
    have h' := h ha hfin
    rw [← union_assoc] at h'
    refine le_antisymm (erk_base_mono k subset_union_left a) ?_
    calc erk k (C ∪ B) a ≤ erk k C a := erk_base_mono k subset_union_left a
      _ = erk k (C ∪ B ∪ D) a := h'.symm
  · rintro ⟨h1, h2⟩ a ha hfin
    rw [← union_assoc, h2 ha hfin, h1 ha hfin]

/-- (R7): the closures of independent sets meet in the closure of the base.
@isnad1 id=le.1h5v.s7.1c14ad5abb15 from=translated src=- shape=f318d10b vocab=5e2db88c
-/
theorem IndepOver.racl_inter_subset {C B D : Set K} (h : IndepOver k C B D) :
    (racl k (C ∪ B) : Set K) ∩ racl k (C ∪ D) ⊆ racl k C := by
  rintro x ⟨hxB, hxD⟩
  have hx : IndepOver k C {x} D :=
    (indepOver_racl_left_iff.2 h).mono_left (singleton_subset_iff.2 hxB)
  have h0 : erk k (C ∪ D) {x} = 0 := (erk_singleton_eq_zero_iff k).2 hxD
  have hx' := hx (subset_refl _) (finite_singleton x)
  rw [h0] at hx'
  exact (erk_singleton_eq_zero_iff k).1 hx'.symm

/-- (R7), equality form: `acl(C ∪ B) ∩ acl(C ∪ D) = acl(C)` for `B ⫝_C D`.
@isnad1 id=eq.1h5v.s7.995b171fa3b9 from=translated src=- shape=f318d10b vocab=4617198d
-/
theorem IndepOver.racl_inter_eq {C B D : Set K} (h : IndepOver k C B D) :
    (racl k (C ∪ B) : Set K) ∩ racl k (C ∪ D) = racl k C :=
  le_antisymm h.racl_inter_subset (subset_inter
    (SetLike.coe_subset_coe.2 (racl_mono subset_union_left))
    (SetLike.coe_subset_coe.2 (racl_mono subset_union_left)))

/-- (R8): a set independent from itself is algebraic over the base.
@isnad1 id=le.1h4v.s6.dc09772732e1 from=translated src=- shape=cf4da51c vocab=38e96cee
-/
theorem IndepOver.subset_racl_of_self {C B : Set K} (h : IndepOver k C B B) :
    B ⊆ racl k C := by
  intro b hb
  have h0 : erk k (C ∪ B) {b} = 0 :=
    (erk_singleton_eq_zero_iff k).2 (subset_racl k _ (mem_union_right _ hb))
  have hb' := h (singleton_subset_iff.2 hb) (finite_singleton b)
  rw [h0] at hb'
  exact (erk_singleton_eq_zero_iff k).1 hb'.symm

/-- (R9), first clause: `B ⫝_C D` and `A ⫝_C (B ∪ D)` give `(A ∪ B) ⫝_C D`.
@isnad1 id=indepove.2h6v.s6.0b4b12f25fcc from=translated src=- shape=16e8d9e3 vocab=ffe8f99f
-/
theorem IndepOver.union_left {C A B D : Set K} (h1 : IndepOver k C B D)
    (h2 : IndepOver k C A (B ∪ D)) : IndepOver k C (A ∪ B) D := by
  intro c hc hfin
  have hsplit : c = (c ∩ B) ∪ (c ∩ A) := by
    rw [← inter_union_distrib_left, union_comm, inter_eq_left.2 hc]
  have haA : c ∩ A ⊆ A := inter_subset_right
  have hbB : c ∩ B ⊆ B := inter_subset_right
  have hafin : (c ∩ A).Finite := hfin.subset inter_subset_left
  have hbfin : (c ∩ B).Finite := hfin.subset inter_subset_left
  have h2' : IndepOver k (C ∪ (c ∩ B)) A D :=
    (indepOver_union_right_iff.1 (h2.mono_right (union_subset_union_left D hbB))).2
  have key : erk k (C ∪ D) ((c ∩ B) ∪ (c ∩ A)) = erk k C ((c ∩ B) ∪ (c ∩ A)) := by
    rw [erk_union_eq k (C ∪ D), erk_union_eq k C, h1 hbB hbfin, union_right_comm,
      h2' haA hafin]
  rwa [← hsplit] at key

/-- (R9), second clause: `A ⫝_C B` and `(A ∪ B) ⫝_C D` give `A ⫝_C (B ∪ D)`.
@isnad1 id=indepove.2h6v.s6.b6b5db2609c6 from=translated src=- shape=8648d8f7 vocab=ffe8f99f
-/
theorem IndepOver.union_right {C A B D : Set K} (h1 : IndepOver k C A B)
    (h2 : IndepOver k C (A ∪ B) D) : IndepOver k C A (B ∪ D) := by
  rw [indepOver_union_right_iff]
  refine ⟨h1, fun a ha hfin ↦ ?_⟩
  -- Reduce to a finite part of `B` using finite character of the base.
  obtain ⟨b, hbB, hbfin, hb⟩ := exists_finite_subset_erk_union_eq k hfin (C ∪ D) B
  have hb' : erk k (C ∪ B ∪ D) a = erk k (C ∪ D ∪ b) a := by
    rw [union_right_comm, ← hb]
  have hb'' : erk k (C ∪ B) a = erk k (C ∪ b) a := by
    rw [h1 ha hfin, (h1.mono_right hbB) ha hfin]
  rw [hb', hb'']
  -- Compare the tower decompositions of `erk (b ∪ a)` over `C ∪ D` and over `C`.
  have hab : erk k (C ∪ D) (b ∪ a) = erk k C (b ∪ a) :=
    h2 (union_subset (hbB.trans subset_union_right) (ha.trans subset_union_left))
      (hbfin.union hfin)
  have hbD : erk k (C ∪ D) b = erk k C b := h2 (hbB.trans subset_union_right) hbfin
  have t1 := erk_union_eq k (C ∪ D) b a
  have t2 := erk_union_eq k C b a
  rw [hab, hbD, t2] at t1
  exact le_antisymm (erk_base_mono k (union_subset_union_left b subset_union_left) a)
    ((ENat.add_le_add_iff_left (erk_ne_top k hbfin C)).1 t1.le)

/-- (R10), first clause: independence is unchanged by adjoining to the base
a set independent from everything in sight.
@isnad1 id=iff.1h6v.s6.db52405ce516 from=translated src=- shape=57659cdf vocab=ab0c3170
-/
theorem indepOver_base_union_iff {C A B E : Set K}
    (hE : IndepOver k ∅ E (C ∪ (A ∪ B))) :
    IndepOver k C A B ↔ IndepOver k (C ∪ E) A B := by
  have hE' : IndepOver k C E (A ∪ B) := by
    have h := (indepOver_union_right_iff.1 hE).2
    rwa [empty_union] at h
  have hAB : IndepOver k C (A ∪ B) E := hE'.symm
  have hAe : IndepOver k C A E := hAB.mono_left subset_union_left
  have hAbe : IndepOver k (C ∪ B) A E := by
    have h' : IndepOver k C E (B ∪ A) := by rwa [union_comm] at hE'
    exact (indepOver_union_right_iff.1 h').2.symm
  constructor
  · intro h a ha hfin
    have e1 : erk k (C ∪ E ∪ B) a = erk k (C ∪ B) a := by
      rw [union_right_comm]; exact hAbe ha hfin
    have e2 : erk k (C ∪ E) a = erk k C a := hAe ha hfin
    rw [e1, e2]; exact h ha hfin
  · intro h a ha hfin
    have e1 : erk k (C ∪ E ∪ B) a = erk k (C ∪ B) a := by
      rw [union_right_comm]; exact hAbe ha hfin
    have e2 : erk k (C ∪ E) a = erk k C a := hAe ha hfin
    rw [← e1, ← e2]; exact h ha hfin

/-- (R10), second clause: algebraicity over the base is unchanged by adjoining
an independent set.
@isnad1 id=iff.1h5v.s6.c4977e878dee from=translated src=- shape=afa27e30 vocab=5287ca79
-/
theorem subset_racl_base_union_iff {C A E : Set K} (hE : IndepOver k ∅ E (C ∪ A)) :
    A ⊆ racl k C ↔ A ⊆ racl k (C ∪ E) := by
  refine ⟨fun h ↦ h.trans (racl_mono subset_union_left), fun h x hx ↦ ?_⟩
  have hAE : IndepOver k C A E := by
    have h' := (indepOver_union_right_iff.1 hE).2
    rw [empty_union] at h'
    exact h'.symm
  have hx' := hAE (singleton_subset_iff.2 hx) (finite_singleton x)
  rw [(erk_singleton_eq_zero_iff k).2 (h hx)] at hx'
  exact (erk_singleton_eq_zero_iff k).1 hx'.symm

/-! ### Bridges to the field-based matroids and to transcendence degree -/

section Bridges

variable (k)

/-- Over the empty base, `rkMatroid` is the algebraic-independence matroid over `k`.
@isnad1 id=eq.0h2v.s5.760fab55af61 from=translated src=- shape=7330b792 vocab=250126f7
-/
theorem rkMatroid_empty : rkMatroid k (∅ : Set K) = AlgebraicIndependent.matroid k K := by
  refine Matroid.ext_closure fun X ↦ ?_
  rw [rkMatroid_closure_eq, algebraicMatroid_closure_eq_racl, empty_union]

/-- Over (the carrier of) a subfield `M`, `rkMatroid` is the algebraic-independence
matroid over `M`.
@isnad1 id=eq.0h3v.s7.eb8d98e02e07 from=translated src=- shape=51e99801 vocab=581a5e55
-/
theorem rkMatroid_coe (M : IntermediateField k K) :
    rkMatroid k (M : Set K) = AlgebraicIndependent.matroid (↥M) K := by
  refine Matroid.ext_closure fun X ↦ ?_
  rw [rkMatroid_closure_eq, algebraicMatroid_closure_eq_racl (k := ↥M)]
  ext x
  simp only [SetLike.mem_coe]
  rw [mem_racl_iff, mem_racl_iff]
  have key : adjoin k ((M : Set K) ∪ X) = (adjoin (↥M) X).restrictScalars k :=
    (restrictScalars_adjoin k M X).symm
  rw [key]
  exact ⟨fun h ↦ h, fun h ↦ h⟩

/--
@isnad1 id=eq.0h3v.s5.ae2fd56ce773 from=translated src=- shape=e99c2d1d vocab=d8c464d4
-/
theorem erk_empty_eq (X : Set K) :
    erk k ∅ X = (AlgebraicIndependent.matroid k K).eRk X := by
  unfold erk
  rw [rkMatroid_empty]

/--
@isnad1 id=eq.0h4v.s7.a7c58f1745c6 from=translated src=- shape=0648c815 vocab=c276e920
-/
theorem erk_coe_eq (M : IntermediateField k K) (X : Set K) :
    erk k (M : Set K) X = (AlgebraicIndependent.matroid (↥M) K).eRk X := by
  unfold erk
  rw [rkMatroid_coe]

variable {k}

/-- The rank of a set in the algebraic-independence matroid over a field `R` is the
transcendence degree over `R` of the field it generates.-/
theorem _root_.AlgebraicIndependent.matroid_eRk_eq_toENat_trdeg (R : Type*) [Field R]
    [Algebra R K] (S : Set K) :
    (AlgebraicIndependent.matroid R K).eRk S =
      Cardinal.toENat (Algebra.trdeg R ↥(adjoin R S)) := by
  classical
  obtain ⟨I, hI⟩ := (AlgebraicIndependent.matroid R K).exists_isBasis' S
  rw [← hI.encard_eq_eRk, ← toENat_cardinalMk]
  congr 1
  set L := adjoin R S with hL
  have hIL : I ⊆ (L : Set K) := hI.subset.trans (subset_adjoin R S)
  let x : I → L := fun i ↦ ⟨(i : K), hIL i.2⟩
  have hx : IsTranscendenceBasis R x := by
    rw [isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]
    refine ⟨?_, ?_⟩
    · have h1 : AlgebraicIndependent R ((↑) : I → K) :=
        AlgebraicIndependent.matroid_indep_iff.1 hI.indep
      exact AlgebraicIndependent.of_comp L.val h1
    · -- every element of `L` is algebraic over `R[I]`
      have hScl : S ⊆ racl R I := by
        have h := hI.closure_eq_closure
        rw [algebraicMatroid_closure_eq_racl, algebraicMatroid_closure_eq_racl] at h
        rw [h]
        exact subset_racl R S
      have hLcl : (L : Set K) ⊆ racl R I := by
        rw [SetLike.coe_subset_coe]
        exact adjoin_le_iff.2 hScl
      refine ⟨fun y ↦ ?_⟩
      have hy : IsAlgebraic (Algebra.adjoin R (I : Set K)) (y : K) :=
        (mem_racl_iff_isAlgebraic_adjoin R).1 (hLcl y.2)
      have himg : (Algebra.adjoin R (Set.range x)).map L.val =
          Algebra.adjoin R (I : Set K) := by
        rw [AlgHom.map_adjoin]
        congr 1
        ext z
        constructor
        · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
          exact i.2
        · intro hz
          exact ⟨x ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩, rfl⟩
      let e : Algebra.adjoin R (Set.range x) ≃ₐ[R] Algebra.adjoin R (I : Set K) :=
        (Subalgebra.equivMapOfInjective _ L.val Subtype.val_injective).trans
          (Subalgebra.equivOfEq _ _ himg)
      refine IsAlgebraic.of_ringHom_of_comp_eq e L.val hy e.surjective Subtype.val_injective ?_
      ext a
      rfl
  exact hx.cardinalMk_eq_trdeg

/-- The rank over the carrier of a subfield `M` is the transcendence degree over `M`.
@isnad1 id=eq.0h4v.s9.061537851149 from=translated src=- shape=c319781b vocab=d1e213b1
-/
theorem erk_coe_eq_toENat_trdeg (M : IntermediateField k K) (X : Set K) :
    erk k (M : Set K) X = Cardinal.toENat (Algebra.trdeg (↥M) ↥(adjoin (↥M) X)) := by
  rw [erk_coe_eq, AlgebraicIndependent.matroid_eRk_eq_toENat_trdeg]

/-- The rank over the empty base is the transcendence degree over `k`.
@isnad1 id=eq.0h3v.s7.61b419ae2229 from=translated src=- shape=6123e51c vocab=a291c141
-/
theorem erk_empty_eq_toENat_trdeg (X : Set K) :
    erk k ∅ X = Cardinal.toENat (Algebra.trdeg k ↥(adjoin k X)) := by
  rw [erk_empty_eq, AlgebraicIndependent.matroid_eRk_eq_toENat_trdeg]

/-- Over (the carrier of) a subfield `M` together with a set `B`, `rkMatroid` is the
matroid over `M` with base `B`: change of base type.
@isnad1 id=eq.0h4v.s6.781a66e1b209 from=translated src=- shape=d25a91ed vocab=947be135
-/
theorem rkMatroid_coe_union (M : IntermediateField k K) (B : Set K) :
    rkMatroid k ((M : Set K) ∪ B) = rkMatroid (↥M) B := by
  refine Matroid.ext_closure fun X ↦ ?_
  rw [rkMatroid_closure_eq, rkMatroid_closure_eq]
  ext x
  simp only [SetLike.mem_coe]
  rw [mem_racl_iff, mem_racl_iff]
  have key : adjoin k ((M : Set K) ∪ B ∪ X) = (adjoin (↥M) (B ∪ X)).restrictScalars k := by
    rw [restrictScalars_adjoin k M (B ∪ X), union_assoc]
  rw [key]
  exact ⟨fun h ↦ h, fun h ↦ h⟩

/--
@isnad1 id=eq.0h5v.s7.0bcf12882c81 from=translated src=- shape=99f642a0 vocab=0bf6af4c
-/
theorem erk_coe_union (M : IntermediateField k K) (B X : Set K) :
    erk k ((M : Set K) ∪ B) X = erk (↥M) B X := by
  unfold erk
  rw [rkMatroid_coe_union]

/-- Independence over the base type `M` is independence over `k` with `M` adjoined to the
base set.
@isnad1 id=iff.0h6v.s7.8a3bcd55c6f5 from=translated src=- shape=c5aab4ec vocab=4ce317c1
-/
theorem indepOver_coe_union_iff (M : IntermediateField k K) (B A D : Set K) :
    IndepOver k ((M : Set K) ∪ B) A D ↔ IndepOver (↥M) B A D := by
  constructor
  · intro h a ha hfin
    have h' := h ha hfin
    rwa [union_assoc, erk_coe_union, erk_coe_union] at h'
  · intro h a ha hfin
    rw [union_assoc, erk_coe_union, erk_coe_union]
    exact h ha hfin

end Bridges

/-! ### Independence from rank equalities -/

/-- A finite set with the same rank over `C ∪ B` as over `C` is independent from `B`
over `C`.
@isnad1 id=indepove.2h5v.s6.2b7946bb20f9 from=translated src=- shape=d1c2a418 vocab=7b685e29
-/
theorem indepOver_of_erk_eq {C B X : Set K} (hX : X.Finite)
    (h : erk k (C ∪ B) X = erk k C X) : IndepOver k C X B := by
  intro a ha hfin
  have hsplit : X = a ∪ (X \ a) := (union_sdiff_cancel ha).symm
  have t1 := erk_union_eq k (C ∪ B) a (X \ a)
  have t2 := erk_union_eq k C a (X \ a)
  rw [← hsplit] at t1 t2
  have hle1 : erk k (C ∪ B) a ≤ erk k C a := erk_base_mono k subset_union_left a
  have hle2 : erk k (C ∪ B ∪ a) (X \ a) ≤ erk k (C ∪ a) (X \ a) :=
    erk_base_mono k (union_subset_union_left a subset_union_left) (X \ a)
  exact (ENat.eq_of_add_eq_add_of_le hle1 hle2 (erk_ne_top k hfin C)
    (erk_ne_top k (hX.subset sdiff_subset) _) (by rw [← t1, ← t2, h])).1

end

end GroupConfig

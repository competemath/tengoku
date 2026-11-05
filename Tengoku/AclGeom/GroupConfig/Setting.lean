/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Transfer.Transcendence
import Tengoku.AclGeom.GroupConfig.Rank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The universal domain: small sets and fresh elements

Blueprint `sources/group_configuration/01-universal-domain.tex`, `conv:ud`
and `lem:fresh`.

`UniversalDomain k K` records the standing hypothesis that the ambient field
`K` has infinite transcendence degree over the base `k`.  A set `C ⊆ K` is
*small* (`IsSmall k C`) if it has finite rank over `k`; a small set has the
same closure as one of its finite subsets (`IsSmall.exists_finite_racl_eq`),
and in a universal domain every small set has a fresh element outside its
closure (`exists_notMem_racl_of_isSmall`) and, for every `n`, a fresh
`n`-tuple of rank `n` over it (`exists_fresh_tuple`, blueprint `lem:fresh`).

This module is part of the formalization of the group configuration theorem
blueprint `sources/group_configuration_blueprint.tex`.

**Status:** finite-rank small sets have finite closure generators, and the explicit
infinite-transcendence-degree hypothesis supplies fresh tuples of every finite
rank. Algebraic closedness is not needed for these results. Generic loci are
developed in `GroupConfig.Locus` and `GroupConfig.PrimeLocus`; group-of-germs
extraction is in `GroupConfig.Main`.
-/

namespace GroupConfig

open AclGeom Matroid Set

noncomputable section

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/-- `conv:ud`: the ambient field `K` has infinite transcendence degree over the
base field `k`.  (The hypotheses that `k` and `K` are algebraically closed are
separate instance arguments where they are needed.)-/
class UniversalDomain : Prop where
  /-- The ambient extension has at least countably infinite transcendence degree.-/
  aleph0_le_trdeg : Cardinal.aleph0 ≤ Algebra.trdeg k K

variable {K}

/-- A set `C ⊆ K` is *small* if it has finite rank over `k`.-/
def IsSmall (C : Set K) : Prop := erk k ∅ C ≠ ⊤

variable {k}

theorem IsSmall.of_finite {C : Set K} (hC : C.Finite) : IsSmall k C :=
  erk_ne_top k hC ∅

theorem IsSmall.mono {C C' : Set K} (hC : IsSmall k C) (h : C' ⊆ C) : IsSmall k C' :=
  fun htop ↦ hC (eq_top_iff.2 (htop ▸ erk_mono k ∅ h))

theorem IsSmall.union {C D : Set K} (hC : IsSmall k C) (hD : IsSmall k D) :
    IsSmall k (C ∪ D) := by
  intro htop
  have h := erk_union_le k ∅ C D
  rw [htop] at h
  exact (ENat.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hC, lt_top_iff_ne_top.2 hD⟩).ne
    (top_le_iff.1 h)

theorem IsSmall.racl {C : Set K} (hC : IsSmall k C) : IsSmall k (racl k C : Set K) := by
  have h := erk_racl k ∅ C
  rw [empty_union] at h
  exact fun htop ↦ hC (h ▸ htop)

/-- A small set has the same closure as one of its finite subsets.-/
theorem IsSmall.exists_finite_racl_eq {C : Set K} (hC : IsSmall k C) :
    ∃ S ⊆ C, S.Finite ∧ AclGeom.racl k S = AclGeom.racl k C := by
  obtain ⟨J, hJ⟩ := (rkMatroid k ∅).exists_isBasis' C
  have hJfin : J.Finite := by
    rw [← encard_lt_top_iff, hJ.encard_eq_eRk]
    exact lt_top_iff_ne_top.2 hC
  refine ⟨J, hJ.subset, hJfin, le_antisymm (racl_mono hJ.subset) ?_⟩
  have h := subset_racl_of_isBasis' k hJ
  rw [empty_union] at h
  exact racl_le_of_subset_racl h

end

end GroupConfig

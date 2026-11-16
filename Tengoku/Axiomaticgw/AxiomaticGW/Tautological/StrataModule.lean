/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.Tautological.DecoratedStableGraph
public import Tengoku.Seed.LinearAlgebra.Finsupp.Defs
public import Tengoku.Seed.LinearAlgebra.Quotient.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The rational module of tautological strata

The strata module is the free rational module on isomorphism classes of
decorated stable graphs. It is deliberately not yet called the tautological
ring: multiplication requires the common-refinement and excess-intersection
formula, while passage to the tautological ring requires geometric relations.
-/

@[expose] public section

namespace AxiomaticGW

open scoped BigOperators

/-- Finite rational linear combinations of decorated strata of fixed genus
and external label type.-/
abbrev StrataModule (g : ℕ) (S : Type) [Fintype S] :=
  TautologicalStratum g S →₀ ℚ

namespace StrataModule

variable {g : ℕ} {S : Type} [Fintype S]

/-- Basis vector associated to one decorated stratum.-/
noncomputable def basis (x : TautologicalStratum g S) : StrataModule g S :=
  Finsupp.single x 1

/-- The codimension-`d` subspace is spanned by decorated strata of
codimension `d`.-/
noncomputable def degree (d : ℕ) : Submodule ℚ (StrataModule g S) :=
  Submodule.span ℚ {x | ∃ s : TautologicalStratum g S,
    s.codimension = d ∧ x = basis s}

/-- A basis stratum is homogeneous in its combinatorial codimension.
@isnad1 id=mem.0h3v.s6.3c0387f349c4 from=translated src=- shape=0e464f67 vocab=cb327c15
-/
theorem basis_mem_degree (x : TautologicalStratum g S) :
    basis x ∈ degree x.codimension := by
  apply Submodule.subset_span
  exact ⟨x, rfl, rfl⟩

/-- Relations forced solely by geometric dimension: a homogeneous stratum
above `3g - 3 + |S|` maps to zero in every geometric realization.-/
noncomputable def dimensionRelations : Submodule ℚ (StrataModule g S) :=
  Submodule.span ℚ {x | ∃ s : TautologicalStratum g S,
    StableArity.dimension g S < s.codimension ∧ x = basis s}

/-- Every above-dimension basis stratum belongs to the dimension-relation
submodule.
@isnad1 id=mem.1h3v.s6.c1f75fa0d734 from=translated src=- shape=2a95e085 vocab=74e75112
-/
theorem basis_mem_dimensionRelations (x : TautologicalStratum g S)
    (hx : StableArity.dimension g S < x.codimension) :
    basis x ∈ dimensionRelations := by
  apply Submodule.subset_span
  exact ⟨x, hx, rfl⟩

/-- Quotient of a strata module by an explicitly supplied submodule of
relations. The name does not claim that the supplied relations are complete.-/
abbrev KnownRelationsQuotient
    (relations : Submodule ℚ (StrataModule g S)) :=
  StrataModule g S ⧸ relations

/-- Canonical map to a quotient by known relations.-/
noncomputable def quotientMk (relations : Submodule ℚ (StrataModule g S)) :
    StrataModule g S →ₗ[ℚ] KnownRelationsQuotient relations :=
  relations.mkQ

/-- Every supplied relation vanishes in the corresponding quotient.
@isnad1 id=eq.1h4v.s8.e1fa84d3ea9f from=translated src=- shape=aac539ae vocab=8c725b2d
-/
theorem quotientMk_eq_zero
    (relations : Submodule ℚ (StrataModule g S))
    {x : StrataModule g S} (hx : x ∈ relations) :
    quotientMk relations x = 0 := by
  exact (Submodule.Quotient.mk_eq_zero relations).mpr hx

end StrataModule

end AxiomaticGW

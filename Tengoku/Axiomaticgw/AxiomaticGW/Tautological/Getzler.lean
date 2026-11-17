/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.Tautological.StrataRealization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Getzler's relation on `Mbar(1,4)`

Getzler's relation is represented as a named relation generator. The seven
terms use Getzler's orbifold-cycle normalization; an encoding into decorated
strata must therefore provide the normalization explicitly. Vanishing in the
known-relations quotient is formal, while validity in a geometric cohomology
target remains a separately visible hypothesis.
-/

@[expose] public section

namespace AxiomaticGW

open scoped BigOperators

/-- The seven symmetric codimension-two cycles occurring in Getzler's
relation on `Mbar(1,4)`.-/
inductive GetzlerStratum
  | delta22
  | delta23
  | delta24
  | delta34
  | delta03
  | delta04
  | deltaBeta
  deriving DecidableEq

/-- The finite index has seven relation terms. It is distinct from `Fin 4`,
which labels the four marked points of `Mbar(1,4)`.-/
instance : Fintype GetzlerStratum where
  elems := {.delta22, .delta23, .delta24, .delta34, .delta03, .delta04,
    .deltaBeta}
  complete x := by
    cases x
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    · exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
    · exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))
    · exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))
    · exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))))

/--
@isnad1 id=eq.0h0v.s3.16335a011ae5 from=translated src=- shape=b0ae1d2b vocab=ce3f496e
-/
@[simp]
theorem getzlerStratum_card : Fintype.card GetzlerStratum = 7 := rfl

namespace GetzlerStratum

/-- Coefficient of a named cycle in Getzler's relation
`12 delta22 - 4 delta23 - 2 delta24 + 6 delta34 + delta03 + delta04
- 2 deltaBeta`.-/
def coefficient : GetzlerStratum → ℚ
  | .delta22 => 12
  | .delta23 => -4
  | .delta24 => -2
  | .delta34 => 6
  | .delta03 => 1
  | .delta04 => 1
  | .deltaBeta => -2

/--
@isnad1 id=eq.0h0v.s3.b20c8fb1baab from=translated src=- shape=b0ae1d2b vocab=566d9002
-/
@[simp] theorem coefficient_delta22 : coefficient .delta22 = 12 := rfl
/--
@isnad1 id=eq.0h0v.s3.b0c417cadb6b from=translated src=- shape=f7285ee8 vocab=b26c87de
-/
@[simp] theorem coefficient_delta23 : coefficient .delta23 = -4 := rfl
/--
@isnad1 id=eq.0h0v.s3.8a3b0c1338be from=translated src=- shape=f7285ee8 vocab=cdce75c7
-/
@[simp] theorem coefficient_delta24 : coefficient .delta24 = -2 := rfl
/--
@isnad1 id=eq.0h0v.s3.1f39128f269a from=translated src=- shape=b0ae1d2b vocab=9139b8fd
-/
@[simp] theorem coefficient_delta34 : coefficient .delta34 = 6 := rfl
/--
@isnad1 id=eq.0h0v.s3.4f8e7ea5fef1 from=translated src=- shape=b0ae1d2b vocab=a640dcc1
-/
@[simp] theorem coefficient_delta03 : coefficient .delta03 = 1 := rfl
/--
@isnad1 id=eq.0h0v.s3.6d959cbd1d38 from=translated src=- shape=b0ae1d2b vocab=9a156f2c
-/
@[simp] theorem coefficient_delta04 : coefficient .delta04 = 1 := rfl
/--
@isnad1 id=eq.0h0v.s3.3b7404719ab6 from=translated src=- shape=f7285ee8 vocab=9f03ba6f
-/
@[simp] theorem coefficient_deltaBeta : coefficient .deltaBeta = -2 := rfl

end GetzlerStratum

/-- A concrete encoding of Getzler's seven named orbifold cycles as rational
linear combinations of decorated strata. The codimension proof prevents a
normalization table from silently referring to the wrong graph type.-/
structure GetzlerStrataEncoding where
  /-- Normalized symmetric cycle associated to each name.-/
  cycle : GetzlerStratum → StrataModule 1 (Fin 4)
  /-- Every encoded cycle has codimension two.-/
  cycle_degree : ∀ x, cycle x ∈ StrataModule.degree 2

namespace GetzlerStrataEncoding

/-- The exact linear combination in Getzler's relation.-/
noncomputable def relation (E : GetzlerStrataEncoding) :
    StrataModule 1 (Fin 4) :=
  ∑ x, GetzlerStratum.coefficient x • E.cycle x

/-- Getzler's relation is homogeneous of codimension two.
@isnad1 id=mem.0h1v.s8.1ca1b46b5790 from=translated src=- shape=b2254b7e vocab=8e06345a
-/
theorem relation_mem_degree (E : GetzlerStrataEncoding) :
    E.relation ∈ StrataModule.degree 2 := by
  unfold relation
  apply Submodule.sum_mem
  intro x _hx
  exact Submodule.smul_mem _ _ (E.cycle_degree x)

/-- Known relations generated by dimension vanishing and the chosen encoding
of Getzler's relation. This is a submodule, not a claim of completeness.-/
noncomputable def knownRelations (E : GetzlerStrataEncoding) :
    Submodule ℚ (StrataModule 1 (Fin 4)) :=
  StrataModule.dimensionRelations ⊔ Submodule.span ℚ {E.relation}

/-- The module quotient in which the encoded Getzler relation is imposed.-/
abbrev KnownQuotient (E : GetzlerStrataEncoding) :=
  StrataModule.KnownRelationsQuotient E.knownRelations

/-- The encoded Getzler combination vanishes in the quotient where it is a
named relation generator. This does not prove the geometric relation.
@isnad1 id=eq.0h1v.s9.4fce68639c16 from=translated src=- shape=2ccc256c vocab=6392f852
-/
theorem relation_eq_zero (E : GetzlerStrataEncoding) :
    StrataModule.quotientMk E.knownRelations E.relation = 0 := by
  apply StrataModule.quotientMk_eq_zero
  apply Submodule.mem_sup_right
  apply Submodule.subset_span
  exact Set.mem_singleton E.relation

end GetzlerStrataEncoding

/-- Semantic realization of the seven normalized Getzler cycles in an
abstract stable-curve cohomology target.-/
structure GetzlerRelationGeometry
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (C : StableCurveCohomology R) where
  /-- Realized named cycles.-/
  cycle : GetzlerStratum → C.H 1 (Fin 4)
  /-- Every realized cycle has codimension two.-/
  cycle_degree : ∀ x, cycle x ∈ (C.H 1 (Fin 4)).degree 2
  /-- Geometric Getzler relation. Unlike quotient vanishing, this field is
  genuine additional geometric input.-/
  relation : ∑ x, algebraMap ℚ R (GetzlerStratum.coefficient x) • cycle x = 0

namespace GetzlerStrataEncoding

variable {R : Type*} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R}

attribute [local instance] strataRealizationModule

/-- If an encoded cycle realizes as the corresponding geometric cycle, the
encoded Getzler combination lies in the realization kernel.
@isnad1 id=mem.1h5v.s9.7eefa6f510a7 from=translated src=- shape=dea9d655 vocab=5afa7084
-/
theorem relation_mem_realization_kernel (E : GetzlerStrataEncoding)
    (A : StrataRealization C 1 (Fin 4)) (G : GetzlerRelationGeometry C)
    (hcycle : ∀ x, A.map (E.cycle x) = G.cycle x) : E.relation ∈ A.kernel := by
  letI : Module ℚ (C.H 1 (Fin 4)) :=
    strataRealizationModule C 1 (Fin 4)
  rw [A.mem_kernel_iff]
  unfold relation
  rw [map_sum]
  simp only [map_smul, hcycle]
  change ∑ x, algebraMap ℚ R (GetzlerStratum.coefficient x) • G.cycle x = 0
  exact G.relation

/-- The dimension and encoded Getzler relations lie in the kernel of every
compatible geometric realization.
@isnad1 id=le.1h5v.s9.c8d098521687 from=translated src=- shape=ec087b9b vocab=022e530e
-/
theorem knownRelations_le_realization_kernel (E : GetzlerStrataEncoding)
    (A : StrataRealization C 1 (Fin 4)) (G : GetzlerRelationGeometry C)
    (hcycle : ∀ x, A.map (E.cycle x) = G.cycle x) :
    E.knownRelations ≤ A.kernel := by
  apply sup_le
  · apply A.dimensionRelations_le_kernel
    change 3 ≤ 2 * 1 + Fintype.card (Fin 4)
    rw [Fintype.card_fin]
    omega
  · apply Submodule.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact E.relation_mem_realization_kernel A G hcycle

/-- Factor a compatible geometric realization through the quotient imposing
the encoded Getzler relation and dimension vanishing.-/
noncomputable def realizationFactor (E : GetzlerStrataEncoding)
    (A : StrataRealization C 1 (Fin 4)) (G : GetzlerRelationGeometry C)
    (hcycle : ∀ x, A.map (E.cycle x) = G.cycle x) :
    E.KnownQuotient →ₗ[ℚ] C.H 1 (Fin 4) :=
  A.factor E.knownRelations
    (E.knownRelations_le_realization_kernel A G hcycle)

end GetzlerStrataEncoding

end AxiomaticGW

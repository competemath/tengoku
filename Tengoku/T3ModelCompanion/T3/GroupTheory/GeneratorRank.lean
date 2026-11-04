/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Tengoku.T3ModelCompanion.T3.GroupTheory.Free.Graded
public import Tengoku.T3ModelCompanion.T3.GroupTheory.GradedQuotient
public import Tengoku.Seed.GroupTheory.Rank
public import Tengoku.Seed.LinearAlgebra.Dimension.Constructions
public import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Generator rank and the dimensions of the first two graded layers

The paper's minimum number of generators is mathlib's `Group.rank` on finitely generated
groups. No new rank definition is introduced. A finite generating family gives a surjection
from the corresponding free exponent-three group and hence surjections on its actual graded
layers. The free-layer coefficient bases bound the first two dimensions by the number of
generators and its second binomial coefficient.

The ambient group is not assumed finite. Finite dimensionality is proved along with each
bound, so the numerical conclusions do not depend on the default value of infinite `finrank`.
Empty generating families and trivial groups are included.

Paper-ID: preliminaries.notation.generator_rank, structure.derived_strictification,
structure.lcs_strictification
TeX: T3_modelcompanion_v9.tex, Notation 2.1(7), `lemma:commutator root`,
`lemma:number of generators for triple commutator roots`, lines 1180–1182 and 1230–1231.
-/

@[expose] public section

namespace Group

/-- A finite generating family supplies finite generation without any finiteness assumption
on the group itself.

Paper-ID: preliminaries.notation.generator_rank
TeX: T3_modelcompanion_v9.tex, Notation 2.1, item 7, minimum number of generators.
@isnad1 id=fg.1h3v.s5.b3974b9b06c9 from=translated src=- shape=381fdbde vocab=13e1d283
-/
theorem fg_of_generating_family {G I : Type*} [Group G] [Finite I] (a : I → G)
    (ha : Subgroup.closure (Set.range a) = ⊤) : FG G :=
  fg_iff.mpr ⟨Set.range a, ha, Set.finite_range a⟩

end Group

namespace T3

open AssociatedGraded

namespace Free

variable {I G : Type*} [Group G] [Fact (HasExponentThree G)]

/-- A generating family gives a surjection from the free exponent-three group on its indices.

Paper-ID: preliminaries.notation.generator_rank, structure.derived_strictification,
structure.lcs_strictification
TeX: T3_modelcompanion_v9.tex, `lemma:commutator root` and
`lemma:number of generators for triple commutator roots`, the given generating families.
@isnad1 id=surjecti.1h3v.s7.4a4bb15ef47c from=translated src=- shape=45bbea10 vocab=531a6008
-/
theorem lift_surjective_of_generating_family (a : I → G)
    (ha : Subgroup.closure (Set.range a) = ⊤) :
    Function.Surjective (lift (show HasExponentThree G from Fact.out) a) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← ha]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact ⟨of i, lift_of (show HasExponentThree G from Fact.out) a i⟩

/-- The first graded layer of a free group on finitely many generators is finite dimensional.

Paper-ID: preliminaries.free_graded_equiv, structure.derived_strictification
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`, degree one.
@isnad1 id=finite.0h1v.s7.2dc5a39d82f7 from=translated src=- shape=286ad9ba vocab=916b1ffb
-/
instance finite_layerOne [Finite I] : Module.Finite (ZMod 3) (Layer (Free I) 1) := by
  classical
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  exact Module.Finite.of_basis (Module.Basis.ofRepr layerOneEquiv)

/-- The second graded layer of a free group on finitely many generators is finite dimensional.

Paper-ID: preliminaries.free_graded_equiv, structure.lcs_strictification
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`, degree two.
@isnad1 id=finite.0h1v.s7.8bcd31898f65 from=translated src=- shape=286ad9ba vocab=916b1ffb
-/
instance finite_layerTwo [Finite I] : Module.Finite (ZMod 3) (Layer (Free I) 2) := by
  classical
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  exact Module.Finite.of_basis (Module.Basis.ofRepr layerTwoEquiv)

/-- The dimension of the first free graded layer is the number of free generators.

Paper-ID: preliminaries.free_graded_equiv, structure.derived_strictification
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`, degree one.
@isnad1 id=eq.0h1v.s7.2a3cf9fb1541 from=translated src=- shape=4562b2c2 vocab=069a1d07
-/
theorem finrank_layerOne [Finite I] :
    Module.finrank (ZMod 3) (Layer (Free I) 1) = Nat.card I := by
  classical
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let : Fintype I := Fintype.ofFinite I
  rw [layerOneEquiv.finrank_eq, Module.finrank_finsupp_self, Nat.card_eq_fintype_card]

/-- The dimension of the second free graded layer counts increasing pairs of generators.

Paper-ID: preliminaries.free_graded_equiv, structure.lcs_strictification
TeX: T3_modelcompanion_v9.tex, `proposition:gr(F) is Grassmann algebra`, degree two.
@isnad1 id=eq.0h1v.s7.b09aafc9c649 from=translated src=- shape=7308c83d vocab=ea00a440
-/
theorem finrank_layerTwo [Finite I] :
    Module.finrank (ZMod 3) (Layer (Free I) 2) = (Nat.card I).choose 2 := by
  classical
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let : Fintype (IncreasingPair I) := Fintype.ofFinite _
  rw [layerTwoEquiv.finrank_eq, Module.finrank_finsupp_self,
    ← Nat.card_eq_fintype_card, IncreasingPair.natCard_eq_choose]

end Free

namespace AssociatedGraded

variable {G I : Type*} [Group G] [Fact (HasExponentThree G)]

/-- A finite generating family makes the first layer finite dimensional.

Paper-ID: structure.derived_strictification
TeX: T3_modelcompanion_v9.tex, `lemma:commutator root`, the finite-dimensional basis choice.
@isnad1 id=finite.1h3v.s6.61af0feaedc8 from=translated src=- shape=68f4d47a vocab=14f34b2e
-/
theorem finite_layerOne_of_generating_family [Finite I] (a : I → G)
    (ha : Subgroup.closure (Set.range a) = ⊤) : Module.Finite (ZMod 3) (Layer G 1) :=
  Module.Finite.of_surjective (mapLayer (Free.lift (show HasExponentThree G from Fact.out) a) 1)
    (mapLayer_surjective _ (Free.lift_surjective_of_generating_family a ha) 1)

/-- A finite generating family makes the second layer finite dimensional.

Paper-ID: structure.lcs_strictification
TeX: T3_modelcompanion_v9.tex, `lemma:number of generators for triple commutator roots`,
the finite-dimensional basis choice.
@isnad1 id=finite.1h3v.s6.be36a421d715 from=translated src=- shape=68f4d47a vocab=14f34b2e
-/
theorem finite_layerTwo_of_generating_family [Finite I] (a : I → G)
    (ha : Subgroup.closure (Set.range a) = ⊤) : Module.Finite (ZMod 3) (Layer G 2) :=
  Module.Finite.of_surjective (mapLayer (Free.lift (show HasExponentThree G from Fact.out) a) 2)
    (mapLayer_surjective _ (Free.lift_surjective_of_generating_family a ha) 2)

/-- The first-layer dimension is bounded by the size of any finite generating family.

Paper-ID: structure.derived_strictification
TeX: T3_modelcompanion_v9.tex, `lemma:commutator root`, `dim gr₁(C) ≤ m`.
@isnad1 id=le.1h3v.s6.b0ba918e99af from=translated src=- shape=34684515 vocab=a0bd1c33
-/
theorem finrank_layerOne_le_of_generating_family [Finite I] (a : I → G)
    (ha : Subgroup.closure (Set.range a) = ⊤) :
    Module.finrank (ZMod 3) (Layer G 1) ≤ Nat.card I := by
  simpa only [Free.finrank_layerOne] using LinearMap.finrank_le_finrank_of_surjective
    (mapLayer_surjective _ (Free.lift_surjective_of_generating_family a ha) 1)

/-- The second-layer dimension is bounded by the number of pairs in a finite generating family.

Paper-ID: structure.lcs_strictification
TeX: T3_modelcompanion_v9.tex, `lemma:number of generators for triple commutator roots`,
`dim gr₂(C) ≤ binom(n,2)`.
@isnad1 id=le.1h3v.s6.0d3c962617dd from=translated src=- shape=d6bcfaf3 vocab=eeda1620
-/
theorem finrank_layerTwo_le_of_generating_family [Finite I] (a : I → G)
    (ha : Subgroup.closure (Set.range a) = ⊤) :
    Module.finrank (ZMod 3) (Layer G 2) ≤ (Nat.card I).choose 2 := by
  simpa only [Free.finrank_layerTwo] using LinearMap.finrank_le_finrank_of_surjective
    (mapLayer_surjective _ (Free.lift_surjective_of_generating_family a ha) 2)

/-- The first layer of a finitely generated exponent-three group is finite dimensional.

Paper-ID: preliminaries.notation.generator_rank, structure.derived_strictification
TeX: T3_modelcompanion_v9.tex, `lemma:commutator root`, the finite-dimensional basis choice.
@isnad1 id=finite.0h1v.s6.d796c086691b from=translated src=- shape=82bb75d8 vocab=3e8298a9
-/
instance finite_layerOne [Group.FG G] : Module.Finite (ZMod 3) (Layer G 1) := by
  obtain ⟨s, hs, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  let : Finite s := hfin.to_subtype
  exact finite_layerOne_of_generating_family (Subtype.val : s → G) (by simpa using hs)

/-- The second layer of a finitely generated exponent-three group is finite dimensional.

Paper-ID: preliminaries.notation.generator_rank, structure.lcs_strictification
TeX: T3_modelcompanion_v9.tex, `lemma:number of generators for triple commutator roots`,
the finite-dimensional basis choice.
@isnad1 id=finite.0h1v.s6.9ef3fcf3dde6 from=translated src=- shape=82bb75d8 vocab=3e8298a9
-/
instance finite_layerTwo [Group.FG G] : Module.Finite (ZMod 3) (Layer G 2) := by
  obtain ⟨s, hs, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  let : Finite s := hfin.to_subtype
  exact finite_layerTwo_of_generating_family (Subtype.val : s → G) (by simpa using hs)

/-- The paper's generator rank bounds the first graded dimension.

Paper-ID: preliminaries.notation.generator_rank, structure.derived_strictification
TeX: T3_modelcompanion_v9.tex, Notation 2.1(7), `lemma:commutator root`.
@isnad1 id=le.0h1v.s6.0bc2640cfa3a from=translated src=- shape=7f483030 vocab=13a34266
-/
theorem finrank_layerOne_le_rank [Group.FG G] :
    Module.finrank (ZMod 3) (Layer G 1) ≤ Group.rank G := by
  obtain ⟨s, hcard, hs⟩ := Group.rank_spec G
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, hcard] using
    finrank_layerOne_le_of_generating_family (Subtype.val : s → G) (by simpa using hs)

/-- The number of pairs of a minimum generating family bounds the second graded dimension.

Paper-ID: preliminaries.notation.generator_rank, structure.lcs_strictification
TeX: T3_modelcompanion_v9.tex, Notation 2.1(7),
`lemma:number of generators for triple commutator roots`.
@isnad1 id=le.0h1v.s6.d81f16ffa0c1 from=translated src=- shape=e9fb293c vocab=35dbe311
-/
theorem finrank_layerTwo_le_rank [Group.FG G] :
    Module.finrank (ZMod 3) (Layer G 2) ≤ (Group.rank G).choose 2 := by
  obtain ⟨s, hcard, hs⟩ := Group.rank_spec G
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, hcard] using
    finrank_layerTwo_le_of_generating_family (Subtype.val : s → G) (by simpa using hs)

end AssociatedGraded

namespace Free

variable {I : Type*}

/-- A free exponent-three group on finitely many generators is finitely generated.

Paper-ID: preliminaries.notation.generator_rank, structure.strict_envelope
TeX: T3_modelcompanion_v9.tex, `proposition:bdd LCS`, the free-two factor.
@isnad1 id=fg.0h1v.s4.66e836f79362 from=translated src=- shape=1666ae32 vocab=cadb5880
-/
instance fg [Finite I] : Group.FG (Free I) :=
  Group.fg_iff.mpr ⟨Set.range of, closure_range_of, Set.finite_range of⟩

/-- The rank of a free exponent-three group is bounded by the number of its generators.

Paper-ID: preliminaries.notation.generator_rank, structure.strict_envelope
TeX: T3_modelcompanion_v9.tex, `proposition:bdd LCS`, the two added generators.
@isnad1 id=le.0h1v.s4.e7566abb6c4f from=translated src=- shape=f1cbd57e vocab=25c2258b
-/
theorem rank_le_card [Finite I] : Group.rank (Free I) ≤ Nat.card I := by
  classical
  let := Fintype.ofFinite I
  have hgen : Subgroup.closure (↑(Finset.univ.image (of : I → Free I)) : Set (Free I)) = ⊤ := by
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using closure_range_of (I := I)
  exact (Group.rank_le hgen).trans (Finset.card_image_le.trans_eq (by simp))

end Free

end T3

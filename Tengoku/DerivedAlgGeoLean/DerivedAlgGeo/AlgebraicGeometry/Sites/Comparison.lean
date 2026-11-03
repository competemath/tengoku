/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.AlgebraicGeometry.Sites.Etale
import Tengoku.Seed.AlgebraicGeometry.Sites.Fpqc
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Sites.QuasiCompact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Comparing the big Zariski, étale, fppf and fpqc sites

Mathlib defines `Scheme.zariskiTopology`, `Scheme.etaleTopology`,
`Scheme.fppfTopology` and `Scheme.fpqcTopology`, proves the fpqc topology
subcanonical, and derives the fppf case from it.  At the pin it records the
comparisons `zariskiTopology ≤ etaleTopology`,
`zariskiPrecoverage ≤ fppfPrecoverage` and `fppfTopology ≤ fpqcTopology`, but
not the étale-to-fppf comparison, so the étale site has no `Subcanonical`
instance and the Zariski-to-fppf comparison is available only at the
precoverage level.

This file supplies the missing edges of that square.  Every étale morphism is
smooth, hence flat and locally of finite presentation, so an étale covering
family is an fppf covering family; subcanonicity then descends along that
inequality by `GrothendieckTopology.Subcanonical.of_le`.  No new descent
theorem is proved here: the content is Mathlib's fpqc descent for
representables, transported along topology inequalities.

These are direct extensions of Mathlib's site API, stated about Mathlib's own
topologies.  Nothing here is about stacks, moduli, or algebraicity.

The fppf and étale precoverages also agree with their quasi-compact property precoverages:
flat morphisms locally of finite presentation, and étale morphisms, are open maps. The resulting
topology equalities extend Mathlib's `AlgebraicGeometry/Sites/Fpqc.lean` and
`AlgebraicGeometry/Sites/Etale.lean`, their respective upstream owners.
-/

namespace AlgebraicGeometry.Scheme

open CategoryTheory MorphismProperty

universe u

/-- Flat morphisms locally of finite presentation are open, so the generic open-map criterion
supplies the finite local refinements required by quasi-compact covers.
@isnad1 id=eq.0h0v.s5.75878b39915c from=translated src=- shape=2acc09a4 vocab=b5100662
-/
lemma fppfPrecoverage_eq_propQCPrecoverage :
    fppfPrecoverage.{u} = propQCPrecoverage (@Flat ⊓ @LocallyOfFinitePresentation) :=
  precoverage_eq_propQCPrecoverage_of_isOpenMap fun _ _ f ⟨_, _⟩ ↦ f.isOpenMap

/-- Compare precoverages before generating the topology, using openness of flat, locally
finitely presented morphisms rather than a new descent theorem.
@isnad1 id=eq.0h0v.s5.1b82a58d3949 from=translated src=- shape=2acc09a4 vocab=8a4180a1
-/
lemma fppfTopology_eq_propQCTopology :
    fppfTopology.{u} = propQCTopology (@Flat ⊓ @LocallyOfFinitePresentation) :=
  congrArg Precoverage.toGrothendieck fppfPrecoverage_eq_propQCPrecoverage

/-- Étale morphisms are open, so their jointly surjective covering families satisfy the
quasi-compact covering condition without requiring each arrow to be quasi-compact.
@isnad1 id=eq.0h0v.s2.8f2864899ac8 from=translated src=- shape=95347b04 vocab=44d1984e
-/
lemma etalePrecoverage_eq_propQCPrecoverage :
    etalePrecoverage.{u} = propQCPrecoverage @Etale :=
  precoverage_eq_propQCPrecoverage_of_isOpenMap fun _ _ f _ ↦ f.isOpenMap

/-- Generate both topologies from the equal precoverages; the comparison requires no
additional finiteness hypothesis beyond étaleness.
@isnad1 id=eq.0h0v.s2.41d49db98ea2 from=translated src=- shape=95347b04 vocab=15885a55
-/
lemma etaleTopology_eq_propQCTopology :
    etaleTopology.{u} = propQCTopology @Etale :=
  congrArg Precoverage.toGrothendieck etalePrecoverage_eq_propQCPrecoverage

/-- Every étale covering family is an fppf covering family: an étale morphism
is smooth, hence flat and locally of finite presentation.
@isnad1 id=le.0h0v.s4.6c8278a2d6c7 from=translated src=- shape=836e6cbb vocab=a99d5b74
-/
lemma etalePrecoverage_le_fppfPrecoverage :
    etalePrecoverage.{u} ≤ fppfPrecoverage.{u} :=
  precoverage_mono fun _ _ _ _ ↦ ⟨inferInstance, inferInstance⟩

/-- The étale topology is coarser than the fppf topology.
@isnad1 id=le.0h0v.s3.7fb11587153d from=translated src=- shape=836e6cbb vocab=ab9f7dde
-/
lemma etaleTopology_le_fppfTopology : etaleTopology.{u} ≤ fppfTopology.{u} :=
  Precoverage.toGrothendieck_mono etalePrecoverage_le_fppfPrecoverage

/-- The étale topology is coarser than the fpqc topology.
@isnad1 id=le.0h0v.s3.5115586c384e from=translated src=- shape=836e6cbb vocab=7b1228f8
-/
lemma etaleTopology_le_fpqcTopology : etaleTopology.{u} ≤ fpqcTopology.{u} :=
  le_trans etaleTopology_le_fppfTopology fppfTopology_le_fpqcTopology

/-- The big Zariski topology is coarser than the fppf topology.  Mathlib has
this comparison at the level of precoverages only.
@isnad1 id=le.0h0v.s3.1834f0a03cac from=translated src=- shape=836e6cbb vocab=e982a7a8
-/
lemma zariskiTopology_le_fppfTopology : zariskiTopology.{u} ≤ fppfTopology.{u} :=
  Precoverage.toGrothendieck_mono zariskiPrecoverage_le_fppfPrecoverage

/-- The étale site is subcanonical, because the fppf site is and the étale
topology is coarser.  This is Mathlib's fpqc descent theorem for
representables restricted along `etaleTopology_le_fppfTopology`; it is not a
new descent result.
@isnad1 id=subcanon.0h0v.s2.d0a95e8b66bc from=translated src=- shape=25b03439 vocab=24fd5f6e
-/
instance subcanonical_etaleTopology : etaleTopology.{u}.Subcanonical :=
  .of_le etaleTopology_le_fppfTopology

end AlgebraicGeometry.Scheme

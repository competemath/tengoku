import Tengoku.MiyaokaMoriCharzero.MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegree
import Tengoku.Seed.Algebra.Algebra.Equiv
import Tengoku.Seed.Algebra.Algebra.Tower
import Tengoku.Seed.AlgebraicGeometry.ResidueField
import Tengoku.Seed.RingTheory.AlgebraicIndependent.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The affine residue-field isomorphism over the specified base field

For an actual morphism `f : Spec A ⟶ Spec k`, the coefficient algebra on `A`
comes from `Spec.preimage f`. Mathlib's isomorphism between the scheme residue
field and the prime-ideal residue field respects this same coefficient map and
the existing `pointBaseMap f p`.

The compatibility equation promotes the actual residue-field ring isomorphism
to a `k`-algebra equivalence. Transcendence degree is then compared through that
algebra equivalence. No finite-type or dimension hypothesis is needed here.

Sources: Stacks Project, Tag 0A21 (`varieties.tex`, dimension-locally-algebraic)
and Tag 02R1 (`chow.tex`, equal-dimension). This adapter supplies the common-base
identification required by the dimension argument for the cycle pushforward; it does not
assert that dimension argument.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Intersection

/-- The affine description of the existing base map, before choosing algebra instances.
@isnad1 id=eq.0h4v.s9.edaf17083980 from=translated src=- shape=6591dda6 vocab=18881998
-/
theorem pointBaseMap_spec_eq {k : Type u} [Field k]
    (A : CommRingCat.{u}) (f : Spec A ⟶ Spec (CommRingCat.of k)) (p : Spec A) :
    letI : p.asIdeal.IsPrime := p.isPrime
    pointBaseMap f p = Spec.preimage f ≫
      CommRingCat.ofHom (algebraMap A p.asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso A p).inv := by
  let : p.asIdeal.IsPrime := p.isPrime
  apply Spec.map_injective
  simp only [pointBaseMap, Spec.map_comp, Spec.map_preimage]
  rw [Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]

/-- The inverse residue-field isomorphism carries the actual coefficient map to `pointBaseMap`.
@isnad1 id=eq.0h4v.s9.47596b48760b from=translated src=- shape=54dcc467 vocab=02b6b8f0
-/
theorem pointBaseMap_spec_algebraMap {k : Type u} [Field k]
    (A : CommRingCat.{u}) (f : Spec A ⟶ Spec (CommRingCat.of k)) (p : Spec A) :
    letI : p.asIdeal.IsPrime := p.isPrime
    letI : Algebra k A := (Spec.preimage f).hom.toAlgebra
    CommRingCat.ofHom (algebraMap k p.asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso A p).inv = pointBaseMap f p := by
  let : p.asIdeal.IsPrime := p.isPrime
  let : Algebra k A := (Spec.preimage f).hom.toAlgebra
  rw [IsScalarTower.algebraMap_eq k A p.asIdeal.ResidueField,
    CommRingCat.ofHom_comp, Category.assoc]
  exact (pointBaseMap_spec_eq A f p).symm

/-- Mathlib's affine residue-field isomorphism as an equivalence over the specified base field.-/
def specResidueFieldAlgEquiv {k : Type u} [Field k]
    (A : CommRingCat.{u}) (f : Spec A ⟶ Spec (CommRingCat.of k)) (p : Spec A) :
    letI : p.asIdeal.IsPrime := p.isPrime
    letI : Algebra k A := (Spec.preimage f).hom.toAlgebra
    letI : Algebra k ((Spec A).residueField p) := (pointBaseMap f p).hom.toAlgebra
    (Spec A).residueField p ≃ₐ[k] p.asIdeal.ResidueField := by
  letI : p.asIdeal.IsPrime := p.isPrime
  letI : Algebra k A := (Spec.preimage f).hom.toAlgebra
  letI : Algebra k ((Spec A).residueField p) := (pointBaseMap f p).hom.toAlgebra
  refine (AlgEquiv.ofRingEquiv
    (f := (Scheme.Spec.residueFieldIso A p).symm.commRingCatIsoToRingEquiv) ?_).symm
  intro t
  change (Scheme.Spec.residueFieldIso A p).inv.hom
      (algebraMap k p.asIdeal.ResidueField t) = (pointBaseMap f p).hom t
  exact congrArg (fun m : CommRingCat.of k ⟶ (Spec A).residueField p ↦ m.hom t)
    (pointBaseMap_spec_algebraMap A f p)

/-- The algebra equivalence has exactly the original residue-field isomorphism as its function.
@isnad1 id=eq.0h5v.s10.4dd68bf03bbc from=translated src=- shape=2a80d241 vocab=111093e1
-/
theorem specResidueFieldAlgEquiv_apply {k : Type u} [Field k]
    (A : CommRingCat.{u}) (f : Spec A ⟶ Spec (CommRingCat.of k)) (p : Spec A)
    (z : (Spec A).residueField p) :
    letI : p.asIdeal.IsPrime := p.isPrime
    letI : Algebra k A := (Spec.preimage f).hom.toAlgebra
    letI : Algebra k ((Spec A).residueField p) := (pointBaseMap f p).hom.toAlgebra
    specResidueFieldAlgEquiv A f p z = (Scheme.Spec.residueFieldIso A p).hom z := rfl

/-- The two actual affine residue fields have equal transcendence degree over the same base.
@isnad1 id=eq.0h4v.s8.b2ab8cce30d4 from=translated src=- shape=1f522e10 vocab=c4aeadea
-/
theorem specResidueField_trdeg_eq {k : Type u} [Field k]
    (A : CommRingCat.{u}) (f : Spec A ⟶ Spec (CommRingCat.of k)) (p : Spec A) :
    letI : p.asIdeal.IsPrime := p.isPrime
    letI : Algebra k A := (Spec.preimage f).hom.toAlgebra
    letI : Algebra k ((Spec A).residueField p) := (pointBaseMap f p).hom.toAlgebra
    Algebra.trdeg k ((Spec A).residueField p) = Algebra.trdeg k p.asIdeal.ResidueField := by
  let : p.asIdeal.IsPrime := p.isPrime
  let : Algebra k A := (Spec.preimage f).hom.toAlgebra
  let : Algebra k ((Spec A).residueField p) := (pointBaseMap f p).hom.toAlgebra
  exact (specResidueFieldAlgEquiv A f p).trdeg_eq

end AlgebraicGeometry.Intersection

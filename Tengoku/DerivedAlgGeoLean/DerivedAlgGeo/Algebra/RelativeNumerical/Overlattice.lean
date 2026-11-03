/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.Algebra.RelativeNumerical.Basic
import Tengoku.Seed.GroupTheory.Index

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Images and finite-index overlattices of additive-group maps

This file models an image by the canonical `AddMonoidHom.range`, records the
finite-index-overlattice predicate for two additive subgroups, and factors
family values through chosen image inclusions.  The terminology is motivated
by relative numerical K-theory, but the public API uses only additive groups
and homomorphisms; geometric base-change maps are consumers of this root.
-/

namespace DerivedAlgGeo.Algebra.RelativeNumerical

universe u v w

/-! ## Images and finite-index overlattices -/

variable {A B V : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup V]

/-- The image group determined by an additive map `η`.

This is an abbreviation for the existing additive-subgroup range, so all
subgroup, quotient, and finite-index API remains available without a parallel
lattice hierarchy.-/
abbrev EtaImage (eta : A →+ V) := eta.range

/-- A numerical class regarded as an element of the image of `ηᵛ`.-/
def etaClass (eta : A →+ V) : A →+ EtaImage eta :=
  eta.rangeRestrict

/--
@isnad1 id=eq.0h4v.s9.240e9c56188c from=translated src=- shape=53698507 vocab=7ee1e1c9
-/
@[simp]
theorem etaClass_coe (eta : A →+ V) (x : A) :
    (etaClass eta x : V) = eta x :=
  rfl

/-- `larger` is a finite-index overlattice of `base` inside their common
ambient additive group.  Containment and finite relative index are properties,
not fields on a new carrier.-/
def IsFiniteIndexOverlattice (base larger : AddSubgroup V) : Prop :=
  base ≤ larger ∧ base.IsFiniteRelIndex larger

/-- Transport a class through an additive map whose range lies in a chosen
second range.-/
def specializationMap (eta : A →+ V) (geometricEta : B →+ V)
    (h : eta.range ≤ geometricEta.range) : A →+ EtaImage geometricEta :=
  eta.codRestrict geometricEta.range fun x ↦ h ⟨x, rfl⟩

/--
@isnad1 id=eq.1h6v.s9.a8518c53e91b from=translated src=- shape=e15ba393 vocab=ebcc9b99
-/
@[simp]
theorem specializationMap_coe (eta : A →+ V) (geometricEta : B →+ V)
    (h : eta.range ≤ geometricEta.range) (x : A) :
    (specializationMap eta geometricEta h x : V) = eta x :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.3063790373c4 from=translated src=- shape=1d2b755d vocab=130b07cc
-/
theorem specializationMap_self (eta : A →+ V) :
    specializationMap eta eta le_rfl = etaClass eta := by
  ext x
  rfl

/-! ## Admissible families -/

namespace FamilyRelationSystem

variable {I : Type u} {K V₀ : I → Type v}
  [∀ i, AddCommGroup (K i)] [∀ i, AddCommGroup (V₀ i)]

/-- Construct a family relation system from indexed additive maps.

For each index `i`, `geometricEta i` presents the target group as an image in
`V₀ i`. At a point `t` of an admissible family, `eta F t` maps a source into
the same ambient group; `hEta` is precisely its factorization through the
chosen image. The resulting system is consumed by the saturated quotient in
`Basic`. Geometric applications may instantiate these parameters with
base-change maps, but no geometric vocabulary occurs in this root.-/
def ofEta
    (geometricEta : ∀ i, K i →+ V₀ i)
    (Family : Type w) (Point : Family → Type w)
    (index : ∀ F, Point F → I)
    (Source : ∀ F, Point F → Type v)
    [∀ F t, AddCommGroup (Source F t)]
    (eta : ∀ F t, Source F t →+ V₀ (index F t))
    (hEta : ∀ F t, (eta F t).range ≤ (geometricEta (index F t)).range)
    (classValue : ∀ F t, Source F t) :
    FamilyRelationSystem fun i ↦ EtaImage (geometricEta i) where
  Family := Family
  Point := Point
  index := index
  classValue := fun F t ↦
    specializationMap (eta F t) (geometricEta (index F t)) (hEta F t)
      (classValue F t)

/--
@isnad1 id=eq.1h12v.s11.7196a4ab081d from=translated src=- shape=27f91c9e vocab=8552156d
-/
@[simp]
theorem ofEta_classValue_coe
    (geometricEta : ∀ i, K i →+ V₀ i)
    (Family : Type w) (Point : Family → Type w)
    (index : ∀ F, Point F → I)
    (Source : ∀ F, Point F → Type v)
    [∀ F t, AddCommGroup (Source F t)]
    (eta : ∀ F t, Source F t →+ V₀ (index F t))
    (hEta : ∀ F t, (eta F t).range ≤ (geometricEta (index F t)).range)
    (classValue : ∀ F t, Source F t) (F : Family) (t : Point F) :
    ((ofEta geometricEta Family Point index Source eta hEta classValue).classValue F t).1 =
      eta F t (classValue F t) :=
  rfl

end FamilyRelationSystem

/-! ## Boundary tests -/

/-- For the identity base-change map, the image construction recovers the
original additive group.-/
def etaImageIdEquiv (A : Type*) [AddCommGroup A] :
    EtaImage (AddMonoidHom.id A) ≃+ A where
  toFun x := x.1
  invFun := etaClass (AddMonoidHom.id A)
  left_inv x := by
    ext
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/--
@isnad1 id=eq.0h2v.s9.559e954017cd from=translated src=- shape=b988c9e5 vocab=86d1c866
-/
@[simp]
theorem etaImageIdEquiv_etaClass (A : Type*) [AddCommGroup A] (x : A) :
    etaImageIdEquiv A (etaClass (AddMonoidHom.id A) x) = x :=
  rfl

end DerivedAlgGeo.Algebra.RelativeNumerical

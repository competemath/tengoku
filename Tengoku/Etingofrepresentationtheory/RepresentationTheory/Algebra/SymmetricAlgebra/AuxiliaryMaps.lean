/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Tengoku.Etingofrepresentationtheory.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis
import Tengoku.Seed.Data.Finsupp.Order

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option backward.isDefEq.respectTransparency false

universe u v w

open scoped TensorProduct

namespace RepresentationTheory.Algebra.SymmetricAlgebra.AuxiliaryMaps

variable {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V] [Module k V]

section Exponent

variable {κ : Type w}

/-- If a coefficient is at least one, subtracting and then adding its unit singleton recovers the finitely supported function.
@isnad1 id=eq.1h3v.s7.f152d1658e4f from=translated src=- shape=4b960c4f vocab=2be3bae9
-/
theorem Finsupp.sub_single_add_single {α : κ →₀ ℕ} {a : κ} (h : 1 ≤ α a) :
    α - Finsupp.single a 1 + Finsupp.single a 1 = α := by
  ext x
  rcases eq_or_ne a x with rfl | hne
  · simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega
  · have h0 : (Finsupp.single a (1 : ℕ)) x = 0 := Finsupp.single_eq_of_ne hne.symm
    simp only [Finsupp.add_apply, Finsupp.tsub_apply]
    omega

/-- Under positivity at the subtracted index, adding one singleton commutes with subtracting another singleton.
@isnad1 id=eq.1h4v.s7.b9f2c677c484 from=translated src=- shape=aa1e39f7 vocab=2be3bae9
-/
theorem Finsupp.sub_single_add_single_comm {α : κ →₀ ℕ} {p a : κ} (h : 1 ≤ α p) :
    α - Finsupp.single p 1 + Finsupp.single a 1 =
      α + Finsupp.single a 1 - Finsupp.single p 1 := by
  ext x
  rcases eq_or_ne p x with rfl | hne
  · rcases eq_or_ne a p with rfl | hne'
    · simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    · have h0 : (Finsupp.single a (1 : ℕ)) p = 0 := Finsupp.single_eq_of_ne hne'.symm
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
  · have h0 : (Finsupp.single p (1 : ℕ)) x = 0 := Finsupp.single_eq_of_ne hne.symm
    simp only [Finsupp.add_apply, Finsupp.tsub_apply]
    omega

/-- Adding and then subtracting the same unit singleton leaves a natural-valued finitely supported function unchanged.
@isnad1 id=eq.0h3v.s6.5ebeb21b99e0 from=translated src=- shape=e8d4c3b2 vocab=b608eeeb
-/
theorem Finsupp.add_single_sub_single {α : κ →₀ ℕ} {a : κ} :
    α + Finsupp.single a 1 - Finsupp.single a 1 = α := by
  ext x
  simp only [Finsupp.add_apply, Finsupp.tsub_apply]
  omega

/-- An index belongs to the support after adding a unit singleton exactly when it is the singleton index or belonged to the original support.
@isnad1 id=iff.0h4v.s6.a97ef5d4b4ba from=translated src=- shape=99511bfb vocab=04adee25
-/
theorem Finsupp.mem_support_add_single {α : κ →₀ ℕ} {a m : κ} :
    m ∈ (α + Finsupp.single a 1).support ↔ m = a ∨ m ∈ α.support := by
  rcases eq_or_ne m a with rfl | hne
  · simp [Finsupp.mem_support_iff, Finsupp.add_apply]
  · simp [Finsupp.mem_support_iff, Finsupp.add_apply, hne]

end Exponent

section Insert

variable {κ : Type w} [DecidableEq κ]

/-- Adjoin an absent element to a subset of fixed finite cardinality, producing a subset whose cardinality is one larger.-/
def Set.PowersetCard.insert {i : ℕ} (s : Set.powersetCard κ i) {a : κ} (ha : a ∉ (s : Finset κ)) :
    Set.powersetCard κ (i + 1) :=
  ⟨Insert.insert a (s : Finset κ), Set.powersetCard.mem_iff.mpr (by
    rw [Finset.card_insert_of_notMem ha, Set.powersetCard.card_eq])⟩

/-- The underlying set obtained by adjoining a fresh element to a fixed-cardinality subset is its set insertion.
@isnad1 id=eq.1h4v.s6.d099b60fab23 from=translated src=- shape=475dff51 vocab=c0478f26
-/
@[simp]
theorem Set.PowersetCard.coe_insert {i : ℕ} (s : Set.powersetCard κ i) {a : κ} (ha : a ∉ (s : Finset κ)) :
    (Set.PowersetCard.insert s ha : Finset κ) = Insert.insert a (s : Finset κ) := rfl

end Insert

section Position

variable {κ : Type w} [LinearOrder κ] [DecidableEq κ]

/-- Under the displayed order hypothesis, the shown natural-valued function has value zero at the inserted element.
@isnad1 id=eq.1h3v.s6.bfbda0585413 from=translated src=- shape=1b0c7092 vocab=a166707d
-/
theorem Finset.auxiliaryNatFunction_insert_self_of_lt {s : Finset κ} {p : κ} (hp : ∀ c ∈ s, p < c) :
    _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank (insert p s) p = 0 := by
  rw [_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact lt_irrefl _
  · exact not_lt.mpr (hp x hx).le

/-- Under the displayed order hypothesis, the shown natural-valued function increases by one on each original member after insertion.
@isnad1 id=eq.2h4v.s6.24365879f50b from=translated src=- shape=59346166 vocab=88e76aa0
-/
theorem Finset.auxiliaryNatFunction_insert_of_lt {s : Finset κ} {p c : κ} (hp : ∀ c' ∈ s, p < c') (hc : c ∈ s) :
    _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank (insert p s) c = _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank s c + 1 := by
  have hpn : p ∉ s := fun h => absurd (hp p h) (lt_irrefl p)
  have hfil : (insert p s).filter (· < c) = insert p (s.filter (· < c)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hx | hx, hlt⟩
      · exact Or.inl hx
      · exact Or.inr ⟨hx, hlt⟩
    · rintro (rfl | ⟨hx, hlt⟩)
      · exact ⟨Or.inl rfl, hp c hc⟩
      · exact ⟨Or.inr hx, hlt⟩
  rw [_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank, hfil, Finset.card_insert_of_notMem fun h => hpn (Finset.mem_filter.mp h).1,
    _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank]

omit [DecidableEq κ] in

/-- The shown natural-valued function has value zero at the minimum of a nonempty finite set.
@isnad1 id=eq.1h2v.s4.2c98b3b2e62e from=translated src=- shape=99a329a1 vocab=78a8054d
-/
theorem Finset.auxiliaryNatFunction_min' {s : Finset κ} (h : s.Nonempty) : _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank s (s.min' h) = 0 := by
  rw [_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun x hx => not_lt.mpr (s.min'_le x hx)

end Position

section Pivot

variable {κ : Type w} [LinearOrder κ] [DecidableEq κ]

/-- A predicate on a finitely supported natural-valued function, a finite set, and an index.-/
def Finsupp.IndexPredicate (α : κ →₀ ℕ) (s : Finset κ) (a : κ) : Prop :=
  a ∈ α.support ∧ (∀ m ∈ α.support, a ≤ m) ∧ ∀ c ∈ s, a < c

/-- The displayed predicate for a natural-valued finitely supported function and finite set is decidable.-/
instance Finsupp.decidablePredIndexPredicate (α : κ →₀ ℕ) (s : Finset κ) : DecidablePred (Finsupp.IndexPredicate α s) := fun a => by
  unfold Finsupp.IndexPredicate; infer_instance

omit [DecidableEq κ] in
/-- An index satisfying the predicate lies outside the given finite set.
@isnad1 id=not.1h4v.s5.425fe4fbe11a from=translated src=- shape=f7345e71 vocab=d0636775
-/
theorem Finsupp.IndexPredicate.not_mem {α : κ →₀ ℕ} {s : Finset κ} {a : κ} (h : Finsupp.IndexPredicate α s a) :
    a ∉ s := fun ha => absurd (h.2.2 a ha) (lt_irrefl a)

omit [DecidableEq κ] in

/-- Any two indices satisfying the predicate for the same function and finite set are equal.
@isnad1 id=eq.2h5v.s5.da62d96f7134 from=translated src=- shape=9e6112b6 vocab=2fde7ef9
-/
theorem Finsupp.IndexPredicate.eq {α : κ →₀ ℕ} {s : Finset κ} {a a' : κ} (h : Finsupp.IndexPredicate α s a)
    (h' : Finsupp.IndexPredicate α s a') : a = a' :=
  le_antisymm (h.2.1 a' h'.1) (h'.2.1 a h.1)

omit [DecidableEq κ] in
/-- The coefficient at an index satisfying the predicate is at least one.
@isnad1 id=le.1h4v.s5.9fd62779ffb4 from=translated src=- shape=168f99d2 vocab=9f0b0fb6
-/
theorem Finsupp.IndexPredicate.one_le {α : κ →₀ ℕ} {s : Finset κ} {a : κ} (h : Finsupp.IndexPredicate α s a) :
    1 ≤ α a :=
  Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp h.1)

end Pivot

section Homotopy

variable {κ : Type w} [LinearOrder κ] [DecidableEq κ]

/-- A basis-dependent value in the displayed module at a successor index, determined by a finitely supported function and fixed-cardinality subset.-/
noncomputable def Module.Basis.pairToSucc (b : Module.Basis κ k V) (i : ℕ)
    (P : (κ →₀ ℕ) × Set.powersetCard κ i) : _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V (i + 1) :=
  ∑ a ∈ P.1.support,
    if h : Finsupp.IndexPredicate P.1 (P.2 : Finset κ) a then
      -_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor k V b (i + 1) (P.1 - Finsupp.single a 1, Set.PowersetCard.insert P.2 h.not_mem)
    else 0

/-- A basis-dependent linear map from the displayed module at an index to the displayed module at its successor.-/
noncomputable def Module.Basis.linearMapToSucc (b : Module.Basis κ k V) (i : ℕ) :
    _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i →ₗ[k] _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V (i + 1) :=
  (_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor k V b i).constr k (Module.Basis.pairToSucc b i)

/-- The displayed linear map applied to the given pair equals the displayed basis-dependent value.
@isnad1 id=eq.0h6v.s13.966791eb8b19 from=translated src=- shape=6c9285c0 vocab=e6f8d752
-/
@[simp]
theorem Module.Basis.linearMapToSucc_apply_pair (b : Module.Basis κ k V) (i : ℕ)
    (P : (κ →₀ ℕ) × Set.powersetCard κ i) :
    Module.Basis.linearMapToSucc b i (_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor k V b i P) = Module.Basis.pairToSucc b i P :=
  Module.Basis.constr_basis _ _ _ _

/-- The scalar actions of the base ring and its symmetric algebra on the displayed third module form a scalar tower.
@isnad1 id=isscalar.0h2v.s9.a34285371f31 from=translated src=- shape=828b4cc5 vocab=7aa1d38c
-/
instance instIsScalarTowerSymmetricAlgebraAuxiliary : IsScalarTower k (SymmetricAlgebra k V) (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V) where
  smul_assoc c s x := by
    apply (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V).injective
    have h1 : _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V ((c • s) • x) =
        SymmetricAlgebra.algebraMapInv (c • s) * _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V x :=
      _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing_smul _ _
    have h2 : _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V (c • (s • x)) =
        c • _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V (s • x) := map_smul _ _ _
    rw [h1, h2, _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_assoc]

variable (k V) in

/-- A linear map from the displayed source module to the displayed module at index zero.-/
noncomputable def auxiliaryLinearMapToIndexZero : _root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero k V →ₗ[k] _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V 0 :=
  ((TensorProduct.mk k (SymmetricAlgebra k V) (⋀[k]^0 V)).flip
      ((exteriorPower.zeroEquiv k V).symm 1)).comp
    ((Algebra.linearMap k (SymmetricAlgebra k V)).comp
      (_root_.RepresentationTheory.LinearAlgebra.ExteriorPower.DegreeZero.degreeZero.equivBaseRing k V).toLinearMap)

/-- An auxiliary value determined by a basis, an index, a finitely supported function, a fixed-cardinality subset, and an element.-/
noncomputable def Module.Basis.auxiliaryTerm (b : Module.Basis κ k V) (i : ℕ) (α : κ →₀ ℕ)
    (s : Set.powersetCard κ (i + 1)) (a : κ) : _root_.RepresentationTheory.Algebra.Homology.BasisSymmetricAlgebraComplex.degreeIndexedType k V i :=
  if h : a ∈ (s : Finset κ) then
    ((-1 : k) ^ (_root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Finset.rank (s : Finset κ) a + 1)) •
      _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.Module.Basis.symmetricExteriorTensor k V b i (α + Finsupp.single a 1, _root_.RepresentationTheory.LinearAlgebra.SymmetricExteriorBasis.erase s ⟨a, h⟩)
  else 0

variable [Fintype κ]

end Homotopy

end RepresentationTheory.Algebra.SymmetricAlgebra.AuxiliaryMaps

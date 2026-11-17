/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Uniformization.PartialBorel
import Tengoku.Seed.Topology.Maps.Proper.Basic
import Tengoku.Seed.Topology.MetricSpace.PiNat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Closed projections over compact codomains

If the second coordinate is compact, the first projection is a closed map.  Consequently the
domain of a closed relation is closed (and hence Borel whenever the first topology generates its
measurable space).  This module also records exact section-hit semantics and Cantor-cylinder
approximations that recover a closed section pointwise.

The compactness assumption here is global: the entire codomain is compact.  In particular, this
module does **not** prove the substantially stronger theorem that a Borel relation with merely
pointwise compact vertical sections has Borel projection.
-/

open MeasurableSpace Set

universe u v

namespace DescriptiveSetTheory

variable {X : Type u} {Y : Type v}

/-- First coordinates whose vertical section meets `t`.-/
def sectionHit (R : Set (X × Y)) (t : Set Y) : Set X :=
  relationDomain (R ∩ (univ ×ˢ t))

/--
@isnad1 id=iff.0h5v.s5.a00b43949594 from=translated src=- shape=ea8f4aee vocab=ee722a72
-/
@[simp] theorem mem_sectionHit {R : Set (X × Y)} {t : Set Y} {x : X} :
    x ∈ sectionHit R t ↔ (verticalSection R x ∩ t).Nonempty := by
  constructor
  · rintro ⟨y, hR, -, ht⟩
    exact ⟨y, hR, ht⟩
  · rintro ⟨y, hR, ht⟩
    exact ⟨y, hR, mem_univ y, ht⟩

/-- A relation domain is exactly the image under the first projection.
@isnad1 id=eq.0h3v.s4.4f55af14694e from=translated src=- shape=2516cb29 vocab=af89e0b7
-/
theorem relationDomain_eq_fst_image (R : Set (X × Y)) :
    relationDomain R = Prod.fst '' R := by
  ext x
  constructor
  · rintro ⟨y, hxy⟩
    exact ⟨(x, y), hxy, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, hp⟩

/-- A closed relation over a compact codomain has closed domain.
@isnad1 id=isclosed.1h3v.s5.fbe61b1ff209 from=translated src=- shape=cd7de622 vocab=22445d06
-/
theorem IsClosed.isClosed_relationDomain_of_compactCodomain
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    {R : Set (X × Y)} (hR : IsClosed R) : IsClosed (relationDomain R) := by
  rw [relationDomain_eq_fst_image]
  exact isClosedMap_fst_of_compactSpace R hR

/-- Intersecting the second coordinate with a closed set preserves closed section-hit sets.
@isnad1 id=isclosed.2h4v.s5.fdf9466bc406 from=translated src=- shape=0d745e22 vocab=3af46f88
-/
theorem IsClosed.isClosed_sectionHit_of_compactCodomain
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    {R : Set (X × Y)} (hR : IsClosed R) {t : Set Y} (ht : IsClosed t) :
    IsClosed (sectionHit R t) := by
  apply DescriptiveSetTheory.IsClosed.isClosed_relationDomain_of_compactCodomain
  exact hR.inter (isClosed_univ.prod ht)

/-- The closed projection is Borel when the first measurable space is its Borel space.
@isnad1 id=measurab.1h3v.s5.9d00b9499203 from=translated src=- shape=4d42357f vocab=88d82413
-/
theorem IsClosed.measurableSet_relationDomain_of_compactCodomain
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [CompactSpace Y]
    {R : Set (X × Y)} (hR : IsClosed R) : MeasurableSet (relationDomain R) :=
  (DescriptiveSetTheory.IsClosed.isClosed_relationDomain_of_compactCodomain hR).measurableSet

/-- A closed compact-codomain projection has an exact standard-Borel code.
@isnad1 id=ex.1h3v.s6.0ab8651ace9c from=translated src=- shape=4f479ee9 vocab=42ee2b6d
-/
theorem IsClosed.exists_standardBorelCode_relationDomain_of_compactCodomain
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace Y] [CompactSpace Y]
    {R : Set (X × Y)} (hR : IsClosed R) :
    ∃ c : StandardBorelCode X, c.eval = relationDomain R :=
  StandardBorelCode.exists_code
    (DescriptiveSetTheory.IsClosed.measurableSet_relationDomain_of_compactCodomain hR)

/-- Cylinders in Cantor space are closed as well as open.
@isnad1 id=isclosed.0h2v.s4.8be2230fd825 from=translated src=- shape=35fede8f vocab=b1be2f60
-/
theorem isClosed_cantorCylinder (p : ℕ → Bool) (n : ℕ) :
    IsClosed (PiNat.cylinder p n) := by
  rw [PiNat.cylinder_eq_pi]
  exact isClosed_set_pi fun i _ => isClosed_discrete {p i}

/-- The closed set of first coordinates whose section meets a fixed Cantor cylinder.-/
def cantorSectionHit (R : Set (X × (ℕ → Bool))) (p : ℕ → Bool) (n : ℕ) : Set X :=
  sectionHit R (PiNat.cylinder p n)

/--
@isnad1 id=iff.0h5v.s5.f19763eea31c from=translated src=- shape=ca804241 vocab=0e197e6c
-/
@[simp] theorem mem_cantorSectionHit {R : Set (X × (ℕ → Bool))}
    {p : ℕ → Bool} {n : ℕ} {x : X} :
    x ∈ cantorSectionHit R p n ↔
      (verticalSection R x ∩ PiNat.cylinder p n).Nonempty :=
  mem_sectionHit

/--
@isnad1 id=isclosed.1h4v.s5.682876bc783b from=translated src=- shape=68a43c06 vocab=ea99165c
-/
theorem IsClosed.isClosed_cantorSectionHit [TopologicalSpace X]
    {R : Set (X × (ℕ → Bool))} (hR : IsClosed R) (p : ℕ → Bool) (n : ℕ) :
    IsClosed (cantorSectionHit R p n) :=
  DescriptiveSetTheory.IsClosed.isClosed_sectionHit_of_compactCodomain hR
    (isClosed_cantorCylinder p n)

/-- Cylinder-hit approximations shrink with the prefix length.
@isnad1 id=le.1h5v.s5.354767d8e13f from=translated src=- shape=5c3719eb vocab=228851c5
-/
theorem cantorSectionHit_anti (R : Set (X × (ℕ → Bool))) (p : ℕ → Bool)
    {m n : ℕ} (hmn : m ≤ n) : cantorSectionHit R p n ⊆ cantorSectionHit R p m := by
  intro x hx
  rw [mem_cantorSectionHit] at hx ⊢
  obtain ⟨y, hyR, hyc⟩ := hx
  exact ⟨y, hyR, PiNat.cylinder_anti p hmn hyc⟩

/-- The zero-length approximation is exactly the relation domain.
@isnad1 id=eq.0h3v.s4.09ebc1d09ba6 from=translated src=- shape=298f34c4 vocab=de2a727b
-/
@[simp] theorem cantorSectionHit_zero (R : Set (X × (ℕ → Bool))) (p : ℕ → Bool) :
    cantorSectionHit R p 0 = relationDomain R := by
  ext x
  simp [cantorSectionHit, sectionHit]

/-- A point belongs to a closed Cantor section exactly when every cylinder around it meets that
section.  This is the exact limit equation behind the cylinder approximations.
@isnad1 id=iff.1h4v.s6.d94ebe4f5d7f from=translated src=- shape=199f53a0 vocab=9fef0924
-/
theorem IsClosed.mem_verticalSection_iff_forall_mem_cantorSectionHit
    [TopologicalSpace X] {R : Set (X × (ℕ → Bool))} (hR : IsClosed R)
    (x : X) (p : ℕ → Bool) :
    p ∈ DescriptiveSetTheory.verticalSection R x ↔
      ∀ n, x ∈ cantorSectionHit R p n := by
  constructor
  · intro hp n
    rw [mem_cantorSectionHit]
    exact ⟨p, hp, PiNat.self_mem_cylinder p n⟩
  · intro hp
    have hpClosure : p ∈ closure (DescriptiveSetTheory.verticalSection R x) := by
      refine (PiNat.isTopologicalBasis_cylinders fun _ : ℕ => Bool).mem_closure_iff.mpr ?_
      intro o ho hpo
      rcases ho with ⟨z, n, rfl⟩
      have hpn := hp n
      rw [mem_cantorSectionHit] at hpn
      obtain ⟨y, hyR, hyc⟩ := hpn
      refine ⟨y, ?_, hyR⟩
      rw [PiNat.mem_cylinder_iff] at hpo hyc ⊢
      intro i hi
      exact (hyc i hi).trans (hpo i hi)
    rw [(DescriptiveSetTheory.IsClosed.verticalSection hR x).closure_eq] at hpClosure
    exact hpClosure

end DescriptiveSetTheory

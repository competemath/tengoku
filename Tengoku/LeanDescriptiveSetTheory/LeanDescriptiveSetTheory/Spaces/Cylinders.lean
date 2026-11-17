/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.CountableBasis
import Tengoku.Seed.Topology.MetricSpace.PiNat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Countable cylinder bases for Baire and Cantor space

Mathlib's `PiNat.cylinder x n` is the set of sequences agreeing with `x` on the first `n`
coordinates, and mathlib proves that these cylinders form a basis for a countable product of
discrete spaces. Although the displayed center `x` ranges over an often uncountable function space,
each cylinder is determined by the finite list `PiNat.res x n`.

This file packages that observation as a countable basis family. It supplies an encodable type of
basic opens and a natural-number sequence whose range is exactly the cylinder family. The Baire
space `ℕ → ℕ` and Cantor space `ℕ → Bool` specializations can therefore use the existing
`CountableBasisCode` API without introducing a second code tree.
-/

open Set TopologicalSpace

universe u

namespace DescriptiveSetTheory

/-- The family of finite-prefix cylinders in the sequence space `ℕ → α`.-/
def cylinderBasis (α : Type u) : Set (Set (ℕ → α)) :=
  {s | ∃ x : ℕ → α, ∃ n : ℕ, s = PiNat.cylinder x n}

/-- Cylinders form a topological basis when the coordinate space is discrete.
@isnad1 id=istopolo.0h1v.s4.7923b7d193cc from=translated src=- shape=444e245f vocab=f11f994d
-/
theorem isTopologicalBasis_cylinderBasis (α : Type u) [TopologicalSpace α]
    [DiscreteTopology α] : IsTopologicalBasis (cylinderBasis α) := by
  exact PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => α)

/-- The cylinder family is countable when the coordinate type is countable.
@isnad1 id=countabl.0h1v.s3.09948e25db4c from=translated src=- shape=13077133 vocab=f0c7474e
-/
theorem countable_cylinderBasis (α : Type u) [Countable α] :
    (cylinderBasis α).Countable := by
  apply (Set.countable_range fun p : List α => {y | PiNat.res y p.length = p}).mono
  rintro s ⟨x, n, rfl⟩
  refine ⟨PiNat.res x n, ?_⟩
  change {y | PiNat.res y (PiNat.res x n).length = PiNat.res x n} = PiNat.cylinder x n
  rw [PiNat.res_length]
  exact (PiNat.cylinder_eq_res x n).symm

/-- An encodable basic-open code for a finite-prefix cylinder.-/
abbrev CylinderBasicOpen (α : Type u) := cylinderBasis α

/-- Cylinder basic opens inherit an encoding from the countability proof.-/
noncomputable instance instEncodableCylinderBasicOpen (α : Type u) [Countable α] :
    Encodable (CylinderBasicOpen α) :=
  (countable_cylinderBasis α).toEncodable

/-- The whole sequence space is the cylinder of length zero.
@isnad1 id=mem.0h1v.s4.ba6aaf6894ad from=translated src=- shape=c5ea64c0 vocab=cddd15f0
-/
theorem univ_mem_cylinderBasis (α : Type u) [Nonempty α] :
    (Set.univ : Set (ℕ → α)) ∈ cylinderBasis α :=
  ⟨fun _ => Classical.choice inferInstance, 0, (PiNat.cylinder_zero _).symm⟩

/-- A natural-number enumeration whose range is exactly the cylinder family.-/
noncomputable def cylinderBasisSequence (α : Type u) [Countable α] :
    ℕ → Set (ℕ → α) :=
  Set.enumerateCountable (countable_cylinderBasis α) Set.univ

/-- The cylinder-basis sequence enumerates every cylinder and no other set.
@isnad1 id=eq.0h1v.s4.3f23477cd314 from=translated src=- shape=4ed23cea vocab=daacb2fc
-/
theorem range_cylinderBasisSequence (α : Type u) [Countable α] [Nonempty α] :
    Set.range (cylinderBasisSequence α) = cylinderBasis α :=
  Set.range_enumerateCountable_of_mem (countable_cylinderBasis α)
    (univ_mem_cylinderBasis α)

/-- The enumerated cylinders form a natural-number-indexed topological basis.
@isnad1 id=istopolo.0h1v.s5.202d36a03741 from=translated src=- shape=05891d69 vocab=7be20077
-/
theorem isTopologicalBasis_range_cylinderBasisSequence (α : Type u) [Countable α]
    [Nonempty α] [TopologicalSpace α] [DiscreteTopology α] :
    IsTopologicalBasis (Set.range (cylinderBasisSequence α)) := by
  rw [range_cylinderBasisSequence]
  exact isTopologicalBasis_cylinderBasis α

/-- Borel codes whose leaves are the enumerated cylinders in `ℕ → α`.-/
abbrev CylinderBorelCode (α : Type u) [Countable α] :=
  CountableBasisCode (cylinderBasisSequence α)

/-- The finite-prefix cylinder basis for Baire space `ℕ → ℕ`.-/
def baireCylinderBasis : Set (Set (ℕ → ℕ)) := cylinderBasis ℕ

/-- The finite-prefix cylinder basis for Cantor space `ℕ → Bool`.-/
def cantorCylinderBasis : Set (Set (ℕ → Bool)) := cylinderBasis Bool

/-- A natural-number enumeration of the Baire-space cylinder basis.-/
noncomputable def baireCylinderBasisSequence : ℕ → Set (ℕ → ℕ) :=
  cylinderBasisSequence ℕ

/-- A natural-number enumeration of the Cantor-space cylinder basis.-/
noncomputable def cantorCylinderBasisSequence : ℕ → Set (ℕ → Bool) :=
  cylinderBasisSequence Bool

/-- Borel codes over the explicit Baire-space cylinder basis.-/
abbrev BaireBorelCode := CylinderBorelCode ℕ

/-- Borel codes over the explicit Cantor-space cylinder basis.-/
abbrev CantorBorelCode := CylinderBorelCode Bool

/-- The Cantor-space cylinders form a topological basis.
@isnad1 id=istopolo.0h0v.s3.d178855526c3 from=translated src=- shape=67086572 vocab=ce964b13
-/
theorem isTopologicalBasis_cantorCylinderBasis :
    IsTopologicalBasis cantorCylinderBasis :=
  isTopologicalBasis_cylinderBasis Bool

/-- The Cantor-space cylinder family is countable.
@isnad1 id=countabl.0h0v.s2.b652cce78fe6 from=translated src=- shape=5d89a3b7 vocab=2ced0314
-/
theorem countable_cantorCylinderBasis : cantorCylinderBasis.Countable :=
  countable_cylinderBasis Bool

/-- The natural-number-indexed Baire cylinders form a topological basis.
@isnad1 id=istopolo.0h0v.s4.e5d97972a70e from=translated src=- shape=fd4d5e0a vocab=152d5c12
-/
theorem isTopologicalBasis_range_baireCylinderBasisSequence :
    IsTopologicalBasis (Set.range baireCylinderBasisSequence) :=
  isTopologicalBasis_range_cylinderBasisSequence ℕ

/-- The natural-number-indexed Cantor cylinders form a topological basis.
@isnad1 id=istopolo.0h0v.s4.d188b1d7b1b8 from=translated src=- shape=45c2f459 vocab=b1f66ed5
-/
theorem isTopologicalBasis_range_cantorCylinderBasisSequence :
    IsTopologicalBasis (Set.range cantorCylinderBasisSequence) :=
  isTopologicalBasis_range_cylinderBasisSequence Bool

end DescriptiveSetTheory

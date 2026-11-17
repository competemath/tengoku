/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.Linear.PerfectPairing
public import Tengoku.Seed.Algebra.Algebra.Bilinear

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Commutative Frobenius algebras

The primitive datum is a Frobenius functional `counit : A -> R`. Its trace
pairing is required to be perfect; symmetry and Frobenius invariance are
derived theorems.

## Design choice

We store only the counit and the proof of perfectness. The pairing is derived
as `η(a, b) = counit (a * b)`. Commutativity of `A` then proves symmetry, and
associativity of multiplication proves Frobenius invariance. Storing all of
these facts independently would introduce redundant data.

The notation `A →ₗ[R] R` means an `R`-linear functional. The notation
`LinearMap.BilinForm R A` means an `R`-bilinear form `A × A → R`, represented
in Lean as a linear map returning another linear map.
-/

@[expose] public section

namespace AxiomaticGW

/-- The bilinear trace pairing associated to a linear functional.

Mathlib's `LinearMap.mul R A` is multiplication viewed as a bilinear map.
`compr₂ counit` composes its output with the counit, producing
`(a, b) ↦ counit (a * b)`.-/
def tracePairing {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (counit : A →ₗ[R] R) : LinearMap.BilinForm R A :=
  (LinearMap.mul R A).compr₂ counit

/-- The trace pairing evaluates to its intended mathematical formula. This is
true by definition, so the proof is `rfl` (reflexivity).
@isnad1 id=eq.0h5v.s9.70eeb4a11bec from=translated src=- shape=cbdeeffe vocab=19beb76f
-/
@[simp]
theorem tracePairing_apply {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (counit : A →ₗ[R] R) (a b : A) :
    tracePairing counit a b = counit (a * b) := rfl

/-- A commutative Frobenius algebra, presented by its Frobenius functional.

There are only two fields: the functional and perfectness of its trace
pairing. Notice that the assumption that `A` is finite free over `R` is not
built into this structure. It is required later only for constructions, such
as the copairing, that use a finite tensor--Hom equivalence.-/
structure CommFrobeniusAlgebra (R A : Type*) [CommRing R] [CommRing A]
    [Algebra R A] where
  /-- The Frobenius functional, also used as the coalgebra counit.-/
  counit : A →ₗ[R] R
  /-- A proof that the trace pairing induced by `counit` is perfect.-/
  isPerfPair : (tracePairing counit).IsPerfPair

namespace CommFrobeniusAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Two Frobenius structures are equal when their counits are equal. The
remaining fields are proofs, and Lean's proof irrelevance says that two proofs
of the same proposition do not create different structures.

`@[ext]` registers this as an extensionality theorem for later proofs.
@isnad1 id=eq.1h4v.s6.41d47f501f9d from=translated src=- shape=9d06797b vocab=be33cb4a
-/
@[ext]
theorem ext {F G : CommFrobeniusAlgebra R A} (h : F.counit = G.counit) : F = G := by
  cases F
  cases G
  simp_all only

/-- The symmetric perfect pairing underlying a commutative Frobenius
algebra.

The `where` block constructs the three fields of
`SymmetricPerfectPairing`. Symmetry follows from commutativity; perfectness is
exactly the proof stored in `F`.-/
def pairing (F : CommFrobeniusAlgebra R A) : SymmetricPerfectPairing R A where
  form := tracePairing F.counit
  isSymm := ⟨fun a b ↦ by simp only [tracePairing_apply, mul_comm]⟩
  isPerfPair := F.isPerfPair

/-- Evaluation formula for the pairing derived from a Frobenius algebra.
@isnad1 id=eq.0h5v.s9.6ff685792f64 from=translated src=- shape=151819e3 vocab=77a688b3
-/
@[simp]
theorem pairing_apply (F : CommFrobeniusAlgebra R A) (a b : A) :
    F.pairing.form a b = F.counit (a * b) := rfl

/-- A named accessor for symmetry of the derived pairing.
@isnad1 id=issymm.0h3v.s6.3f0119f22793 from=translated src=- shape=434ac00d vocab=541ef199
-/
theorem pairing_isSymm (F : CommFrobeniusAlgebra R A) :
    F.pairing.form.IsSymm := F.pairing.isSymm

/-- Frobenius invariance of the trace pairing:
`η(a * b, c) = η(a, b * c)`. After expanding `pairing_apply`, the result is
exactly associativity of multiplication.
@isnad1 id=eq.0h6v.s9.e6f855447985 from=translated src=- shape=d93c6768 vocab=23aabe0d
-/
theorem pairing_assoc (F : CommFrobeniusAlgebra R A) (a b c : A) :
    F.pairing.form (a * b) c = F.pairing.form a (b * c) := by
  simp only [pairing_apply, mul_assoc]

end CommFrobeniusAlgebra

end AxiomaticGW

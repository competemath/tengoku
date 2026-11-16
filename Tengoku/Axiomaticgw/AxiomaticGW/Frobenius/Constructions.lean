/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.Frobenius.Basic
public import Tengoku.Axiomaticgw.AxiomaticGW.Linear.Copairing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Constructions from commutative Frobenius algebras

This file contains the reverse passage from an invariant pairing to a counit,
followed by the finite-free tensors used in two-dimensional TFT formulas.

In a theorem statement, `∀ a b c : A, ...` means "for every `a`, `b`, and
`c` in `A`".  A proof introduced by `by` is tactic-style Lean code: each line
transforms the current goal until no goals remain.
-/

@[expose] public section

namespace AxiomaticGW

open TensorProduct

namespace CommFrobeniusAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Construct a Frobenius algebra from an invariant perfect pairing.

The input `invariant` is the equation
`form (a * b) c = form a (b * c)`. The counit is recovered by
`counit a = form a 1`.-/
def ofInvariantPairing (form : LinearMap.BilinForm R A)
    (isPerfPair : form.IsPerfPair)
    (invariant : ∀ a b c : A, form (a * b) c = form a (b * c)) :
    CommFrobeniusAlgebra R A where
  -- `form.flip 1` is the linear functional `a ↦ form a 1`.
  counit := form.flip 1
  isPerfPair := by
    -- First prove that the trace pairing produced by this counit is exactly
    -- the original form.  Invariance with `c = 1` is the key calculation.
    have hform : tracePairing (form.flip 1) = form := by
      ext a b
      simpa only [tracePairing_apply, LinearMap.BilinForm.flip_apply, mul_one]
        using invariant a b 1
    -- Rewrite the goal using that equality, then reuse the assumed
    -- perfectness of `form`.
    rw [hform]
    exact isPerfPair

/-- Evaluation formula for the counit constructed from an invariant pairing.-/
@[simp]
theorem ofInvariantPairing_counit (form : LinearMap.BilinForm R A)
    (isPerfPair : form.IsPerfPair)
    (invariant : ∀ a b c : A, form (a * b) c = form a (b * c)) (a : A) :
    (ofInvariantPairing form isPerfPair invariant).counit a = form a 1 := rfl

/-- The construction really recovers the supplied pairing, rather than merely
an isomorphic pairing.-/
@[simp]
theorem pairing_ofInvariantPairing (form : LinearMap.BilinForm R A)
    (isPerfPair : form.IsPerfPair)
    (invariant : ∀ a b c : A, form (a * b) c = form a (b * c)) :
    (ofInvariantPairing form isPerfPair invariant).pairing.form = form := by
  ext a b
  simpa only [pairing_apply, ofInvariantPairing_counit, mul_one]
    using invariant a b 1

section FiniteFree

/- The remaining definitions use finite-free duality.  Keeping the hypotheses
inside this section means that the basic Frobenius structure itself remains
usable without them. -/
variable [Module.Free R A] [Module.Finite R A]

/-- The Casimir tensor of a Frobenius algebra.  This is simply the generic
copairing of its derived symmetric perfect pairing, given a Frobenius-specific
name.-/
noncomputable def casimir (F : CommFrobeniusAlgebra R A) : A ⊗[R] A :=
  F.pairing.copairing

/-- Contracting the Casimir tensor with the Frobenius pairing gives the
identity endomorphism.-/
@[simp]
theorem tensorEndEquiv_casimir (F : CommFrobeniusAlgebra R A) :
    F.pairing.tensorEndEquiv F.casimir = LinearMap.id := by
  simp only [casimir, SymmetricPerfectPairing.tensorEndEquiv_copairing]

/-- The handle (Euler) element, obtained by multiplying the two legs of the
Casimir tensor.

`LinearMap.mul' R A` is mathlib's linear map `A ⊗[R] A →ₗ[R] A` induced by
multiplication.-/
noncomputable def handleElement (F : CommFrobeniusAlgebra R A) : A :=
  LinearMap.mul' R A F.casimir

end FiniteFree

end CommFrobeniusAlgebra

end AxiomaticGW

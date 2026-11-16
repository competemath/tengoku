/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Seed.LinearAlgebra.BilinearForm.Properties
public import Tengoku.Seed.LinearAlgebra.PerfectPairing.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Symmetric perfect pairings

A small bundled interface for the metric on a CohFT state space.  Perfectness
is expressed using mathlib's `LinearMap.IsPerfPair`.

## Reading the Lean notation

This file is a good starting point for readers new to Lean.

* `R V : Type*` introduces two unspecified types.  Mathematically, `R` is the
  coefficient ring and `V` is the module.
* Assumptions in square brackets, such as `[CommRing R]`, are *typeclass
  arguments*.  Lean searches for them automatically instead of requiring us
  to pass the ring operations to every definition by hand.
* `Module R V` says that `V` is an `R`-module.
* `V →ₗ[R] W` means an `R`-linear map from `V` to `W`.
* `V ≃ₗ[R] W` means an invertible `R`-linear map.
* A `structure` is a record: to construct one, all of its fields must be
  supplied.
* A declaration marked `noncomputable` is mathematically well-defined, but
  Lean does not claim that it can execute the construction as a program.
-/

@[expose] public section

namespace AxiomaticGW

open Module

/-- A symmetric bilinear form whose two induced maps to the dual are
equivalences.  This is explicit data rather than a typeclass because one module
may carry several metrics.

The three fields say:

1. `form` is the pairing `V × V → R`;
2. `isSymm` proves `form x y = form y x`;
3. `isPerfPair` proves that contraction with the pairing identifies `V` with
   its dual.-/
structure SymmetricPerfectPairing (R V : Type*) [CommRing R] [AddCommGroup V]
    [Module R V] where
  /-- The underlying bilinear form.-/
  form : LinearMap.BilinForm R V
  /-- A proof that the bilinear form is symmetric.-/
  isSymm : form.IsSymm
  /-- A proof that contraction with the form identifies the module with its dual.-/
  isPerfPair : form.IsPerfPair

namespace SymmetricPerfectPairing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The equivalence between a module and its dual induced by a perfect
pairing.

Mathematically this sends `x : V` to the functional `y ↦ P.form x y`.
`letI` temporarily presents the stored proof `P.isPerfPair` to mathlib's
typeclass system, allowing us to reuse `LinearMap.toPerfPair`.-/
noncomputable def toDual (P : SymmetricPerfectPairing R V) :
    V ≃ₗ[R] Dual R V := by
  letI : P.form.IsPerfPair := P.isPerfPair
  exact P.form.toPerfPair

/-- Evaluating the dual functional produced by `toDual` recovers the original
pairing.  The `@[simp]` attribute lets Lean use this fact automatically during
simplification.-/
@[simp]
theorem toDual_apply (P : SymmetricPerfectPairing R V) (x y : V) :
    P.toDual x y = P.form x y := by
  simp only [toDual, LinearMap.toLinearMap_toPerfPair]

end SymmetricPerfectPairing

end AxiomaticGW

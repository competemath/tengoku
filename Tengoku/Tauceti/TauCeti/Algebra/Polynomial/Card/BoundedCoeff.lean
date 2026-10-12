/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku

/-!
# Counting polynomials of bounded degree and bounded coefficients

For a (semi)ring `R` and a finite set `U` of allowed coefficient values, the polynomials of
degree at most `d` all of whose coefficients lie in `U` form a set of cardinality at most
`#U ^ (d + 1)`: a polynomial of degree `≤ d` is determined by its `d + 1` coefficients
`coeff 0, …, coeff d`, each of which ranges over `U`.

Mathlib uses the *finiteness* of this set inline, as the engine of its `bUnion_roots_finite`
(the set of roots of all polynomials of bounded degree with coefficients in a finite set is
finite), where the same injection `f ↦ (f.coeff i)ᵢ` appears, but exposes neither that finiteness
nor the explicit cardinality bound; this file supplies both.

The integer specialisation counts the polynomials of degree `≤ d` whose coefficients are bounded
in absolute value by `B`: there are at most `(2 * B + 1) ^ (d + 1)` of them. This is the
elementary counting input named by the Layer-2 ("effective Hermite–Minkowski") target of the
effective-bounds roadmap: Mathlib's `NumberField.finite_of_discr_bdd` already bounds the degree
and coefficient height of a generating polynomial of a number field of bounded discriminant
(`natDegree_le_rankOfDiscrBdd`, `boundOfDiscBdd`), so an explicit *count* of number fields of
bounded discriminant needs an explicit count of the polynomials of bounded degree and height.

The cardinality bound counts a number but does not by itself record finiteness (`Set.ncard` is
`0` on an infinite set), so each count is paired with the matching finiteness statement: these are
what turn an injection of some family into one of these boxes into an explicit count of the family,
the counting step the Layer-2 effective Hermite–Minkowski target needs. Mathlib proves this
finiteness only inline, inside `Polynomial.bUnion_roots_finite`, rather than exposing it.

## Main results

* `TauCeti.Polynomial.ncard_natDegree_le_coeff_mem_le`: at most `#U ^ (d + 1)` polynomials of
  degree `≤ d` with every coefficient in a finite set `U`.
* `TauCeti.Polynomial.finite_setOf_natDegree_le_coeff_mem`: that family is finite.
* `TauCeti.Polynomial.ncard_natDegree_le_abs_intCoeff_le`: at most `(2 * B + 1) ^ (d + 1)`
  integer polynomials of degree `≤ d` with every coefficient bounded by `B` in absolute value.
* `TauCeti.Polynomial.finite_setOf_natDegree_le_abs_intCoeff_le`: that family is finite.
-/

public section

open Polynomial

namespace TauCeti.Polynomial

variable {R : Type*} [Semiring R]

end TauCeti.Polynomial

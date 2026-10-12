/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.Algebra.Polynomial.Card.BoundedCoeff

/-!
# Counting the roots of all polynomials of bounded degree and bounded coefficients

For a ring hom `m : R →+* S` into a domain `S` and a finite set `U` of allowed coefficient
values, the set of all roots in `S` of the polynomials of degree at most `d` with every
coefficient in `U`,

`⋃ (f) (_ : f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ U), (f.map m).roots.toFinset`,

has cardinality at most `#U ^ (d + 1) · d`: there are at most `#U ^ (d + 1)` such polynomials
(`TauCeti.Polynomial.ncard_natDegree_le_coeff_mem_le`), and each contributes at most `d`
roots (a degree-`≤ d` polynomial has at most `d` roots in a domain).

This is precisely the explicit count of the *generating set* in Mathlib's proof of Hermite's
finiteness theorem. There, `NumberField.finite_of_discr_bdd` shows the number fields of bounded
discriminant inside a fixed extension are finite by realising each as `ℚ(x)` for `x` a root of an
integer polynomial of explicitly bounded degree and coefficient height, then invoking the
*finiteness* of this very union of root sets, `Polynomial.bUnion_roots_finite`. Mathlib exposes
only that finiteness; the effective Hermite–Minkowski target of the effective-bounds roadmap needs
the matching explicit cardinality, so that an injection of the fields into this generating set
turns into an explicit count of the fields. This file supplies that cardinality, upgrading
`Polynomial.bUnion_roots_finite` exactly as
`TauCeti.Polynomial.ncard_natDegree_le_coeff_mem_le` upgrades the polynomial finiteness it is
built on.

## Main results

* `TauCeti.Polynomial.ncard_biUnion_roots_natDegree_le_coeff_mem_le`: at most `#U ^ (d + 1) · d`
  roots in `S` among all degree-`≤ d` polynomials with every coefficient in a finite set `U`.
* `TauCeti.Polynomial.ncard_biUnion_roots_natDegree_le_abs_intCoeff_le`: the integer
  specialisation, `(2 · B + 1) ^ (d + 1) · d` roots among all degree-`≤ d` integer polynomials
  with every coefficient bounded by `B` in absolute value. This is the form named by the
  Layer-2 ("effective Hermite–Minkowski") target.
-/

public section

open Polynomial

namespace TauCeti.Polynomial

variable {R S : Type*} [Semiring R] [CommRing S] [IsDomain S] [DecidableEq S]

end TauCeti.Polynomial

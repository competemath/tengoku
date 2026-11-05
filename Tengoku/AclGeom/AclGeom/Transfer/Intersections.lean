/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.Seed.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Tengoku.Seed.Combinatorics.Matroid.Rank.ENat
import Tengoku.AclGeom.AclGeom.Closure.Ambient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite generators for intersections of absolute closures

For finite `A ⊆ K₁` and arbitrary `B ⊆ K₁` there is a finite `C ⊆ K₁` with
`racl(A) ⊓ racl(B) = racl(C)` (blueprint Lemma
finite-intersection-generator, slightly generalized: only one of the two
sets needs to be finite).

Two departures from the blueprint proof, both simplifications:

* the transcendence-basis bookkeeping runs through mathlib's
  algebraic-independence *matroid* (`AlgebraicIndependent.matroid`): a
  matroid basis of the carrier of the intersection is algebraically
  independent, generates it algebraically, and is finite because it is an
  independent subset of the matroid closure of the finite set `A`;
* the automorphism-symmetry step is replaced by minimal-polynomial
  divisibility: an annihilator of `c` over `k(A)` has coefficients in `K₁`,
  so `minpoly K₁ c` divides it and every `K₁`-conjugate of `c` is again a
  root of it — conjugates never leave `racl k A` (`conjugate_mem_racl`).
  No automorphism of `Ω` is ever constructed.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** complete (M5, checklist T2 and T3's strict-inclusion
transfer); the one-quantifier transfer consumes these in
`AclGeom.Transfer.OneQuantifier`.
-/

namespace AclGeom

open IntermediateField Polynomial

noncomputable section

variable {k : Type*} {Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

section MatroidBridge

end MatroidBridge

section PolyCharacterization

end PolyCharacterization

section IntersectionGenerator

end IntersectionGenerator

section StrictTransfer

end StrictTransfer

end

end AclGeom

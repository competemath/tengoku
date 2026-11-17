/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.Xi.CanonicalDivisor
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.Xi.RiemannHypothesisBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact multiplicity across the centered xi--zeta correspondence

This module combines two unconditional local facts:

* the affine map `z ↦ 1 / 2 + I * z` preserves analytic order; and
* at every zero of `entireRiemannXi`, the entire xi function is locally a
  nonvanishing analytic unit times `riemannZeta`.

Consequently, each canonical pullback-zero occurrence has exactly the
analytic multiplicity used by the corresponding zeta zero count.  No
xi-specific zero-distribution or Hadamard-product package is assumed.
-/

namespace OverflowResidueRH

/-- At a zero of the centered pullback, analytic order is exactly the order
of `riemannZeta` at the corresponding point `1 / 2 + I * z`.
@isnad1 id=eq.1h1v.s6.02c3703fb657 from=translated src=- shape=2537151f vocab=f2075a70
-/
theorem entireXiPullback_analyticOrderAt_eq_riemannZeta_of_zero
    {z : ℂ} (hz : EntireXiPullback z = 0) :
    analyticOrderAt EntireXiPullback z =
      analyticOrderAt riemannZeta
        ((1 / 2 : ℂ) + Complex.I * z) :=
  (entireXiPullback_analyticOrderAt_eq_entireRiemannXi z).trans
    (entireRiemannXi_analyticOrderAt_eq_riemannZeta_of_zero hz)

/-- Natural-number form of exact pullback--zeta multiplicity preservation.
@isnad1 id=eq.1h1v.s6.56a785924865 from=translated src=- shape=2537151f vocab=30a0ac3f
-/
theorem entireXiPullback_analyticOrderNatAt_eq_riemannZeta_of_zero
    {z : ℂ} (hz : EntireXiPullback z = 0) :
    analyticOrderNatAt EntireXiPullback z =
      analyticOrderNatAt riemannZeta
        ((1 / 2 : ℂ) + Complex.I * z) :=
  congrArg ENat.toNat
    (entireXiPullback_analyticOrderAt_eq_riemannZeta_of_zero hz)

/-- The canonical occurrence fiber over a nonzero pullback zero has cardinal
equal to the analytic multiplicity of the corresponding zeta zero.  This is
the precise local bridge needed by multiplicity-weighted height counts.
@isnad1 id=eq.0h1v.s7.2dffa87f7058 from=translated src=- shape=c547c846 vocab=9d3a5ec7
-/
theorem entireXiPullbackZeroOccurrence_fiber_natCard_eq_riemannZeta_order
    (z : EntireXiPullbackNonzeroZero) :
    Nat.card {i : EntireXiPullbackZeroOccurrence // i.1 = z} =
      analyticOrderNatAt riemannZeta
        ((1 / 2 : ℂ) + Complex.I * z.1) :=
  (entireXiPullbackZeroOccurrence_fiber_natCard z).trans
    (entireXiPullback_analyticOrderNatAt_eq_riemannZeta_of_zero z.2.1)

end OverflowResidueRH

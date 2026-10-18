/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.JInvariantReductionType
import Tengoku.Seed.RingTheory.Valuation.ValuationSubring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The sharp multiplicative-reduction valuation of `j` over a DVR extension (issue #72)

Let `L / K` be a field extension and `A : ValuationSubring L` a **discrete** valuation subring of
`L`.  This is the abstract shape of "a finite extension `L / K` with `A` the corresponding valuation
ring", exactly as used by the reduction base-change bricks
`isIntegral_j_of_hasGoodReduction_baseChange` (`JInvariantGoodReductionBaseChange.lean`, #501),
`not_mem_j_of_hasMultiplicativeReduction_baseChange`
(`JInvariantMultiplicativeReductionBaseChange.lean`, #505) and
`valuation_j_of_hasGoodReduction_baseChange` (`JInvariantGoodReductionValuationBaseChange.lean`,
#507).

If a Weierstrass curve `W : WeierstrassCurve K` (elliptic) base changes to a curve `W⁄L` with
**multiplicative reduction over `A`**, then the valuation of its `j`-invariant at the base place is
*exactly* `(v_A Δ)⁻¹`:

```
valuation L (maximalIdeal A) (algebraMap K L W.j)
  = (valuation L (maximalIdeal A) (algebraMap K L W.Δ))⁻¹.
```

This **strengthens** the merged multiplicative base-change brick #505
`not_mem_j_of_hasMultiplicativeReduction_baseChange`, which only records that
`algebraMap K L W.j ∉ A` (i.e. `1 < v`), to the exact value — the base-change reflection of the
sharp identity `valuation_j_of_hasMultiplicativeReduction` (`v(j) = (v Δ)⁻¹`,
`JInvariantReductionType.lean`).  It is the multiplicative-reduction mirror of the sharp
good-reduction reflection #507 `valuation_j_of_hasGoodReduction_baseChange`.
As in #505/#507 the "`A` lies over the base" condition is free (no ad-hoc hypothesis): the substrate
is simply reused with `R := A`, `K := L`, and `map_j`, `map_Δ` translate back to `W`'s invariants
over `K`.

## Main results

* `WeierstrassCurve.valuation_j_of_hasMultiplicativeReduction_baseChange` — the sharp identity
  `v_A(algebraMap K L W.j) = (v_A(algebraMap K L W.Δ))⁻¹` under multiplicative reduction of
  `W⁄L` over `A`.

## Scope

This delivers the reusable *per-extension* sharp identity.  The full statement quantifies over all
finite extensions `L / K`, and the *converse* (`v(j) < 0` ⟹ *potential* multiplicative reduction,
via the Tate curve) needs infrastructure absent from the repository and the pinned Mathlib; both
remain larger efforts.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.1, VII.5.5.
-/

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (A : ValuationSubring L) [IsDiscreteValuationRing A]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- **The sharp multiplicative-reduction valuation of `j` at the base place.** If the base change
`W⁄L` has multiplicative reduction over the discrete valuation subring `A ⊆ L`, then the valuation
of `j` at the base place is exactly `(v_A Δ)⁻¹`. This strengthens
`not_mem_j_of_hasMultiplicativeReduction_baseChange` (#505, which records only
`algebraMap K L W.j ∉ A`) to the exact value — the base-change reflection of the sharp identity
`valuation_j_of_hasMultiplicativeReduction` (`v(j) = (v Δ)⁻¹`), and the multiplicative mirror of
the good-reduction reflection `valuation_j_of_hasGoodReduction_baseChange` (#507). -/
theorem valuation_j_of_hasMultiplicativeReduction_baseChange
    (h : HasMultiplicativeReduction A (W⁄L)) :
    valuation L (maximalIdeal A) (algebraMap K L W.j) =
      (valuation L (maximalIdeal A) (algebraMap K L W.Δ))⁻¹ := by
  haveI : HasMultiplicativeReduction A (W⁄L) := h
  haveI : (W⁄L).IsElliptic := inferInstanceAs (W.map (algebraMap K L)).IsElliptic
  have hv := valuation_j_of_hasMultiplicativeReduction A (W⁄L)
  rwa [show (W⁄L).j = algebraMap K L W.j from W.map_j (algebraMap K L),
    show (W⁄L).Δ = algebraMap K L W.Δ from W.map_Δ (algebraMap K L)] at hv

end WeierstrassCurve

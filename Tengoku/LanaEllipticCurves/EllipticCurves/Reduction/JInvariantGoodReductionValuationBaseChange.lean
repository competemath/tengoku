/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.JInvariantGoodReductionValuation
import Tengoku.Seed.RingTheory.Valuation.ValuationSubring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The sharp good-reduction valuation of `j` over a DVR extension (issue #72)

Let `L / K` be a field extension and `A : ValuationSubring L` a **discrete** valuation subring of
`L`.  This is the abstract shape of "a finite extension `L / K` with `A` the corresponding valuation
ring", exactly as used by the good-reduction base-change bricks
`isIntegral_j_of_hasGoodReduction_baseChange` (`JInvariantGoodReductionBaseChange.lean`, #501) and
`not_mem_j_of_hasMultiplicativeReduction_baseChange`
(`JInvariantMultiplicativeReductionBaseChange.lean`, #505).

If a Weierstrass curve `W : WeierstrassCurve K` (elliptic) base changes to a curve `W⁄L` with
**good reduction over `A`**, then the valuation of its `j`-invariant at the base place is *exactly*
`v_A(c₄)³`:

```
valuation L (maximalIdeal A) (algebraMap K L W.j)
  = valuation L (maximalIdeal A) (algebraMap K L W.c₄) ^ 3.
```

This **strengthens** the merged good-reduction base-change brick #501
`isIntegral_j_of_hasGoodReduction_baseChange`, which only records that `algebraMap K L W.j ∈ A`
(i.e. `v ≥ 0`), to the exact value — the base-change reflection of the sharp identity
`valuation_j_of_hasGoodReduction` (`v(j) = v(c₄)³`, `JInvariantGoodReductionValuation.lean`), and
the sharp form of Silverman AEC VII.5.1 at the extended place.  As in #501 the "`A` lies over the
base" condition is free (no ad-hoc hypothesis): the substrate is simply reused with `R := A`,
`K := L`, and `map_j`, `map_c₄` translate back to `W`'s invariants over `K`.

## Main results

* `WeierstrassCurve.valuation_j_of_hasGoodReduction_baseChange` — the sharp identity
  `v_A(algebraMap K L W.j) = v_A(algebraMap K L W.c₄)³` under good reduction of `W⁄L` over `A`.
* `WeierstrassCurve.valuation_j_eq_one_iff_valuation_c₄_eq_one_baseChange` — the base-place unit
  criterion `v_A(algebraMap K L W.j) = 1 ↔ v_A(algebraMap K L W.c₄) = 1`.

## Scope

This delivers the reusable *per-extension* sharp identity.  The full VII.5.5 statement quantifies
over all finite extensions `L / K`, and the *converse* (`v(j) ≥ 0` ⟹ good reduction, via the Tate
curve / Néron models) needs infrastructure absent from the repository and the pinned Mathlib; both
remain larger efforts.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.1, VII.5.5.
-/

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (A : ValuationSubring L) [IsDiscreteValuationRing A]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- **The sharp good-reduction valuation of `j` at the base place.** If the base change `W⁄L` has
good reduction over the discrete valuation subring `A ⊆ L`, then the valuation of `j` at the base
place is exactly `v_A(c₄)³`. This strengthens `isIntegral_j_of_hasGoodReduction_baseChange` (#501,
which records only `algebraMap K L W.j ∈ A`) to the exact value — the base-change reflection of the
sharp identity `valuation_j_of_hasGoodReduction` (`v(j) = v(c₄)³`). -/
theorem valuation_j_of_hasGoodReduction_baseChange
    (h : HasGoodReduction A (W⁄L)) :
    valuation L (maximalIdeal A) (algebraMap K L W.j) =
      valuation L (maximalIdeal A) (algebraMap K L W.c₄) ^ 3 := by
  haveI : HasGoodReduction A (W⁄L) := h
  haveI : (W⁄L).IsElliptic := inferInstanceAs (W.map (algebraMap K L)).IsElliptic
  have hv := valuation_j_of_hasGoodReduction A (W⁄L)
  rwa [show (W⁄L).j = algebraMap K L W.j from W.map_j (algebraMap K L),
    show (W⁄L).c₄ = algebraMap K L W.c₄ from W.map_c₄ (algebraMap K L)] at hv

/-- **The base-place unit criterion under good reduction.** From the sharp identity
`v_A(j) = v_A(c₄)³`, the `j`-invariant is a unit at the base place exactly when `c₄` is:
`v_A(algebraMap K L W.j) = 1 ↔ v_A(algebraMap K L W.c₄) = 1`. -/
theorem valuation_j_eq_one_iff_valuation_c₄_eq_one_baseChange
    (h : HasGoodReduction A (W⁄L)) :
    valuation L (maximalIdeal A) (algebraMap K L W.j) = 1 ↔
      valuation L (maximalIdeal A) (algebraMap K L W.c₄) = 1 := by
  rw [valuation_j_of_hasGoodReduction_baseChange A W h]
  refine ⟨fun hj => ?_, fun hc => by rw [hc, one_pow]⟩
  exact (pow_left_inj₀ (n := 3) zero_le zero_le (by norm_num)).mp (by rw [hj, one_pow])

end WeierstrassCurve

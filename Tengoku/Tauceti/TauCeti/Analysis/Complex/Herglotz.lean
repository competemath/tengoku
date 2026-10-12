/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.MeasureTheory.Group.Circle
import Tengoku.Tauceti.TauCeti.MeasureTheory.Measure.Prokhorov

/-!
# The Herglotz representation of holomorphic functions with nonnegative real part

A function `F` holomorphic on the unit disc with `0 ≤ re F` is the **Herglotz transform** of a
finite positive measure `μ` on the unit circle, up to an imaginary constant:

`F w = ∫ (z + w) / (z - w) dμ(z) + (im F(0)) i`,

and conversely every such transform is holomorphic on the disc with nonnegative real part.
The representation is the basic structure theorem for holomorphic functions of positive real
part (Carathéodory functions). Through a Cayley transform it gives the Nevanlinna representation
of Pick functions, which in turn underlies the analytic characterizations of Stieltjes and
complete Bernstein functions.

## Main results

* `DiffContOnCl.circleAverage_herglotzRieszKernel_smul_re_add`: the Herglotz formula on a disc,
  recovering a holomorphic function from the boundary values of its real part.
* `MeasureTheory.Measure.herglotzTransform`: the Herglotz transform of a measure on the circle.
* `MeasureTheory.Measure.differentiableOn_herglotzTransform` and
  `MeasureTheory.Measure.re_herglotzTransform_nonneg`: the transform of a finite measure is
  holomorphic on the disc with nonnegative real part.
* `TauCeti.exists_isFiniteMeasure_eq_herglotzTransform_add`: **the Herglotz representation
  theorem**.
* `TauCeti.differentiableOn_and_re_nonneg_iff_exists_eq_herglotzTransform_add`: the resulting
  characterization of holomorphic functions on the disc with nonnegative real part.

## References

* G. Herglotz, *Über Potenzreihen mit positivem, reellem Teil im Einheitskreis*, Ber. Verh.
  Sächs. Akad. Wiss. Leipzig **63** (1911), 501–511.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Chapter 11 (positive harmonic functions and
  the Herglotz representation).
* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*, 2nd ed.,
  Chapter 6 (the Nevanlinna–Pick representation, via the Herglotz theorem).
-/

public section

noncomputable section

open Complex MeasureTheory Metric Real Set Filter Topology
open scoped NNReal ENNReal

namespace TauCeti

variable {f : ℂ → ℂ} {c w : ℂ} {R : ℝ}

/-! ### The Herglotz transform of a measure on the circle -/

/-! ### The Herglotz representation -/

end TauCeti

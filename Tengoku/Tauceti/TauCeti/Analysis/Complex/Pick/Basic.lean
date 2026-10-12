/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Analysis.Complex.Herglotz
public import Tengoku.Tauceti.TauCeti.Analysis.Complex.UpperHalfPlane.DiscCoordinate

/-!
# Pick functions in Cayley coordinates

A Pick function is holomorphic on the upper half-plane and has nonnegative imaginary part there.
The Cayley coordinate `z ↦ (z - i) / (z + i)` carries the upper half-plane to the unit disc,
and multiplication by `-i` carries nonnegative imaginary part to nonnegative real part.  The
Herglotz representation on the disc therefore gives

`F z = i · ∫ ζ, (ζ + w) / (ζ - w) ∂μ(ζ) + Re F(i)`,

where `w = (z - i) / (z + i)` and `μ` is a finite positive measure on the unit circle.  The
converse holds as well.  This is the Cayley-coordinate form of the Pick representation; moving
the circle measure to the real line gives the usual Nevanlinna representation.

## Main declarations

* `TauCeti.exists_isFiniteMeasure_eq_I_mul_herglotzTransform_cayley_add`: existence of the
  Cayley-coordinate Herglotz representation of a Pick function.
* `TauCeti.differentiableOn_and_im_nonneg_iff_exists_eq_I_mul_herglotzTransform_cayley_add`:
  the characterization of Pick functions by this representation.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*,
  2nd ed., Chapter 6.
-/

public section

noncomputable section

open Complex MeasureTheory Metric Set
open scoped ComplexConjugate

namespace TauCeti

end TauCeti

end

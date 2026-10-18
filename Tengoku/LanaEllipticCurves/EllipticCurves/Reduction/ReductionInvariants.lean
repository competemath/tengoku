/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Reduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reduction commutes with the Weierstrass invariants (issue #72)

Let `R` be a discrete valuation ring with fraction field `K = Frac R`, and let
`W : WeierstrassCurve K` be given by a *minimal* Weierstrass equation (`IsMinimal R W`, which
supplies the `IsIntegral R W` instance and hence makes both the integral minimal model
`integralModel R W : WeierstrassCurve R` and the reduced curve
`W.reduction R : WeierstrassCurve (ResidueField R)` available).

By definition `W.reduction R = (integralModel R W).map (residue R)`, so every Weierstrass
coefficient and invariant of the reduced curve is the **residue** of the corresponding
coefficient/invariant of the integral minimal model. This file records that whole dictionary — the
residue-map face of the already-available algebraMap face `integralModel_aᵢ_eq … integralModel_Δ_eq`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean`), each of which states
`algebraMap R K (integralModel R W).X = W.X`.

It is the natural sibling of `reduction_j_eq` (`JInvariantReductionCommutes.lean`, #486). Unlike the
`j`-invariant, the coefficients `aᵢ` and the invariants `bᵢ`, `c₄`, `c₆`, `Δ` are defined for
*every* Weierstrass curve, so these lemmas require **no** ellipticity or good-reduction
hypothesis — only `IsMinimal R W`.

Each proof is a single application of Mathlib's functoriality lemmas `map_aᵢ`, `map_bᵢ`, `map_c₄`,
`map_c₆`, `map_Δ` (`Weierstrass.lean`) to the residue ring map `residue R`, using that
`reduction R W` unfolds definitionally to `(integralModel R W).map (residue R)`.

## Main results

For `W : WeierstrassCurve K` with `[IsMinimal R W]`, in `namespace WeierstrassCurve`:

* `reduction_a₁_eq`, `reduction_a₂_eq`, `reduction_a₃_eq`, `reduction_a₄_eq`, `reduction_a₆_eq` —
  `(W.reduction R).aᵢ = residue R (integralModel R W).aᵢ`.
* `reduction_b₂_eq`, `reduction_b₄_eq`, `reduction_b₆_eq`, `reduction_b₈_eq` —
  `(W.reduction R).bᵢ = residue R (integralModel R W).bᵢ`.
* `reduction_c₄_eq`, `reduction_c₆_eq` —
  `(W.reduction R).c₄/c₆ = residue R (integralModel R W).c₄/c₆`.
* `reduction_Δ_eq` — `(W.reduction R).Δ = residue R (integralModel R W).Δ`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5.
-/

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve

variable {R K : Type*}
variable [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
variable (R) in
/-- The `a₁`-coefficient of the reduction is the residue of the integral model's `a₁`. -/
theorem reduction_a₁_eq (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.reduction R).a₁ = residue R (integralModel R W).a₁ :=
  map_a₁ (W := integralModel R W) (residue R)

variable (R) in
/-- The `a₂`-coefficient of the reduction is the residue of the integral model's `a₂`. -/
theorem reduction_a₂_eq (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.reduction R).a₂ = residue R (integralModel R W).a₂ :=
  map_a₂ (W := integralModel R W) (residue R)

variable (R) in
/-- The `a₃`-coefficient of the reduction is the residue of the integral model's `a₃`. -/
theorem reduction_a₃_eq (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.reduction R).a₃ = residue R (integralModel R W).a₃ :=
  map_a₃ (W := integralModel R W) (residue R)

variable (R) in
/-- The `a₄`-coefficient of the reduction is the residue of the integral model's `a₄`. -/
theorem reduction_a₄_eq (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.reduction R).a₄ = residue R (integralModel R W).a₄ :=
  map_a₄ (W := integralModel R W) (residue R)

variable (R) in
/-- The `a₆`-coefficient of the reduction is the residue of the integral model's `a₆`. -/
theorem reduction_a₆_eq (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.reduction R).a₆ = residue R (integralModel R W).a₆ :=
  map_a₆ (W := integralModel R W) (residue R)

variable (R) in
/-- The `b₂`-invariant of the reduction is the residue of the integral model's `b₂`. -/
theorem reduction_b₂_eq (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.reduction R).b₂ = residue R (integralModel R W).b₂ :=
  map_b₂ (W := integralModel R W) (residue R)

variable (R) in
/-- The `b₄`-invariant of the reduction is the residue of the integral model's `b₄`. -/
theorem reduction_b₄_eq (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.reduction R).b₄ = residue R (integralModel R W).b₄ :=
  map_b₄ (W := integralModel R W) (residue R)

variable (R) in
/-- The `b₆`-invariant of the reduction is the residue of the integral model's `b₆`. -/
theorem reduction_b₆_eq (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.reduction R).b₆ = residue R (integralModel R W).b₆ :=
  map_b₆ (W := integralModel R W) (residue R)

variable (R) in
/-- The `b₈`-invariant of the reduction is the residue of the integral model's `b₈`. -/
theorem reduction_b₈_eq (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.reduction R).b₈ = residue R (integralModel R W).b₈ :=
  map_b₈ (W := integralModel R W) (residue R)

variable (R) in
/-- The `c₄`-invariant of the reduction is the residue of the integral model's `c₄`. -/
theorem reduction_c₄_eq (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.reduction R).c₄ = residue R (integralModel R W).c₄ :=
  map_c₄ (W := integralModel R W) (residue R)

variable (R) in
/-- The `c₆`-invariant of the reduction is the residue of the integral model's `c₆`. -/
theorem reduction_c₆_eq (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.reduction R).c₆ = residue R (integralModel R W).c₆ :=
  map_c₆ (W := integralModel R W) (residue R)

variable (R) in
/-- **The discriminant commutes with reduction.** `(W.reduction R).Δ` is the residue of the
discriminant of the integral minimal model. Compare `reduction_j_eq`; here no good-reduction or
ellipticity hypothesis is needed, since `Δ` is defined for every Weierstrass curve. -/
theorem reduction_Δ_eq (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.reduction R).Δ = residue R (integralModel R W).Δ :=
  map_Δ (W := integralModel R W) (residue R)

end WeierstrassCurve

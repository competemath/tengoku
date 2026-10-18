/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.GoodReductionBaseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reduction commutes with base change to a DVR extension (issue #395)

Let `R` be a discrete valuation ring with fraction field `K = Frac R`, and let `A` be a second
discrete valuation ring with fraction field `L = Frac A`, lying over `R` (compatible scalar towers
`R → A → L` and `R → K → L`, and — crucially for the residue-field map — `algebraMap R A` a local
homomorphism, `[IsLocalHom (algebraMap R A)]`; this is the situation of a finite extension `L / K`
with `A` the corresponding valuation ring). Building on issue #393
(`EllipticCurves/Reduction/GoodReductionBaseChange.lean`), which shows good reduction is *stable*
under base change, this file identifies the *reduced curve* of the base change with the base change
of the reduced curve, along the residue-field extension
`ResidueField.map (algebraMap R A) : ResidueField R →+* ResidueField A`.

This is the **"reduction commutes with base change"** brick of the Néron–Ogg–Shafarevich ladder
(parent issue #73; Silverman AEC VII.5, VII.7 Theorem 7.1) — the functoriality input consumed by
the remaining rungs (D `K^ur` / strict-henselisation, and the general σ̄-equivariant `redPt` form).

The identification is delivered in two steps.

## Step 1 — the canonical-model form (`reduction_baseChange_integralModel_eq`)

Mathlib's `WeierstrassCurve.reduction R W = (integralModel R W).map (residue R)` is defined through
`integralModel R W = hW.integral.choose`, a *`Classical.choice`* of an integral model. Pinning the
integral model on the left to the base-changed model `(integralModel R W)⁄A` (which #393's
`isIntegral_baseChange` exhibits as an integral model of `W⁄L`), rather than the opaque
`integralModel A (W⁄L)`, gives the clean equality

* `WeierstrassCurve.reduction_baseChange_integralModel_eq` — equating
  `((integralModel R W)⁄A).map (residue A)`
  with `(W.reduction R).map (ResidueField.map (algebraMap R A))`.

Both sides unfold to `(integralModel R W).map ((residue A).comp (algebraMap R A))` — the left via
`WeierstrassCurve.map_map`, the right via `WeierstrassCurve.map_map` together with
`IsLocalRing.ResidueField.map_comp_residue` (the residue functor is definitionally compatible with
`residue`). No `choose` mismatch arises because the integral model is fixed on both sides.

## Step 2 — the literal form (`reduction_baseChange_eq`)

The two integral models `integralModel A (W⁄L)` and `(integralModel R W)⁄A` are in fact **equal**,
not merely isomorphic. The subtle point is that `IsIntegral R W` is a *plain lift*
(`∃ W_int, W = W_int⁄K`) with **no** variable change — unlike `minimal`, which does apply a
`VariableChange` to achieve minimality. So `integralModel A (W⁄L)` and `(integralModel R W)⁄A` are
two lifts of `W⁄L` to `A` that agree after base change to `L`:

* `(integralModel A (W⁄L))⁄L = W⁄L` (`baseChange_integralModel_eq`);
* `((integralModel R W)⁄A)⁄L = W⁄L` (#393's `baseChange_integralModel_baseChange_eq`).

Since `algebraMap A L` is injective (`A` a domain, `L = Frac A`) and `WeierstrassCurve.map` along an
injective ring hom is injective (`WeierstrassCurve.map_injective`), the two lifts are equal:

* `WeierstrassCurve.integralModel_baseChange_eq` — `integralModel A (W⁄L) = (integralModel R W)⁄A`.

Feeding this into Step 1 (under good reduction, where `isMinimal_baseChange` makes `W⁄L` minimal
over `A` so that `(W⁄L).reduction A` is defined) yields the literal equality the ladder wants:

* `WeierstrassCurve.reduction_baseChange_eq` —
  `(W⁄L).reduction A = (W.reduction R).map (ResidueField.map (algebraMap R A))`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5, VII.7 Theorem 7.1.
-/

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve

variable {R A K L : Type*}
variable [CommRing R] [CommRing A] [Field K] [Field L]
variable [Algebra R K] [Algebra A L] [Algebra R A] [Algebra K L] [Algebra R L]
variable [IsScalarTower R A L] [IsScalarTower R K L]
variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
variable [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L]

variable (R A) in
/-- **Reduction commutes with base change (canonical-model form).** If `algebraMap R A` is a local
homomorphism of DVRs lying over one another and `W` is minimal over `R`, then reducing the
base-changed integral model `(integralModel R W)⁄A` modulo the maximal ideal of `A` agrees with
base-changing the reduced curve `W.reduction R` along the residue-field extension
`ResidueField.map (algebraMap R A) : ResidueField R →+* ResidueField A`:
`((integralModel R W)⁄A).map (residue A) = (W.reduction R).map (ResidueField.map (algebraMap R A))`.

Both sides equal `(integralModel R W).map ((residue A).comp (algebraMap R A))`: the left by
`WeierstrassCurve.map_map`, the right by `WeierstrassCurve.map_map` and
`IsLocalRing.ResidueField.map_comp_residue`. Pinning the integral model to `(integralModel R W)⁄A`
(rather than the `Classical.choice`-defined `integralModel A (W⁄L)`) is what makes this a genuine
equality; see the module docstring. -/
theorem reduction_baseChange_integralModel_eq [IsLocalHom (algebraMap R A)]
    (W : WeierstrassCurve K) [IsMinimal R W] :
    ((integralModel R W)⁄A).map (residue A)
      = (W.reduction R).map (ResidueField.map (algebraMap R A)) := by
  simp only [reduction, baseChange, WeierstrassCurve.map_map,
    IsLocalRing.ResidueField.map_comp_residue]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsDomain A]
  [IsDiscreteValuationRing A] in
variable (R A) in
/-- The two integral models of `W⁄L` over `A` — the `Classical.choice`-defined `integralModel A`
of the base change, and the base change `(integralModel R W)⁄A` of the integral model over `R` — are
**equal**. Both are lifts of `W⁄L` to `A` (they agree after base change to `L`, by
`baseChange_integralModel_eq` and #393's `baseChange_integralModel_baseChange_eq`), and
`algebraMap A L` is injective with `WeierstrassCurve.map` injective along it. The key point is that
`integralModel`/`IsIntegral` is a *plain lift* with no `VariableChange`, so the two lifts agree on
the nose (this is what distinguishes it from `minimal`). -/
theorem integralModel_baseChange_eq (W : WeierstrassCurve K) [IsIntegral R W] :
    haveI : IsIntegral A (W⁄L) := isIntegral_baseChange R A W
    integralModel A (W⁄L) = (integralModel R W)⁄A := by
  haveI : IsIntegral A (W⁄L) := isIntegral_baseChange R A W
  have h : (integralModel A (W⁄L))⁄L = ((integralModel R W)⁄A)⁄L := by
    rw [baseChange_integralModel_eq A (W⁄L)]
    exact baseChange_integralModel_baseChange_eq R A W
  exact map_injective (IsFractionRing.injective A L) h

variable (R A) in
/-- **Reduction commutes with base change (literal form).** For DVRs `A / R` with a local inclusion
`algebraMap R A`, if `W` has good reduction over `R` then reducing the base-changed curve `W⁄L`
modulo the maximal ideal of `A` agrees with base-changing the reduced curve `W.reduction R` along
the residue-field extension `ResidueField.map (algebraMap R A)`:
`(W⁄L).reduction A = (W.reduction R).map (ResidueField.map (algebraMap R A))`.

This upgrades the canonical-model form `reduction_baseChange_integralModel_eq` to the literal
Mathlib `reduction A (W⁄L)` via `integralModel_baseChange_eq`. Good reduction is needed only to make
`W⁄L` minimal over `A` (`isMinimal_baseChange`), so that `(W⁄L).reduction A` is defined. This is the
functoriality identity the remaining Néron–Ogg–Shafarevich rungs (D `K^ur`, general σ̄-equivariant
`redPt`) consume. -/
theorem reduction_baseChange_eq [IsLocalHom (algebraMap R A)]
    (W : WeierstrassCurve K) [HasGoodReduction R W] :
    haveI : IsMinimal A (W⁄L) := isMinimal_baseChange R A W
    (W⁄L).reduction A = (W.reduction R).map (ResidueField.map (algebraMap R A)) := by
  haveI : IsMinimal A (W⁄L) := isMinimal_baseChange R A W
  change (integralModel A (W⁄L)).map (residue A)
      = (W.reduction R).map (ResidueField.map (algebraMap R A))
  rw [integralModel_baseChange_eq R A W]
  exact reduction_baseChange_integralModel_eq R A W

end WeierstrassCurve

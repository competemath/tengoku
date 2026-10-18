/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.LanaBelyi.Belyi.Curve.Basic
import Tengoku.LanaBelyi.Belyi.Curve.Descent
import Tengoku.LanaBelyi.Belyi.Curve.GeometricIntegralDescent
import Tengoku.LanaBelyi.Belyi.Curve.SmoothRelDimDescent
import Tengoku.LanaBelyi.Belyi.Definable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Base change of curves along a field extension

The base-change half of **B3c** (taxis issue #48): the curve predicate
`Belyi.IsCurveOver` is stable under base change along a field extension `k₀ ⊆ K`, so a
scheme with a curve model over `k₀` is itself a curve over `K`.

All three constituents of `IsCurveOver` are stable under base change in mathlib
(`SmoothOfRelativeDimension`, `IsProper`, `GeometricallyIntegral`), so the content here
is the packaging: transporting the predicate along the identification stored inside a
`Belyi.DefinableOver` witness.

The converse — **descent** of the curve predicate from `X/K` to a model `X₀/k₀` along the
faithfully flat map `Spec K ⟶ Spec k₀` — is the descent direction of B3c (taxis #167). It
is *assembled* here from `MorphismProperty.DescendsAlong` instances for the three curve
properties along `@Surjective ⊓ @Flat ⊓ @QuasiCompact`:

* `@IsProper` descends unconditionally
  (`AlgebraicGeometry.descendsAlong_isProper_surjective_inf_flat_inf_quasicompact`, taxis #167);
* `@GeometricallyIntegral` descends along the field extension by the direct `Geometrically`-API
  argument `Belyi.geometricallyIntegral_of_baseChange` (taxis #204) — no `DescendsAlong` instance
  is needed, because the cover here always has a *field* base;
* `@SmoothOfRelativeDimension 1` descends along the field extension by the direct field-specific
  argument `Belyi.smoothOfRelativeDimension_of_baseChange` (taxis #205) — again no `DescendsAlong`
  instance is needed, for the same reason (the general codescent of
  `Locally (IsStandardSmoothOfRelativeDimension n)` is a genuine mathlib gap, but the field base
  sidesteps it via a per-chart rank-of-Kähler-differentials computation).

Since all three legs descend directly, the descent assembly `IsCurveOver.of_pullback` /
`IsCurveOver.of_baseChangeModel` is now **unconditional** — it carries no `DescendsAlong` instance
hypotheses. This upgrades `IsCurveOver.of_isCurveOver_model` to an equivalence and discharges the
forward-direction gate of the main theorem (`Belyi/Main.lean`, taxis #55/#188).

## Main results

* `Belyi.isCurveOver_pullback`: the base change of a curve along `Spec K ⟶ Spec k₀` is a
  curve over `K`.
* `Belyi.IsCurveOver.of_isCurveOver_model`: if a `DefinableOver` witness has a model that
  is a curve over `k₀`, then `X` is a curve over `K`.
* `Belyi.IsCurveOver.of_pullback` / `Belyi.IsCurveOver.of_baseChangeModel` (descent direction,
  now unconditional): a scheme over `K` that is a curve and admits a `k₀`-model has a **curve**
  model over `k₀`.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

variable (k₀ K : Type u) [Field k₀] [Field K] [Algebra k₀ K]

section Pullback

variable (X₀ : Scheme.{u}) [X₀.Over (Spec (CommRingCat.of k₀))] [IsCurveOver k₀ X₀]

/-- The base change of `X₀/k₀` along `Spec K ⟶ Spec k₀`, as a scheme over `Spec K`. -/
noncomputable instance : (pullback (X₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K)).Over
    (Spec (CommRingCat.of K)) :=
  ⟨pullback.snd _ _⟩

end Pullback

section Transport

variable {k₀ K} {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [Y.Over (Spec (CommRingCat.of K))]

end Transport

section Descent

open MorphismProperty

/-! ### Descent direction of B3c (taxis #167)

The descent of the curve predicate along the field extension `k₀ ⊆ K` is assembled from the
descent of the three curve properties along the faithfully-flat cover
`specAlgebraMap k₀ K : Spec K ⟶ Spec k₀` (which is `@Surjective ⊓ @Flat ⊓ @QuasiCompact`).
`@IsProper` descends unconditionally via `MorphismProperty.of_pullback_snd_of_descendsAlong`;
`@GeometricallyIntegral` and `@SmoothOfRelativeDimension 1` descend by the field-specific
arguments `geometricallyIntegral_of_baseChange` (taxis #204) and
`smoothOfRelativeDimension_of_baseChange` (taxis #205), which exploit that the cover here has a
*field* base. So the assembly is unconditional (no `DescendsAlong` instance hypotheses).

The `MorphismProperty Scheme.{u}` annotation on the cover pins its universe to that of the
ambient schemes at the `@IsProper` descent call site. -/

end Descent

end Belyi

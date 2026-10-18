/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.PointReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The local parameter `z = -x/y` on the kernel of reduction `E₁(K)`

Let `R` be a discrete valuation ring with fraction field `K = Frac R` and residue field `k`, and let
`W : WeierstrassCurve K` be given by an integral Weierstrass equation (`IsIntegral R W`).  Following
Silverman (AEC VII.2, IV.1) the identification `E₁(K) ≅ Ê(𝔪)` is built through the
**local parameter** `z(P) = -x(P)/y(P)`.  This file supplies the *set-level* half of that
identification: the parameter as a map into the maximal ideal `𝔪` of `R`, together with its
membership and normalisation (`z(O) = 0`).

For a point `P = (x, y)` that **reduces to the origin** (`ReducesToZero R W P`, i.e. `1 < v x`), the
`y`-pole strictly dominates the `x`-pole (`valuation_lt_of_one_lt`), so the ratio `-x/y` has
valuation `< 1` (`valuation_neg_x_div_y_lt_one`) and hence lifts to an element of the maximal ideal
of `R` (`exists_lift_of_le_one` + `valuation_lt_one_iff_mem`).  The origin and integral points map
to `0`.

This is deliverable 1 of issue #361 (the `zParam` map into `𝔪` + membership + `map_zero`).  The
addition-law compatibility `z(P + Q) = F_E(z P, z Q)` (the heart, AEC IV.1 / VII.2.2) and the
packaging into the group isomorphism `E₁(K) ≃+ Ê(𝔪)` are not here; both are **merged**, as
`WeierstrassCurve.zParamHatEquiv_map_add` and `WeierstrassCurve.E₁AddEquiv`
(`EllipticCurves/Reduction/KernelFormalGroupIso.lean`).

⚠️ **The opening paragraph used to call it the *"eventual"* identification, and the word outlived
the thing it described.**  `WeierstrassCurve.E₁AddEquiv`
(`EllipticCurves.Reduction.KernelFormalGroupIso`, #368) has existed since 2026-08-09, and the
paragraph opening *"This is deliverable 1 of issue #361"* already says so.

⚠️ **The two were one claim written twice, and a keyword sweep split it in half.**  Both entered in
the same commit on 2026-08-02, when neither theorem existed: *"the **eventual** identification"* and
*"are **deferred to the sibling bricks**"*.  Both stopped being true at the same instant, when
`E₁AddEquiv` landed on 2026-08-09, and #1045's stale-gate sweep repaired only the second of them,
fifteen days on.  The reason is mechanical rather than a lapse: *"deferred to"* and *"sibling"* are
matched by **both** of that sweep's keyword greps, and *"eventual"* is matched by **neither**.
⚠️ **A claim spread over two sentences is repaired as a whole only if both sentences match the
grep.**  When one does not, the sweep leaves the file asserting the repair and the original at once,
which is a worse state than the uniformly stale one it started from.

⚠️ What the retired word got right, and what the opening paragraph still says: this file supplies
only the *set-level* half of the identification, and nothing about that scope has changed.

## Main definitions

* `WeierstrassCurve.localParam` — the local parameter `z(P) = -x/y ∈ K` (with `z(O) = 0` and
  integral points mapping to `0`).
* `WeierstrassCurve.localParamR` — the integral lift of `localParam` as an element of `R`.
* `WeierstrassCurve.zParam` — the packaged map `{P // ReducesToZero R W P} → ↥𝔪` into the maximal
  ideal, `P ↦ z(P)`.

## Main results

* `WeierstrassCurve.valuation_localParam_lt_one` — a point reducing to the origin has `v (z P) < 1`.
* `WeierstrassCurve.algebraMap_localParamR` — `localParamR` is a genuine lift of `localParam`.
* `WeierstrassCurve.localParamR_mem` — a point reducing to the origin has `localParamR P ∈ 𝔪`.
* `WeierstrassCurve.localParamR_zero`, `WeierstrassCurve.zParam_zero` — normalisation `z(O) = 0`.

## References

Silverman, *The Arithmetic of Elliptic Curves*, VII.2 Prop 2.2, IV.1.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum WithZero Multiplicative

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### The local parameter as an element of `K` -/

open Classical in
/-- The **local parameter** `z(P) = -x(P)/y(P)` of a point `P` on `W`, valued in `K`.  The origin
maps to `0`, and an integral point (`v x ≤ 1`, not reducing to the origin) also maps to `0`; only a
point reducing to the origin (`1 < v x`) has a genuine `-x/y`.  On that locus `-x/y` is the standard
local uniformiser at `O`. -/
noncomputable def localParam (W : WeierstrassCurve K) : W.toAffine.Point → K
  | .zero => 0
  | .some x y _ => if 1 < valuation K (maximalIdeal R) x then -x / y else 0

@[simp]
theorem localParam_zero (W : WeierstrassCurve K) : localParam R W .zero = 0 := rfl

theorem localParam_some (W : WeierstrassCurve K) {x y : K} {h : W.toAffine.Nonsingular x y} :
    localParam R W (.some x y h) =
      if 1 < valuation K (maximalIdeal R) x then -x / y else 0 := rfl

/-! ### Valuation of the local parameter -/

/-- For a point reducing to the origin the local parameter reduces into the maximal ideal:
`v (z P) < 1`.  On the pole branch this is `valuation_neg_x_div_y_lt_one`; the origin maps to `0`,
whose valuation is `0 < 1`. -/
theorem valuation_localParam_lt_one (W : WeierstrassCurve K) [IsIntegral R W]
    {P : W.toAffine.Point} (hP : ReducesToZero R W P) :
    valuation K (maximalIdeal R) (localParam R W P) < 1 := by
  cases P with
  | zero => rw [localParam_zero, map_zero]; exact zero_lt_one
  | some x y h =>
    rw [reducesToZero_some_iff] at hP
    rw [localParam_some, ite_eq_left hP]
    exact valuation_neg_x_div_y_lt_one R W h.1 hP

/-- The local parameter always has valuation `≤ 1`, so it lifts to `R`. -/
theorem valuation_localParam_le_one (W : WeierstrassCurve K) [IsIntegral R W]
    (P : W.toAffine.Point) :
    valuation K (maximalIdeal R) (localParam R W P) ≤ 1 := by
  cases P with
  | zero => rw [localParam_zero, map_zero]; exact zero_le_one
  | some x y h =>
    rw [localParam_some]
    split_ifs with hx
    · exact le_of_lt (valuation_neg_x_div_y_lt_one R W h.1 hx)
    · rw [map_zero]; exact zero_le_one

/-! ### The integral lift into the maximal ideal -/

open Classical in
/-- The integral lift of the local parameter: since `v (z P) ≤ 1`, the parameter `z P ∈ K` is the
image of a (unique) element of `R`, which this definition selects. -/
noncomputable def localParamR (W : WeierstrassCurve K) [IsIntegral R W]
    (P : W.toAffine.Point) : R :=
  (exists_lift_of_le_one (valuation_localParam_le_one R W P)).choose

/-- `localParamR` is a genuine lift of `localParam`:
`algebraMap R K (localParamR P) = localParam P`. -/
theorem algebraMap_localParamR (W : WeierstrassCurve K) [IsIntegral R W]
    (P : W.toAffine.Point) :
    algebraMap R K (localParamR R W P) = localParam R W P :=
  (exists_lift_of_le_one (valuation_localParam_le_one R W P)).choose_spec

@[simp]
theorem localParamR_zero (W : WeierstrassCurve K) [IsIntegral R W] :
    localParamR R W .zero = 0 :=
  IsFractionRing.injective R K <| by rw [algebraMap_localParamR, localParam_zero, map_zero]

/-- **The local parameter lands in the maximal ideal** for a point reducing to the origin:
`localParamR P ∈ 𝔪`.  This is the membership `-x/y ∈ 𝔪` witnessing `z(P) ∈ Ê(𝔪)`. -/
theorem localParamR_mem (W : WeierstrassCurve K) [IsIntegral R W]
    {P : W.toAffine.Point} (hP : ReducesToZero R W P) :
    localParamR R W P ∈ (maximalIdeal R).asIdeal := by
  have h : valuation K (maximalIdeal R) (algebraMap R K (localParamR R W P)) < 1 := by
    rw [algebraMap_localParamR]; exact valuation_localParam_lt_one R W hP
  exact (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) (localParamR R W P)).mp h

/-! ### The packaged map into the maximal ideal -/

/-- The **local-parameter map** `z : E₁(K) → 𝔪`, `P ↦ z(P) = -x/y`, from the points reducing to the
origin into the maximal ideal `𝔪` of `R` — the carrier of `Ê(𝔪)`.  The addition-law compatibility
`z(P + Q) = F_E(z P, z Q)` and the resulting group isomorphism `E₁(K) ≃+ Ê(𝔪)` are the remaining
content of issue #361. -/
noncomputable def zParam (W : WeierstrassCurve K) [IsIntegral R W]
    (P : {P : W.toAffine.Point // ReducesToZero R W P}) : (maximalIdeal R).asIdeal :=
  ⟨localParamR R W P.1, localParamR_mem R W P.2⟩

@[simp]
theorem zParam_coe (W : WeierstrassCurve K) [IsIntegral R W]
    (P : {P : W.toAffine.Point // ReducesToZero R W P}) :
    (zParam R W P : R) = localParamR R W P.1 := rfl

@[simp]
theorem zParam_zero (W : WeierstrassCurve K) [IsIntegral R W] :
    zParam R W ⟨.zero, reducesToZero_zero R W⟩ = 0 :=
  Subtype.ext (localParamR_zero R W)

end WeierstrassCurve

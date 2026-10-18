/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.SecantReductionAdd
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.DoublingReductionAdd
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.TwoTorsionReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `redPt` additivity on the good-reduction locus (both summands integral)

Let `R` be a discrete valuation ring with fraction field `K = Frac R` and residue field `k`, and let
`W : WeierstrassCurve K` have good reduction.  This file assembles the individual "rung" lemmas of
the homomorphism property `redPt (P + Q) = redPt P + redPt Q` into the full statement **whenever
both summands are integral** (`v x₁ ≤ 1`, `v x₂ ≤ 1`) — i.e. on the good-reduction locus where
neither point lies in the kernel `E₁(K) = ker (redPt)`.

This is the geometrically substantive part of the reduction homomorphism (issue #383): it covers
every configuration of the reduced points `P̄, Q̄ ∈ Ẽ(k)`, dispatching to the appropriate rung:

* `redPt_add_of_reduced_X_ne` (#380) — the good-secant case `x̄₁ ≠ x̄₂`.
* `redPt_add_of_reduced_equal_nonvertical` / `redPt_add_self_of_reduced_nonvertical` (#381) — the
  reduced-doubling case `P̄ = Q̄` with `P̄` not `2`-torsion (secant `x₁ ≠ x₂` and true-doubling
  `P = Q` sub-configs).
* `redPt_add_of_secant_vertical` / `redPt_add_of_Y_eq` (#382) — the reduced-vertical case `Q̄ = -P̄`
  (`P̄` not `2`-torsion): the genuine secant `P + Q ∈ E₁`, and the literal `P + Q = O`.
* `redPt_add_of_reduced_two_torsion_secant` / `redPt_add_self_of_reduced_two_torsion` (#385) — the
  reduced `2`-torsion edge `P̄ = Q̄ = -P̄`.

The kernel cases needed for the full `map_add` — `P` or `Q` in `E₁(K)` — are the kernel × kernel
closure `redPt_add_of_reducesToZero` (#382) and the kernel × integral case (#384), and this file is
one of the four bricks the #383 assembly glues together to obtain the unconditional homomorphism.

⚠️ **That assembly is not pending: it is `EllipticCurves.Reduction.ReductionHom`, and this
paragraph predicted it in the future tense for fifteen days.**  As written on 2026-08-09 it said the
kernel cases *"**are** … the kernel × integral case (#384)"* and that this file is *"exactly the
on-`main` brick that the #383 assembly glues to those"* — a prediction that both were still to come.
Both landed the same afternoon:

* **#384** — `redPt_add_of_mem_E₁_left` and `redPt_add_of_mem_E₁_right`
  (`EllipticCurves.Reduction.KernelIntegralReduction`), committed **nine minutes** after this
  paragraph was;
* **#383** — `redPt_add`, unconditional in both summands, together with the packaged homomorphism
  `redHom`, the kernel identification `E₁_eq_ker` and the descended `redQuotientHom`
  (`EllipticCurves.Reduction.ReductionHom`), **thirty-six minutes** later.

⚠️ **What the paragraph got right is the part that stays.**  This file really does prove only the
both-integral case, `redPt_add_of_both_integral` really is one brick of four, and `ReductionHom`
really does glue it to the other three — its own dispatch list names this file, by theorem name and
by issue number.  **Nothing here is superseded; the theorem named in this file's `## Main result`
section is exactly what `ReductionHom` consumes.**

⚠️ The citation runs one way only, and that is why this went unnoticed: `ReductionHom` imports this
file and names it, this file imports and names nothing downstream, and no build could ever object.
A reader arriving at `ReductionHom` learns that the homomorphism is finished; a reader arriving
here — which is where the case dispatch is explained — learned that it was not.

## Main result

* `WeierstrassCurve.redPt_add_of_both_integral` — for integral `P, Q`,
  `redPt (P + Q) = redPt P + redPt Q`.

## References

Silverman, *The Arithmetic of Elliptic Curves*, VII.2 Prop 2.1.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum WithZero Multiplicative IsLocalRing

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open Classical in
/-- **Additivity of `redPt` on the good-reduction locus.**  If `P = (x₁, y₁)` and `Q = (x₂, y₂)` are
both integral (`v xᵢ ≤ 1`), then `redPt (P + Q) = redPt P + redPt Q`.  The proof dispatches on the
configuration of the reduced points `P̄, Q̄` (equal/distinct reduced `x`, vertical, `2`-torsion) to
the corresponding rung lemma. -/
theorem redPt_add_of_both_integral (W : WeierstrassCurve K) [HasGoodReduction R W]
    {x₁ y₁ x₂ y₂ : K} {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂}
    (hvx₁ : valuation K (maximalIdeal R) x₁ ≤ 1) (hvx₂ : valuation K (maximalIdeal R) x₂ ≤ 1) :
    redPt R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = redPt R W (.some x₁ y₁ h₁) + redPt R W (.some x₂ y₂ h₂) := by
  haveI : (reduction R W).IsElliptic :=
    (hasGoodReduction_iff_isElliptic_reduction R).mp inferInstance
  have hcurve : (integralModel R W).toAffine.map (algebraMap R K) = W.toAffine :=
    baseChange_integralModel_eq R W
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  -- integral lifts of the four coordinates
  obtain ⟨x₀₁, hx₀₁⟩ := exists_lift_of_le_one hvx₁
  obtain ⟨y₀₁, hy₀₁⟩ := exists_lift_of_le_one (valuation_y_le_one_of_le_one R W h₁.1 hvx₁)
  obtain ⟨x₀₂, hx₀₂⟩ := exists_lift_of_le_one hvx₂
  obtain ⟨y₀₂, hy₀₂⟩ := exists_lift_of_le_one (valuation_y_le_one_of_le_one R W h₂.1 hvx₂)
  -- the Weierstrass equation transfers to the integral model and thence to the residue field
  have hEqP : (integralModel R W).toAffine.Equation x₀₁ y₀₁ := by
    rw [← Affine.map_equation (W := (integralModel R W).toAffine) hinj x₀₁ y₀₁, hx₀₁, hy₀₁, hcurve]
    exact h₁.1
  have hEqQ : (integralModel R W).toAffine.Equation x₀₂ y₀₂ := by
    rw [← Affine.map_equation (W := (integralModel R W).toAffine) hinj x₀₂ y₀₂, hx₀₂, hy₀₂, hcurve]
    exact h₂.1
  have hnsP : (reduction R W).toAffine.Nonsingular (residue R x₀₁) (residue R y₀₁) :=
    (Affine.equation_iff_nonsingular).mp (hEqP.map (residue R))
  have hnsQ : (reduction R W).toAffine.Nonsingular (residue R x₀₂) (residue R y₀₂) :=
    (Affine.equation_iff_nonsingular).mp (hEqQ.map (residue R))
  -- reductions of `P` and `Q` in lift-agnostic form
  have hRP : redPt R W (.some x₁ y₁ h₁) = .some (residue R x₀₁) (residue R y₀₁) hnsP :=
    redPt_some_eq R W hx₀₁ hy₀₁ hnsP
  have hRQ : redPt R W (.some x₂ y₂ h₂) = .some (residue R x₀₂) (residue R y₀₂) hnsQ :=
    redPt_some_eq R W hx₀₂ hy₀₂ hnsQ
  -- a `-P̄ = Q̄` witness collapses the RHS to `0`
  have rhs_zero : ∀ (_hy : residue R y₀₁
        = (reduction R W).toAffine.negY (residue R x₀₂) (residue R y₀₂)),
      residue R x₀₁ = residue R x₀₂ →
      redPt R W (.some x₁ y₁ h₁) + redPt R W (.some x₂ y₂ h₂) = 0 := by
    intro hy hxr
    rw [hRP, hRQ]
    exact Affine.Point.add_of_Y_eq hxr hy
  by_cases hxr : residue R x₀₁ = residue R x₀₂
  · -- reduced `x`-coordinates agree
    by_cases hxK : x₁ = x₂
    · -- the `x`-coordinates already agree over `K`: doubling or literal vertical
      by_cases hyK : y₁ = y₂
      · -- `P = Q`
        subst hxK
        subst hyK
        have hh : h₁ = h₂ := Subsingleton.elim h₁ h₂
        subst hh
        by_cases hv2 : y₁ = W.toAffine.negY x₁ y₁
        · -- `P + P = O`: `P = -P`, so `redPt P + redPt P = 0`
          have hL : redPt R W (.some x₁ y₁ h₁ + .some x₁ y₁ h₁) = 0 :=
            redPt_add_of_Y_eq R W rfl hv2
          have hPQ0 : (Affine.Point.some x₁ y₁ h₁) + (Affine.Point.some x₁ y₁ h₁) = 0 :=
            Affine.Point.add_of_Y_eq rfl hv2
          have hself : (Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point)
              = -(Affine.Point.some x₁ y₁ h₁) := eq_neg_of_add_eq_zero_right hPQ0
          have ha : redPt R W (.some x₁ y₁ h₁) = - redPt R W (.some x₁ y₁ h₁) := by
            conv_lhs => rw [hself]
            rw [redPt_neg]
          have hR : redPt R W (.some x₁ y₁ h₁) + redPt R W (.some x₁ y₁ h₁) = 0 := by
            nth_rewrite 2 [ha]; rw [add_neg_cancel]
          rw [hL, hR]
        · -- doubling, `P` not `2`-torsion over `K`
          by_cases h2t : residue R y₀₁
              = (reduction R W).toAffine.negY (residue R x₀₁) (residue R y₀₁)
          · -- reduced `2`-torsion
            have hyr' : residue R y₀₁ = residue R y₀₂ := by
              have he : y₀₁ = y₀₂ := hinj (by rw [hy₀₁, hy₀₂])
              rw [he]
            have hL : redPt R W (.some x₁ y₁ h₁ + .some x₁ y₁ h₁) = 0 :=
              redPt_add_self_of_reduced_two_torsion R W hx₀₁ hy₀₁ hvx₁ hv2 h2t
            have hR := rhs_zero (by rw [← hyr', ← hxr]; exact h2t) hxr
            rw [hL, hR]
          · -- reduced non-`2`-torsion doubling
            exact redPt_add_self_of_reduced_nonvertical R W hx₀₁ hy₀₁ h2t
      · -- `x₁ = x₂` but `y₁ ≠ y₂`: `P = -Q`, hence `P + Q = O`
        have hyneg : y₁ = W.toAffine.negY x₂ y₂ :=
          (Affine.Y_eq_of_X_eq h₁.1 h₂.1 hxK).resolve_left hyK
        have hL : redPt R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) = 0 :=
          redPt_add_of_Y_eq R W hxK hyneg
        have hPQ0 : (Affine.Point.some x₁ y₁ h₁) + (Affine.Point.some x₂ y₂ h₂) = 0 :=
          Affine.Point.add_of_Y_eq hxK hyneg
        have hQP : (Affine.Point.some x₂ y₂ h₂ : W.toAffine.Point)
            = -(Affine.Point.some x₁ y₁ h₁) := eq_neg_of_add_eq_zero_right hPQ0
        have hR : redPt R W (.some x₁ y₁ h₁) + redPt R W (.some x₂ y₂ h₂) = 0 := by
          rw [hQP, redPt_neg, add_neg_cancel]
        rw [hL, hR]
    · -- secant over `K` (`x₁ ≠ x₂`), reduced `x`-coordinates equal
      by_cases hyr : residue R y₀₁ = residue R y₀₂
      · -- reduced points equal
        by_cases h2t : residue R y₀₁
            = (reduction R W).toAffine.negY (residue R x₀₁) (residue R y₀₁)
        · -- reduced `2`-torsion secant
          have hL : redPt R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) = 0 :=
            redPt_add_of_reduced_two_torsion_secant R W hx₀₁ hy₀₁ hx₀₂ hy₀₂ hvx₁ hvx₂ hxK hxr hyr
              h2t
          have hR := rhs_zero (by rw [← hyr, ← hxr]; exact h2t) hxr
          rw [hL, hR]
        · -- reduced non-`2`-torsion, equal: reduced-doubling secant
          exact redPt_add_of_reduced_equal_nonvertical R W hx₀₁ hy₀₁ hx₀₂ hy₀₂ hxK hxr hyr h2t
      · -- reduced points distinct with equal `x`: they are reduced negatives (vertical secant)
        have hy : residue R y₀₁
            = (reduction R W).toAffine.negY (residue R x₀₂) (residue R y₀₂) :=
          (Affine.Y_eq_of_X_eq (hEqP.map (residue R)) (hEqQ.map (residue R)) hxr).resolve_left hyr
        -- the valuation-domination hypothesis of `redPt_add_of_secant_vertical`
        have hxmem : x₀₁ - x₀₂ ∈ IsLocalRing.maximalIdeal R :=
          (IsLocalRing.residue_eq_zero_iff _).mp (by rw [map_sub, hxr, sub_self])
        have hxsub : valuation K (maximalIdeal R) (x₁ - x₂) < 1 := by
          have he : algebraMap R K (x₀₁ - x₀₂) = x₁ - x₂ := by rw [map_sub, hx₀₁, hx₀₂]
          rw [← he]; exact (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) _).mpr hxmem
        have hymem : y₀₁ - y₀₂ ∉ IsLocalRing.maximalIdeal R := fun hmem =>
          hyr (sub_eq_zero.mp (by
            have := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
            rwa [map_sub] at this))
        have hysub : valuation K (maximalIdeal R) (y₁ - y₂) = 1 := by
          have he : algebraMap R K (y₀₁ - y₀₂) = y₁ - y₂ := by rw [map_sub, hy₀₁, hy₀₂]
          rw [← he, valuation_eq_one_iff_notMem]; exact hymem
        have hlt : valuation K (maximalIdeal R) (x₁ - x₂)
            < valuation K (maximalIdeal R) (y₁ - y₂) := by rw [hysub]; exact hxsub
        have hL : redPt R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) = 0 :=
          redPt_add_of_secant_vertical R W hxK hvx₁ hvx₂ hlt
        have hR := rhs_zero hy hxr
        rw [hL, hR]
  · -- reduced `x`-coordinates distinct: good secant
    exact redPt_add_of_reduced_X_ne R W hx₀₁ hy₀₁ hx₀₂ hy₀₂ hxr

end WeierstrassCurve

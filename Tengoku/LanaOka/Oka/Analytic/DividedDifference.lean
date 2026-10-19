/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Analysis.Calculus.DSlope
import Tengoku.Seed.Analysis.Complex.CauchyIntegral
import Tengoku.LanaOka.Oka.Analytic.ParametricCircleIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The divided difference of a holomorphic function is analytic in *both* variables

For `h` holomorphic on a disc, Mathlib's `dslope h a b` is `(h b - h a) / (b - a)` off the
diagonal and `deriv h a` on it, and `sub_smul_dslope` gives the divided-difference identity

```
(b - a) • dslope h a b = h b - h a
```

for free. Every lemma about `dslope` in Mathlib, however, fixes `a` and varies `b`. This file
supplies the missing statement: **`(a, b) ↦ dslope h a b` is analytic as a function of the pair**,
on the open polydisc of the disc on which `h` is holomorphic.

Joint analyticity is what a consumer substituting two holomorphic functions into `dslope` needs,
and it does not follow from analyticity in each variable separately — that implication is
Hartogs' theorem, **and nothing below uses it**. It is proved here without it:
`analyticAt_dslope_pair` goes through the Cauchy formula on a polydisc, so no result in this file
turns on whether Hartogs' theorem is available anywhere.

**The clause asserting its absence from Mathlib is retired rather than instrumented, because no
scan decides it.** At `v4.32.0` — the revision `lakefile.toml` pins, resolved by
`lake-manifest.json` to `81a5d257c8e410db227a6665ed08f64fea08e997` — **0** names in the
environment of `import Mathlib` write *hartogs* in any case. That
narrows and does not decide: the implication can be stated without the name, so the thing being
denied can be spelled another way, and what that calls for is a sentence that says so rather than
a number. What is left is the statement about this file, which is checkable here. **That clause read
*that implication is Hartogs' theorem, which Mathlib does not have* until 2026-09-21**; `git show
c6bfc1f:Oka/Analytic/DividedDifference.lean` carries the retired wording at `:25–26`, wrapped
after *is*.

## The argument

`dividedDifference R h` is the Cauchy kernel with two poles,

```
(2πi)⁻¹ ∮_{|ζ| = R} ((ζ - a)(ζ - b))⁻¹ h ζ dζ,
```

which is jointly analytic because it is a circle integral depending holomorphically on the
parameter: that is `analyticAt_circleIntegral` of `Oka/Analytic/ParametricCircleIntegral.lean`,
whose two hypotheses here amount to `‖a‖, ‖b‖ < R = ‖ζ‖`, so neither pole meets the contour.
Partial fractions and the Cauchy integral formula identify it with the difference quotient off
the diagonal, and continuity — analyticity on one side, `continuousAt_dslope_same` on the other
— identifies it with `dslope` on the diagonal too.

Note that **only joint *differentiability* is ever needed**, never joint analyticity:
`analyticAt_circleIntegral` is proved from the Cauchy formula on a polydisc, and the same file's
`analyticAt_of_differentiableOn` is the general statement that a differentiable function of
several complex variables is analytic. That is why Hartogs does not arise.

## Main results

- `analyticAt_dslope_pair`: **`fun x : Fin 2 → ℂ ↦ dslope h (x 0) (x 1)` is analytic** at every
  point of the open polydisc of radius `R`, for `h` differentiable on `closedBall 0 R`.
- `AnalyticAt.dslope_comp`: consequently `z ↦ dslope h (G z) (G' z)` is analytic wherever `G`
  and `G'` are, provided their values at the point lie in the disc. This is the form a consumer
  substituting two holomorphic functions wants.
- `dividedDifference_eq_dslope`: the Cauchy-kernel formula computes `dslope`.
- `sub_eq_mul_dividedDifference`: the divided-difference identity for the Cauchy-kernel formula,
  proved directly and used to identify it with `dslope`.

## Status: no consumer in this repository, and that is expected

**No proof in `Oka/` uses `AnalyticAt.dslope_comp`, and it should not be deleted on that
account.** It is cited in the module docstrings of `Oka/AnalyticSpace/HolomorphicMap.lean` and
`Oka/AnalyticSpace/HolomorphicMapGeneral.lean`. What it has no consumer *for* is a proof in the
library. It was built for the independence-of-lift step that `Hom(Z, ℂ) ≃ Γ(Z, 𝒪_Z)` was expected to
need: two lifts of the same section differ by an element of the ideal cutting out the chart, and
`h(G) - h(G')` has to be shown to lie in that ideal, for which the cofactor `dslope h (G ·) (G' ·)`
must be holomorphic. **That route was abandoned**:
`ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace` discharges the compatibility directly,
once `ComplexAnalytic.AnalyticSpace.restrict` makes a chart overlap an analytic space, so no
independence argument is needed at all. The analytification programme, the last place a consumer
could have appeared, does not use it either.

**What is here is nevertheless general one-variable complex analysis with no counterpart in
Mathlib at `v4.32.0`**, and the claim is bounded to the declarations above rather than to a body
of mathematics. Nothing in this file mentions analytic spaces, sheaves or anything else from this
repository; `AnalyticAt.dslope_comp` is stated over an arbitrary `ℂ`-normed space.

**The bound is an enumeration, at the rev `lake-manifest.json` resolves that version to,
`81a5d257c8e410db227a6665ed08f64fea08e997`.** Over the environment of `import Mathlib` there,
exactly **35** non-internal declarations have a type mentioning the constant `dslope`, and **not
one of the 35 mentions `AnalyticAt`, `AnalyticOn`, `AnalyticOnNhd` or `AnalyticWithinAt`**. The
only four whose types mention a power series at all are
`HasFPowerSeriesAt.has_fpower_series_dslope_fslope`,
`HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope`,
`HasFPowerSeriesAt.iterate_dslope_fslope_ne_zero` and
`HasFPowerSeriesAt.eq_pow_order_mul_iterate_dslope`, and every one of the 35 applies `dslope` to a
function and a **fixed** first argument — which is the reading of *fixes the first argument and
varies the second* the sentence above used to assert with no run behind it. **A statement about
the pair has to mention the constant `dslope` in its own type**, whatever it is called, so the
scan decides rather than narrows; the other half of this file is bounded the same way, no name in
that environment writing *dividedDifference* in any case.

**The environment dump is the weaker of the two routes and says so here**: six of the 35 — the
five in the `Complex` namespace and `Real`'s `sinc_eq_dslope` — are absent from the environment of
`Oka` that `scripts/DumpEnvNames.lean` dumps, because this repository imports part of Mathlib and
not all of it, so a zero in that dump would be a statement about this build's imports and not about
Mathlib. That is why the figures above are taken over `import Mathlib` instead.

So the absence of an in-repo consumer is
what an upstreaming candidate looks like, not what dead code looks like, and this paragraph exists
so that the observation is not re-reported a sixth time in place of a decision.

**That sentence read *What is here is nevertheless general one-variable complex analysis that
Mathlib does not have.* until 2026-09-21, and the clause warranting it read *Every `dslope` lemma
in Mathlib fixes the first argument and varies the second, so the statement about the pair is
absent there — checked by conclusion rather than by name.*** — *pair* italicised there, and the
italics are dropped inside this quotation because they do not nest. `git show
c6bfc1f:Oka/Analytic/DividedDifference.lean` carries both at `:76–80`. **The universal is narrowed
to this file's declarations and the check is now a run**: as published, *general one-variable
complex analysis* quantified over a body of mathematics that no instrument could have swept, and
*checked by conclusion* named no command, no version and no figure. The claim about `dslope` is
unchanged and is now measured.

**For a future upstreaming pass**, the file should be split rather than moved whole:
`analyticAt_dslope_pair` belongs beside `Mathlib/Analysis/Calculus/DSlope.lean`, and
`dividedDifference` with its Cauchy-kernel lemmas belongs wherever
`Oka/Analytic/ParametricCircleIntegral.lean` ends up, since it is about the several-variables
Cauchy formula as much as about `dslope`.

## References

- [Lars Hörmander, *An introduction to complex analysis in several variables*][hormander1990],
  §2.2
-/

open Complex Metric
open scoped Topology Real

noncomputable section

variable {R : ℝ} {h : ℂ → ℂ}

/-- **The divided difference of `h` on the disc of radius `R` about the origin**, defined by the
Cauchy kernel with poles at the two arguments.

`dividedDifference_eq_dslope` identifies this with Mathlib's `dslope`; the reason for
introducing it at all is that this formula is visibly analytic in the pair `x`, which `dslope`
is not. -/
def dividedDifference (R : ℝ) (h : ℂ → ℂ) (x : Fin 2 → ℂ) : ℂ :=
  (2 * π * I : ℂ)⁻¹ * ∮ ζ in C(0, R), ((ζ - x 0) * (ζ - x 1))⁻¹ * h ζ

/-- A point strictly inside the circle is not on it, in the form the Cauchy kernel needs. -/
lemma sub_ne_zero_of_mem_sphere_of_norm_lt {w ζ : ℂ} (hw : ‖w‖ < R)
    (hζ : ζ ∈ sphere (0 : ℂ) R) : ζ - w ≠ 0 := by
  rw [mem_sphere_iff_norm, sub_zero] at hζ
  rw [sub_ne_zero]
  exact fun hcon ↦ absurd (hcon ▸ hζ) hw.ne

/-- The Cauchy integral formula, in the multiplicative form used below. -/
lemma circleIntegral_sub_inv_mul (hd : DifferentiableOn ℂ h (closedBall 0 R)) {w : ℂ}
    (hw : ‖w‖ < R) : (∮ ζ in C(0, R), (ζ - w)⁻¹ * h ζ) = (2 * π * I : ℂ) * h w := by
  have := hd.circleIntegral_sub_inv_smul (w := w) (by simpa [Complex.dist_eq] using hw)
  simpa only [smul_eq_mul] using this

/-- The integrand of the Cauchy integral formula is circle-integrable. -/
lemma circleIntegrable_sub_inv_mul (hR : 0 < R) (hd : DifferentiableOn ℂ h (closedBall 0 R))
    {w : ℂ} (hw : ‖w‖ < R) : CircleIntegrable (fun ζ ↦ (ζ - w)⁻¹ * h ζ) 0 R := by
  refine ContinuousOn.circleIntegrable hR.le ?_
  refine ContinuousOn.mul ?_ (hd.continuousOn.mono sphere_subset_closedBall)
  exact ContinuousOn.inv₀ (by fun_prop) fun ζ hζ ↦
    sub_ne_zero_of_mem_sphere_of_norm_lt hw hζ

/-- **The divided-difference identity for `dividedDifference`.**

Partial fractions turn the kernel with two poles into the difference of two Cauchy kernels, and
the Cauchy integral formula evaluates each. The diagonal case is free: both sides vanish. -/
theorem sub_eq_mul_dividedDifference (hR : 0 < R) (hd : DifferentiableOn ℂ h (closedBall 0 R))
    {a b : ℂ} (ha : ‖a‖ < R) (hb : ‖b‖ < R) :
    h a - h b = (a - b) * dividedDifference R h ![a, b] := by
  rcases eq_or_ne a b with rfl | hab
  · simp
  have hsplit : (∮ ζ in C(0, R), ((ζ - a) * (ζ - b))⁻¹ * h ζ) =
      (a - b)⁻¹ * ((∮ ζ in C(0, R), (ζ - a)⁻¹ * h ζ) - ∮ ζ in C(0, R), (ζ - b)⁻¹ * h ζ) := by
    rw [← circleIntegral.integral_sub (circleIntegrable_sub_inv_mul hR hd ha)
        (circleIntegrable_sub_inv_mul hR hd hb), ← circleIntegral.integral_const_mul]
    refine circleIntegral.integral_congr hR.le fun ζ hζ ↦ ?_
    have h1 : ζ - a ≠ 0 := sub_ne_zero_of_mem_sphere_of_norm_lt ha hζ
    have h2 : ζ - b ≠ 0 := sub_ne_zero_of_mem_sphere_of_norm_lt hb hζ
    field_simp
    ring
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  simp only [dividedDifference, Matrix.cons_val_zero, Matrix.cons_val_one, hsplit,
    circleIntegral_sub_inv_mul hd ha, circleIntegral_sub_inv_mul hd hb]
  field_simp

/-- **`dividedDifference R h` is analytic at every point of the open polydisc of radius `R`.**

This is `analyticAt_circleIntegral` applied to the two-pole Cauchy kernel, recentred at the
point by `analyticAt_of_shift`; the two hypotheses reduce to the poles not meeting the contour,
which is `‖x₀ i‖ + ρ < R` for a small enough polyradius `ρ`. -/
theorem analyticAt_dividedDifference (hR : 0 < R) (hd : DifferentiableOn ℂ h (closedBall 0 R))
    {x₀ : Fin 2 → ℂ} (hx₀ : ∀ i, ‖x₀ i‖ < R) :
    AnalyticAt ℂ (dividedDifference R h) x₀ := by
  set M : ℝ := max ‖x₀ 0‖ ‖x₀ 1‖ with hM
  have hMR : M < R := max_lt (hx₀ 0) (hx₀ 1)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (le_max_left _ _)
  set ρ : ℝ := (R - M) / 2 with hρdef
  have hρ : 0 < ρ := by simp only [hρdef]; linarith
  have hbound : ∀ i : Fin 2, ‖x₀ i‖ + ρ < R := by
    intro i
    have : ‖x₀ i‖ ≤ M := by
      fin_cases i
      exacts [le_max_left _ _, le_max_right _ _]
    simp only [hρdef]
    linarith
  have hne : ∀ (x : Fin 2 → ℂ), (∀ i, ‖x i‖ ≤ ρ) → ∀ ζ : ℂ, ‖ζ‖ = R → ∀ i,
      ζ - (x₀ i + x i) ≠ 0 := by
    intro x hx ζ hζ i
    rw [sub_ne_zero]
    intro hcon
    have : ‖ζ‖ ≤ ‖x₀ i‖ + ρ := hcon ▸ (norm_add_le _ _).trans (by gcongr; exact hx i)
    rw [hζ] at this
    exact absurd this (not_le.2 (hbound i))
  set S : Set (Fin 2 → ℂ) := Set.univ.pi fun _ : Fin 2 ↦ closedBall (0 : ℂ) ρ with hS
  have hmemS : ∀ x ∈ S, ∀ i, ‖x i‖ ≤ ρ := by
    intro x hx i
    simpa using hx i (Set.mem_univ i)
  have hcirc : ∀ θ : ℝ, ‖circleMap 0 R θ‖ = R := by
    intro θ
    simpa [mem_sphere_iff_norm] using circleMap_mem_sphere (0 : ℂ) hR.le θ
  have key : AnalyticAt ℂ (fun x : Fin 2 → ℂ ↦
      ∮ ζ in C(0, R), ((ζ - (x₀ 0 + x 0)) * (ζ - (x₀ 1 + x 1)))⁻¹ * h ζ) 0 := by
    refine analyticAt_circleIntegral (m := 2) hR hρ ?_ ?_
    · intro ζ hζ
      have hden : DifferentiableOn ℂ
          (fun x : Fin 2 → ℂ ↦ (ζ - (x₀ 0 + x 0)) * (ζ - (x₀ 1 + x 1))) S := by fun_prop
      refine DifferentiableOn.mul_const ?_ (h ζ)
      refine hden.inv fun x hx ↦ ?_
      exact mul_ne_zero (hne x (hmemS x hx) ζ hζ 0) (hne x (hmemS x hx) ζ hζ 1)
    · have hcm : Continuous fun p : S × ℝ ↦ circleMap 0 R p.2 :=
        (continuous_circleMap 0 R).comp continuous_snd
      have hmem : ∀ p : S × ℝ, circleMap 0 R p.2 ∈ closedBall (0 : ℂ) R := fun p ↦ by
        simp [hcirc p.2]
      have hh : Continuous fun p : S × ℝ ↦ h (circleMap 0 R p.2) :=
        hd.continuousOn.comp_continuous hcm hmem
      have hx : ∀ i : Fin 2, Continuous fun p : S × ℝ ↦ (p.1 : Fin 2 → ℂ) i := fun i ↦
        (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)
      refine Continuous.mul (Continuous.inv₀ (by fun_prop) fun p ↦ ?_) hh
      exact mul_ne_zero (hne _ (hmemS _ p.1.2) _ (hcirc p.2) 0)
        (hne _ (hmemS _ p.1.2) _ (hcirc p.2) 1)
  have key2 : AnalyticAt ℂ (fun x : Fin 2 → ℂ ↦ dividedDifference R h (x₀ + x)) 0 := by
    refine ((analyticAt_const (v := (2 * π * I : ℂ)⁻¹)).mul key).congr ?_
    filter_upwards with x
    simp [dividedDifference]
  exact analyticAt_of_shift key2

/-- Off the diagonal, `dividedDifference` is the difference quotient, i.e. `dslope`. -/
lemma dividedDifference_eq_dslope_of_ne (hR : 0 < R)
    (hd : DifferentiableOn ℂ h (closedBall 0 R)) {a b : ℂ} (ha : ‖a‖ < R) (hb : ‖b‖ < R)
    (hab : b ≠ a) : dividedDifference R h ![a, b] = dslope h a b := by
  rw [dslope_of_ne _ hab, slope_def_field, eq_div_iff (sub_ne_zero.2 hab)]
  have := sub_eq_mul_dividedDifference hR hd ha hb
  linear_combination this

/-- **The Cauchy-kernel formula computes `dslope`**, on the diagonal as well as off it.

Off the diagonal this is `dividedDifference_eq_dslope_of_ne`. On it, both sides are continuous
at the point — the left by `analyticAt_dividedDifference`, the right by
`continuousAt_dslope_same`, which is where the differentiability of `h` is used — and they agree
on a punctured neighbourhood, so they agree. -/
theorem dividedDifference_eq_dslope (hR : 0 < R) (hd : DifferentiableOn ℂ h (closedBall 0 R))
    {a b : ℂ} (ha : ‖a‖ < R) (hb : ‖b‖ < R) :
    dividedDifference R h ![a, b] = dslope h a b := by
  rcases eq_or_ne b a with rfl | hab
  · have hball : ball (0 : ℂ) R ∈ 𝓝 b :=
      isOpen_ball.mem_nhds (by simpa [mem_ball_zero_iff] using hb)
    have hdiffAt : DifferentiableAt ℂ h b :=
      hd.differentiableAt (Filter.mem_of_superset hball ball_subset_closedBall)
    have hfc : ContinuousAt (fun w : ℂ ↦ dividedDifference R h ![b, w]) b := by
      have hana : AnalyticAt ℂ (dividedDifference R h) ![b, b] :=
        analyticAt_dividedDifference hR hd fun i ↦ by fin_cases i <;> simpa using hb
      have hin : Continuous fun w : ℂ ↦ (![b, w] : Fin 2 → ℂ) := by
        refine continuous_pi fun i ↦ ?_
        fin_cases i
        · simpa using continuous_const
        · simpa using continuous_id'
      exact ContinuousAt.comp (g := dividedDifference R h)
        (f := fun w : ℂ ↦ (![b, w] : Fin 2 → ℂ)) (x := b) hana.continuousAt hin.continuousAt
    have hgc : ContinuousAt (dslope h b) b := continuousAt_dslope_same.2 hdiffAt
    have heq : (fun w : ℂ ↦ dividedDifference R h ![b, w]) =ᶠ[𝓝[≠] b] dslope h b := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hball] with w hw hwb
      exact dividedDifference_eq_dslope_of_ne hR hd hb
        (by simpa [mem_ball_zero_iff] using hwb) hw
    exact tendsto_nhds_unique hfc.continuousWithinAt.tendsto
      ((hgc.continuousWithinAt.tendsto).congr' heq.symm)
  · exact dividedDifference_eq_dslope_of_ne hR hd ha hb hab

/-- **The divided difference of a holomorphic function is analytic in the pair of its
arguments.**

For `h` differentiable on `closedBall 0 R`, the function `x ↦ dslope h (x 0) (x 1)` of two
complex variables is analytic at every point of the open polydisc of radius `R`. Every lemma
about `dslope` in Mathlib fixes the first argument; this is the statement about both at once,
and it is what makes `dslope` usable as a function of two holomorphic functions. -/
theorem analyticAt_dslope_pair (hR : 0 < R) (hd : DifferentiableOn ℂ h (closedBall 0 R))
    {x₀ : Fin 2 → ℂ} (hx₀ : ∀ i, ‖x₀ i‖ < R) :
    AnalyticAt ℂ (fun x : Fin 2 → ℂ ↦ dslope h (x 0) (x 1)) x₀ := by
  have hopen : IsOpen (Set.univ.pi fun _ : Fin 2 ↦ ball (0 : ℂ) R) :=
    isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_ball
  have hx₀mem : x₀ ∈ Set.univ.pi fun _ : Fin 2 ↦ ball (0 : ℂ) R := fun i _ ↦ by
    simpa [mem_ball_zero_iff] using hx₀ i
  refine (analyticAt_dividedDifference hR hd hx₀).congr ?_
  filter_upwards [hopen.mem_nhds hx₀mem] with x hx
  have hx' : ![x 0, x 1] = x := by funext i; fin_cases i <;> rfl
  have hxi : ∀ i, ‖x i‖ < R := fun i ↦ by
    simpa [mem_ball_zero_iff] using hx i (Set.mem_univ i)
  exact hx' ▸ dividedDifference_eq_dslope hR hd (hxi 0) (hxi 1)

/-- **Two holomorphic functions may be substituted into the divided difference.**

If `G` and `G'` are analytic at `z₀` with values there in the disc on which `h` is holomorphic,
then `z ↦ dslope h (G z) (G' z)` is analytic at `z₀`. This is `analyticAt_dslope_pair` composed
with `AnalyticAt.pi`, and it is the form in which joint analyticity is consumed: with only the
one-variable `dslope` lemmas of Mathlib, `G'` would have to be constant.

**No proof in the library uses this, and none is expected to**: the argument it was built for was
abandoned in favour of a uniqueness argument. It is retained as a Mathlib upstreaming candidate; see
`## Status` in the module docstring, which is the disposition rather than a fresh observation. -/
theorem AnalyticAt.dslope_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {G G' : E → ℂ} {z₀ : E} (hR : 0 < R) (hd : DifferentiableOn ℂ h (closedBall 0 R))
    (hG : AnalyticAt ℂ G z₀) (hG' : AnalyticAt ℂ G' z₀) (hGb : ‖G z₀‖ < R)
    (hG'b : ‖G' z₀‖ < R) : AnalyticAt ℂ (fun z ↦ dslope h (G z) (G' z)) z₀ := by
  have hpair : AnalyticAt ℂ (fun z : E ↦ (![G z, G' z] : Fin 2 → ℂ)) z₀ :=
    AnalyticAt.pi fun i ↦ by fin_cases i <;> simpa
  have houter : AnalyticAt ℂ (fun x : Fin 2 → ℂ ↦ dslope h (x 0) (x 1)) ![G z₀, G' z₀] :=
    analyticAt_dslope_pair hR hd fun i ↦ by fin_cases i <;> simpa
  exact AnalyticAt.comp (g := fun x : Fin 2 → ℂ ↦ dslope h (x 0) (x 1))
    (f := fun z : E ↦ (![G z, G' z] : Fin 2 → ℂ)) (x := z₀) houter hpair

end

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.InnerProductSpace.FrischWaughLovell
public import Tengoku

/-! # L2 Frisch-Waugh-Lovell Instance

This file instantiates the abstract Frisch-Waugh-Lovell development on
square-integrable real functions under a probability measure. It supplies
orthogonal projections for finite-dimensional nuisance subspaces, identifies
the `Lp` inner product with the corresponding population integral, and exposes
the residualized normal equations, least-squares optimality, and uniqueness
statements for the `L²(μ)` specialization. -/

@[expose] public section

namespace Causalean
namespace Stat
namespace FWLInstanceL2

open MeasureTheory
open scoped InnerProductSpace BigOperators

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- For a measurable sample space, [a measure on that sample space](hyp:μ), and
[a finite-dimensional real linear subspace of the square-integrable real functions
under that measure](hyp:H), [an orthogonal projection onto that subspace](goal)
exists.

The result follows because every finite-dimensional real inner-product subspace is complete.
@isnad1 id=hasortho.0h3v.s11.0cf250296788 from=translated src=- shape=8ab6a582 vocab=f05b9838
-/
instance hasOrthogonalProjection_of_finiteDimensional
    (H : Submodule ℝ (Lp ℝ 2 μ)) [FiniteDimensional ℝ H] :
    H.HasOrthogonalProjection :=
  inferInstance

/-- **L² inner product = integral pairing.** For two square-integrable real
random variables, the Hilbert-space inner product equals the integral of their
product, independent of the chosen representatives. This is the bridge between
abstract FWL inner products and the population second moments used in estimand
papers.
@isnad1 id=eq.0h4v.s9.a10388c8d139 from=translated src=- shape=c9026f45 vocab=f3cf7685
-/
theorem inner_eq_integral (f g : Lp ℝ 2 μ) :
    inner ℝ f g = ∫ a, f a * g a ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
  change inner ℝ (f a) (g a) = f a * g a
  exact mul_comm _ _

section FWL

variable {K : ℕ} (H : Submodule ℝ (Lp ℝ 2 μ)) [H.HasOrthogonalProjection]
  (X : Fin K → Lp ℝ 2 μ) (Y : Lp ℝ 2 μ)

/-- **Residualized normal equations on `L²(μ)`.** The FWL coefficient solves
`gramResid H X *ᵥ fwlCoef H X Y = residInnerVec H X Y` whenever the
residualized Gram matrix is invertible. Specialization of
`Causalean.Mathlib.FWL.gramResid_mulVec_fwlCoef`.
@isnad1 id=eq.1h6v.s10.55ea83158949 from=translated src=- shape=099412d0 vocab=9bde55ce
-/
theorem gramResid_mulVec_fwlCoef
    (hQ : IsUnit (Causalean.Mathlib.FWL.gramResid H X).det) :
    (Causalean.Mathlib.FWL.gramResid H X).mulVec (Causalean.Mathlib.FWL.fwlCoef H X Y)
      = Causalean.Mathlib.FWL.residInnerVec H X Y :=
  Causalean.Mathlib.FWL.gramResid_mulVec_fwlCoef H X Y hQ

/-- **FWL least-squares optimality on `L²(μ)`.** The FWL coefficient (paired
with the nuisance projection of its raw residual) minimizes the original
least-squares objective over coefficients and nuisance terms in `H`.
Specialization of `Causalean.Mathlib.FWL.fwlCoef_original_minimizes`.
@isnad1 id=le.2h8v.s12.b4d39a9de9f1 from=translated src=- shape=dabc1220 vocab=2424bf65
-/
theorem fwlCoef_original_minimizes
    (hQ : IsUnit (Causalean.Mathlib.FWL.gramResid H X).det)
    (β : Fin K → ℝ) {h : Lp ℝ 2 μ} (hh : h ∈ H) :
    Causalean.Mathlib.FWL.originalObjective X Y (Causalean.Mathlib.FWL.fwlCoef H X Y)
        (H.orthogonalProjectionFn
          (Y - Causalean.Mathlib.FWL.fittedValue X (Causalean.Mathlib.FWL.fwlCoef H X Y)))
      ≤ Causalean.Mathlib.FWL.originalObjective X Y β h :=
  Causalean.Mathlib.FWL.fwlCoef_original_minimizes H X Y hQ β hh

/-- **FWL uniqueness on `L²(μ)`.** Fix square-integrable regressors `X` and outcome `Y`, and a
finite-dimensional nuisance subspace `H` of `L²(μ)`, and assume [the residualized regressor Gram
matrix is invertible](hyp:hQ). If [the nuisance term `h` lies in `H`](hyp:hh) and [the pair
`(β, h)` minimizes the original least-squares objective jointly over all coefficient vectors and
nuisance terms in `H`](hyp:hmin), then [`β` equals the Frisch–Waugh–Lovell coefficient computed
by residualizing against `H`](goal). Specialization of
`Causalean.Mathlib.FWL.fwlCoef_eq_of_original_minimizer`.
@isnad1 id=eq.3h8v.s12.84a9796eb111 from=translated src=- shape=d1af1714 vocab=f1ee4694
-/
theorem fwlCoef_eq_of_original_minimizer
    (hQ : IsUnit (Causalean.Mathlib.FWL.gramResid H X).det)
    (β : Fin K → ℝ) {h : Lp ℝ 2 μ} (hh : h ∈ H)
    (hmin : ∀ (γ : Fin K → ℝ) {g : Lp ℝ 2 μ}, g ∈ H →
      Causalean.Mathlib.FWL.originalObjective X Y β h
        ≤ Causalean.Mathlib.FWL.originalObjective X Y γ g) :
    β = Causalean.Mathlib.FWL.fwlCoef H X Y :=
  Causalean.Mathlib.FWL.fwlCoef_eq_of_original_minimizer H X Y hQ β hh hmin

end FWL

end FWLInstanceL2
end Stat
end Causalean

/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
module

public import Tengoku.LeanPool.LeanPool.PoincareThreeBody.Core
public import Tengoku

/-!
# Coordinate minors and functional dependence

Two phase covectors are dependent exactly when all of their two-by-two coordinate minors vanish.
This file proves the direction needed for nonintegrability.  It converts the scalar analytic
identities naturally produced by coefficient induction into failure of the challenge's
`LinearIndependent` predicate.
-/

@[expose] public section

namespace LeanPool.PoincareThreeBody

/-- A two-by-two coordinate minor of a pair of phase covectors. -/
def phaseCovectorMinor
    (first second : PhaseSpace →L[ℝ] ℝ) (i j : Fin 4) : ℝ :=
  first (coordinateVector i) * second (coordinateVector j) -
    first (coordinateVector j) * second (coordinateVector i)

/-- A differentiable scalar function of an observable has zero coordinate minors with that
observable.
@isnad1 id=eq.2h5v.s8.9d595e926da8 from=translated src=- shape=e4c51ad1 vocab=b27e153c
-/
theorem phaseCovectorMinor_comp_self_eq_zero
    {observable : PhaseSpace → ℝ} {scalarFunction : ℝ → ℝ} {state : PhaseSpace}
    (hobservable : DifferentiableAt ℝ observable state)
    (hscalar : DifferentiableAt ℝ scalarFunction (observable state))
    (i j : Fin 4) :
    phaseCovectorMinor (fderiv ℝ observable state)
      (fderiv ℝ (fun candidate ↦ scalarFunction (observable candidate)) state) i j = 0 := by
  have hchain := fderiv_comp state hscalar hobservable
  let coefficient := fderiv ℝ scalarFunction (observable state) 1
  have hscalarDerivative (value : ℝ) :
      fderiv ℝ scalarFunction (observable state) value =
        value * coefficient := by
    calc
      fderiv ℝ scalarFunction (observable state) value =
          fderiv ℝ scalarFunction (observable state) (value • (1 : ℝ)) := by simp
      _ = value • fderiv ℝ scalarFunction (observable state) 1 := by rw [map_smul]
      _ = value * coefficient := by rfl
  unfold phaseCovectorMinor
  rw [show fderiv ℝ (fun candidate ↦ scalarFunction (observable candidate)) state =
      (fderiv ℝ scalarFunction (observable state)).comp
        (fderiv ℝ observable state) by
    simpa only [Function.comp_def] using hchain]
  simp only [ContinuousLinearMap.comp_apply]
  simp_rw [hscalarDerivative]
  ring

/-- A phase covector vanishing on all four coordinate vectors is zero.
@isnad1 id=eq.1h1v.s9.c33a017f555e from=translated src=- shape=f8dd2850 vocab=485cb67d
-/
theorem phaseCovector_eq_zero_of_coordinates_eq_zero
    {covector : PhaseSpace →L[ℝ] ℝ}
    (hzero : ∀ i : Fin 4, covector (coordinateVector i) = 0) :
    covector = 0 := by
  apply ContinuousLinearMap.ext
  intro direction
  have hdecompose : direction =
      direction 0 • coordinateVector 0 + direction 1 • coordinateVector 1 +
        direction 2 • coordinateVector 2 + direction 3 • coordinateVector 3 := by
    funext coordinate
    fin_cases coordinate <;> simp [coordinateVector]
  rw [hdecompose, map_add, map_add, map_add, map_smul, map_smul, map_smul,
    map_smul, hzero 0, hzero 1, hzero 2, hzero 3]
  simp

/-- A pair consisting of a vector and one of its scalar multiples is not linearly independent.
@isnad1 id=not.1h4v.s6.4def846b47a1 from=translated src=- shape=3de8ff36 vocab=9db72ec1
-/
theorem not_linearIndependent_pair_of_eq_smul
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {first second : V} {scalar : ℝ} (hsecond : second = scalar • first) :
    ¬LinearIndependent ℝ ![first, second] := by
  intro hindependent
  let coefficients : Fin 2 → ℝ := ![-scalar, 1]
  have hcombination :
      ∑ i : Fin 2, coefficients i • ![first, second] i = 0 := by
    simp only [Fin.sum_univ_two, coefficients, Matrix.cons_val_zero,
      Matrix.cons_val_one, hsecond]
    module
  have hone := (Fintype.linearIndependent_iff.mp hindependent)
    coefficients hcombination 1
  norm_num [coefficients] at hone

/-- If every coordinate minor vanishes, two concrete phase covectors are dependent.
@isnad1 id=not.1h2v.s9.e47e2753f18b from=translated src=- shape=acd45eff vocab=6adac1b9
-/
theorem not_linearIndependent_phaseCovectors_of_minors_eq_zero
    {first second : PhaseSpace →L[ℝ] ℝ}
    (hminor : ∀ i j : Fin 4, phaseCovectorMinor first second i j = 0) :
    ¬LinearIndependent ℝ ![first, second] := by
  by_cases hfirst : first = 0
  · intro hindependent
    exact (hindependent.ne_zero 0) hfirst
  · have hexists : ∃ coordinate : Fin 4,
        first (coordinateVector coordinate) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hfirst (phaseCovector_eq_zero_of_coordinates_eq_zero hall)
    obtain ⟨pivot, hpivot⟩ := hexists
    let scalar := second (coordinateVector pivot) /
      first (coordinateVector pivot)
    have hcoordinate (coordinate : Fin 4) :
        second (coordinateVector coordinate) =
          scalar * first (coordinateVector coordinate) := by
      have h := hminor pivot coordinate
      unfold phaseCovectorMinor at h
      dsimp only [scalar]
      field_simp [hpivot]
      nlinarith
    have hdependent : second = scalar • first := by
      apply ContinuousLinearMap.ext
      intro direction
      have hdecompose : direction =
          direction 0 • coordinateVector 0 + direction 1 • coordinateVector 1 +
            direction 2 • coordinateVector 2 + direction 3 • coordinateVector 3 := by
        funext coordinate
        fin_cases coordinate <;> simp [coordinateVector]
      rw [hdecompose, map_add, map_add, map_add, map_add, map_add, map_add,
        map_smul, map_smul, map_smul, map_smul, map_smul, map_smul, map_smul,
        map_smul, hcoordinate 0, hcoordinate 1, hcoordinate 2, hcoordinate 3]
      simp only [smul_apply, smul_eq_mul]
    exact not_linearIndependent_pair_of_eq_smul hdependent

/-- One nonzero coordinate minor certifies linear independence of a pair of covectors.
@isnad1 id=linearin.1h4v.s9.1dc4dfc93fb1 from=translated src=- shape=8597b4c6 vocab=6adac1b9
-/
theorem linearIndependent_phaseCovectors_of_minor_ne_zero
    {first second : PhaseSpace →L[ℝ] ℝ} {i j : Fin 4}
    (hminor : phaseCovectorMinor first second i j ≠ 0) :
    LinearIndependent ℝ ![first, second] := by
  rw [LinearIndependent.pair_iffₛ]
  intro s t s' t' hequality
  have hi := congrArg (fun covector : PhaseSpace →L[ℝ] ℝ ↦
    covector (coordinateVector i)) hequality
  have hj := congrArg (fun covector : PhaseSpace →L[ℝ] ℝ ↦
    covector (coordinateVector j)) hequality
  simp only [add_apply, smul_apply, smul_eq_mul] at hi hj
  have hs : (s - s') * phaseCovectorMinor first second i j = 0 := by
    unfold phaseCovectorMinor
    linear_combination (second (coordinateVector j)) * hi -
      (second (coordinateVector i)) * hj
  have ht : (t - t') * phaseCovectorMinor first second i j = 0 := by
    unfold phaseCovectorMinor
    linear_combination -(first (coordinateVector j)) * hi +
      (first (coordinateVector i)) * hj
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_right hminor),
    sub_eq_zero.mp ((mul_eq_zero.mp ht).resolve_right hminor)⟩

/-- For a pair of concrete phase covectors, dependence is equivalent to vanishing of all
coordinate minors.
@isnad1 id=eq.1h4v.s9.b39227e85e95 from=translated src=- shape=6839be76 vocab=6adac1b9
-/
theorem phaseCovectorMinor_eq_zero_of_not_linearIndependent
    {first second : PhaseSpace →L[ℝ] ℝ}
    (hdependent : ¬LinearIndependent ℝ ![first, second]) :
    ∀ i j : Fin 4, phaseCovectorMinor first second i j = 0 := by
  intro i j
  by_contra hminor
  exact hdependent (linearIndependent_phaseCovectors_of_minor_ne_zero hminor)

/-- Coordinate-minor formulation for differentials of two observables.
@isnad1 id=not.1h3v.s10.acbe7f71cc3f from=translated src=- shape=56edf5b1 vocab=072fb990
-/
theorem not_linearIndependent_fderiv_of_minors_eq_zero
    {first second : PhaseSpace → ℝ} {state : PhaseSpace}
    (hminor : ∀ i j : Fin 4,
      phaseCovectorMinor (fderiv ℝ first state) (fderiv ℝ second state) i j = 0) :
    ¬LinearIndependent ℝ ![fderiv ℝ first state, fderiv ℝ second state] :=
  not_linearIndependent_phaseCovectors_of_minors_eq_zero hminor

end LeanPool.PoincareThreeBody

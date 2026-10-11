/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.Decomposition
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.DerivativeAdjoint

/-!
# Decomposition Potentials

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

/-! The eight explicit potentials in the local pressure decomposition. -/

/-- Newtonian potential of the tensor paired with the second derivatives of the cutoff. -/
def pressureP2 (η : Vec3 → ℝ) (u : ParabolicPoint → Vec3) (c : ℝ → Vec3)
    (s : ℝ) : Vec3 → ℝ := fun x =>
  ∑ i, ∑ j, pressureNewtonianPotential
    (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x

/-- First Newtonian derivative potential for the first tensor-cutoff cross term. -/
def pressureP3 (η : Vec3 → ℝ) (u : ParabolicPoint → Vec3) (c : ℝ → Vec3)
    (s : ℝ) : Vec3 → ℝ := fun x =>
  ∑ i, ∑ j, pressureNewtonianDerivativePotential j
    (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x

/-- First Newtonian derivative potential for the second tensor-cutoff cross term. -/
def pressureP4 (η : Vec3 → ℝ) (u : ParabolicPoint → Vec3) (c : ℝ → Vec3)
    (s : ℝ) : Vec3 → ℝ := fun x =>
  ∑ i, ∑ j, pressureNewtonianDerivativePotential i
    (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x

/-- Pressure correction involving the Laplacian of the cutoff. -/
def pressureP5 (η : Vec3 → ℝ) (p : ParabolicPoint → ℝ) (s : ℝ) : Vec3 → ℝ := fun x =>
  -pressureNewtonianPotential (fun y => p (y, s) * spatialLaplacian η y) x

/-- Pressure correction involving the gradient of the cutoff. -/
def pressureP6 (η : Vec3 → ℝ) (p : ParabolicPoint → ℝ) (s : ℝ) : Vec3 → ℝ := fun x =>
  -2 * ∑ j, pressureNewtonianDerivativePotential j
    (fun y => spatialDeriv η j y * p (y, s)) x

/-- First Newtonian derivative potential of the cutoff force. -/
def pressureP7 (η : Vec3 → ℝ) (f : ParabolicPoint → Vec3) (s : ℝ) : Vec3 → ℝ := fun x =>
  -∑ j, pressureNewtonianDerivativePotential j
    (fun y => η y * f (y, s) j) x

/-- Newtonian potential of the force paired with the cutoff gradient. -/
def pressureP8 (η : Vec3 → ℝ) (f : ParabolicPoint → Vec3) (s : ℝ) : Vec3 → ℝ := fun x =>
  -∑ j, pressureNewtonianPotential
    (fun y => spatialDeriv η j y * f (y, s) j) x

/-- Localized pressure after subtracting the seven explicit cutoff and forcing corrections. -/
def pressureP1 (η : Vec3 → ℝ) (u : ParabolicPoint → Vec3) (c : ℝ → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3) (s : ℝ) : Vec3 → ℝ := fun x =>
  η x * p (x, s) - (pressureP2 η u c s x + pressureP3 η u c s x +
    pressureP4 η u c s x + pressureP5 η p s x + pressureP6 η p s x +
    pressureP7 η f s x + pressureP8 η f s x)

theorem pressure_decomposition_pointwise (η : Vec3 → ℝ)
    (u : ParabolicPoint → Vec3) (c : ℝ → Vec3) (p : ParabolicPoint → ℝ)
    (f : ParabolicPoint → Vec3) (s : ℝ) (x : Vec3) :
    η x * p (x, s) = pressureP1 η u c p f s x + pressureP2 η u c s x +
      pressureP3 η u c s x + pressureP4 η u c s x + pressureP5 η p s x +
      pressureP6 η p s x + pressureP7 η f s x + pressureP8 η f s x := by
  simp only [pressureP1]
  ring

private theorem pressure_locallyIntegrable_sum₂
    {F : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hF : ∀ i j, LocallyIntegrable (F i j) volume) :
    LocallyIntegrable (fun x => ∑ i, ∑ j, F i j x) volume := by
  classical
  have hsum (i : Fin 3) : LocallyIntegrable (fun x => ∑ j, F i j x) volume := by
    simpa only [Finset.sum_apply] using
      (locallyIntegrable_finsetSum (Finset.univ : Finset (Fin 3))
        (fun j _hj => hF i j))
  simpa only [Finset.sum_apply] using
    (locallyIntegrable_finsetSum (Finset.univ : Finset (Fin 3))
      (fun i _hi => hsum i))

theorem pressureP2_locallyIntegrable {η : Vec3 → ℝ}
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {s : ℝ}
    (hInt : ∀ i j, Integrable
      (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) volume)
    (hSupp : ∀ i j, HasCompactSupport
      (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j)) :
    LocallyIntegrable (pressureP2 η u c s) volume := by
  apply pressure_locallyIntegrable_sum₂
  intro i j
  exact pressureNewtonianPotential_locallyIntegrable (hInt i j) (hSupp i j)

theorem pressureP5_locallyIntegrable {η : Vec3 → ℝ} {p : ParabolicPoint → ℝ} {s : ℝ}
    (hInt : Integrable (fun y => p (y, s) * spatialLaplacian η y) volume)
    (hSupp : HasCompactSupport (fun y => p (y, s) * spatialLaplacian η y)) :
    LocallyIntegrable (pressureP5 η p s) volume := by
  change LocallyIntegrable
    (fun x => -pressureNewtonianPotential
      (fun y => p (y, s) * spatialLaplacian η y) x) volume
  exact (pressureNewtonianPotential_locallyIntegrable hInt hSupp).neg

theorem pressureP8_locallyIntegrable {η : Vec3 → ℝ}
    {f : ParabolicPoint → Vec3} {s : ℝ}
    (hInt : ∀ j, Integrable (fun y => spatialDeriv η j y * f (y, s) j) volume)
    (hSupp : ∀ j, HasCompactSupport (fun y => spatialDeriv η j y * f (y, s) j)) :
    LocallyIntegrable (pressureP8 η f s) volume := by
  have hsum : LocallyIntegrable
      (fun x => ∑ j, pressureNewtonianPotential
        (fun y => spatialDeriv η j y * f (y, s) j) x) volume := by
    simpa only [Finset.sum_apply] using
      (locallyIntegrable_finsetSum (Finset.univ : Finset (Fin 3))
        (fun j _hj => pressureNewtonianPotential_locallyIntegrable (hInt j) (hSupp j)))
  change LocallyIntegrable
    (fun x => -(∑ j, pressureNewtonianPotential
      (fun y => spatialDeriv η j y * f (y, s) j) x)) volume
  exact hsum.neg

end CKN

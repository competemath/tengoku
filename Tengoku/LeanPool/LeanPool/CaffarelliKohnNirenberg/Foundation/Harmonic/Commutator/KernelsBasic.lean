/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Deriv
public import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Kernels Basic

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators Topology
open Filter MeasureTheory

namespace CKN.Foundation.Harmonic.Commutator

noncomputable section

/-- Squared Euclidean radius used in Newtonian derivative formulas. -/
def q (x : CKN.Vec 3) : ℝ := CKN.vecNormSq x

/-- The inverse Euclidean radius, extended by zero at the origin. -/
def radialInverse (x : CKN.Vec 3) : ℝ :=
  if x = 0 then 0 else q x ^ (-(1 : ℝ) / 2)

/-- First derivative formula for the inverse Euclidean radius. -/
def firstFormula (i : Fin 3) (x : CKN.Vec 3) : ℝ :=
  -x i * q x ^ (-(3 : ℝ) / 2)

/-- Second derivative formula for the inverse Euclidean radius. -/
def secondFormula (i j : Fin 3) (x : CKN.Vec 3) : ℝ :=
  3 * x i * x j * q x ^ (-(5 : ℝ) / 2) -
    (if i = j then 1 else 0) * q x ^ (-(3 : ℝ) / 2)

/-- Continuous linear differential of a power of the squared radius. -/
def qDerivative (p : ℝ) (x : CKN.Vec 3) : CKN.Vec 3 →L[ℝ] ℝ :=
  (p * q x ^ (p - 1)) •
    ∑ k : Fin 3, (2 * x k) •
      (ContinuousLinearMap.proj k : CKN.Vec 3 →L[ℝ] ℝ)

/-- Continuous linear differential of the second inverse-radius derivative formula. -/
def secondDerivative (i j : Fin 3) (x : CKN.Vec 3) : CKN.Vec 3 →L[ℝ] ℝ :=
  3 • ((x i * x j) • qDerivative (-(5 : ℝ) / 2) x +
    (q x ^ (-(5 : ℝ) / 2)) •
      (x i • (ContinuousLinearMap.proj j : CKN.Vec 3 →L[ℝ] ℝ) +
        x j • (ContinuousLinearMap.proj i : CKN.Vec 3 →L[ℝ] ℝ))) -
    (if i = j then 1 else 0) • qDerivative (-(3 : ℝ) / 2) x

/-- The third derivative of the inverse Euclidean radius, in the convention
used by the Newtonian kernel. -/
def inverseThirdFormula (m j l : Fin 3) (x : CKN.Vec 3) : ℝ :=
  -15 * x m * x j * x l * (CKN.vecEuclideanNorm x ^ 7)⁻¹ +
    3 * ((if m = l then 1 else 0) * x j +
      (if m = j then 1 else 0) * x l +
      (if l = j then 1 else 0) * x m) *
      (CKN.vecEuclideanNorm x ^ 5)⁻¹

/-- Third inverse-radius derivative expressed using powers of the squared radius. -/
def inverseThirdFormulaQ (m j l : Fin 3) (x : CKN.Vec 3) : ℝ :=
  -15 * x m * x j * x l * q x ^ (-(7 : ℝ) / 2) +
    3 * ((if m = l then 1 else 0) * x j +
      (if m = j then 1 else 0) * x l +
      (if l = j then 1 else 0) * x m) * q x ^ (-(5 : ℝ) / 2)

/-- Continuous linear differential of the third inverse-radius derivative formula. -/
def inverseThirdFormulaQDerivative (m j l : Fin 3) (x : CKN.Vec 3) :
    CKN.Vec 3 →L[ℝ] ℝ :=
  (-15 : ℝ) • (
      q x ^ (-(7 : ℝ) / 2) •
          ((x j * x l) • (ContinuousLinearMap.proj m : CKN.Vec 3 →L[ℝ] ℝ) +
            (x m * x l) • (ContinuousLinearMap.proj j : CKN.Vec 3 →L[ℝ] ℝ) +
            (x m * x j) • (ContinuousLinearMap.proj l : CKN.Vec 3 →L[ℝ] ℝ)) +
        (x m * x j * x l) • qDerivative (-(7 : ℝ) / 2) x) +
    (3 : ℝ) • (
      q x ^ (-(5 : ℝ) / 2) •
          ((if m = l then 1 else 0) •
              (ContinuousLinearMap.proj j : CKN.Vec 3 →L[ℝ] ℝ) +
            (if m = j then 1 else 0) •
              (ContinuousLinearMap.proj l : CKN.Vec 3 →L[ℝ] ℝ) +
            (if l = j then 1 else 0) •
              (ContinuousLinearMap.proj m : CKN.Vec 3 →L[ℝ] ℝ)) +
        ((if m = l then 1 else 0) * x j +
          (if m = j then 1 else 0) * x l +
          (if l = j then 1 else 0) * x m) •
          qDerivative (-(5 : ℝ) / 2) x)

/-- The Newtonian potential and its third-derivative kernel. -/
def newtonianPotential (x : CKN.Vec 3) : ℝ :=
  -(4 * Real.pi)⁻¹ * radialInverse x

/-- Normalized third Newtonian derivative kernel used in the commutator estimates. -/
def newtonianKernel (m j l : Fin 3) (x : CKN.Vec 3) : ℝ :=
  -(4 * Real.pi)⁻¹ * inverseThirdFormula m j l x

end
end CKN.Foundation.Harmonic.Commutator

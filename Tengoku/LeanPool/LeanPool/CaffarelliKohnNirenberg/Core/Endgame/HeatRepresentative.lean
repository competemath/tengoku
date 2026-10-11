/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.SubordinatedCampanato
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Statements.ParabolicHolderVecNormLE

/-! # Quantitative vector representatives of heat potentials

The scalar heat estimate is applied to each coordinate. Both the local value
bound and the global Hölder constant remain explicit functions of the source
norms and the local averages of the potential.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory Set
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential

noncomputable section
namespace CKN.Core.Endgame

/-- The explicit scalar Hölder coefficient in the heat-potential estimate. -/
def heatHolderCoefficient (F : ParabolicPoint → ℝ)
    (G : Fin 3 → ParabolicPoint → ℝ) (γ θ₀ θ₁ P : ℝ) : ℝ :=
  let V : ℝ := (volume (parabolicCylinder 0 0 1)).toReal
  let BF : ℝ := V ^ (1 - 1 / P) * (morreyNorm P θ₀ F).toReal
  let BG : Fin 3 → ℝ := fun i =>
    V ^ (1 - 1 / P) * (morreyNorm P θ₁ (G i)).toReal
  let Cnear : ℝ :=
    2 * 1000 * (2 : ℝ) ^ (8 - 5 / θ₀) *
        (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BF +
      ∑ i, 2 * 300000 * (2 : ℝ) ^ (10 - 1 - 5 / θ₁) *
        (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ * BG i
  let C : ℝ :=
    (1800000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 16) +
      40000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 20)) * BF +
      ∑ i, (120000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 20) +
        120000000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 24)) * BG i
  parabolicCampanatoHolderConstant γ P *
    (Cnear + C * (1 - (2 : ℝ) ^ (γ - 1))⁻¹)

/-- The sum of the absolute scalar Hölder coefficients. -/
def vectorHeatHolderCoefficient (F : ParabolicPoint → Vec3)
    (G : Fin 3 → ParabolicPoint → Vec3) (γ θ₀ θ₁ P : ℝ) : ℝ :=
  ∑ i, |heatHolderCoefficient (fun x => F x i) (fun j x => G j x i) γ θ₀ θ₁ P|

/-- An explicit bound for the vector potential on a ball. -/
def vectorHeatValueBound (F : ParabolicPoint → Vec3)
    (G : Fin 3 → ParabolicPoint → Vec3) (γ θ₀ θ₁ P : ℝ)
    (z : ParabolicPoint) (R : ℝ) : ℝ :=
  ∑ i : Fin 3, |(2 : ℝ) ^ γ *
    heatHolderCoefficient (fun x => F x i) (fun j x => G j x i) γ θ₀ θ₁ P *
      R ^ γ +
        (⨍ x in Metric.ball z R,
          |heatPotential (fun y => F y i) (fun j y => G j y i) x| ^ P) ^ (1 / P)|

end CKN.Core.Endgame

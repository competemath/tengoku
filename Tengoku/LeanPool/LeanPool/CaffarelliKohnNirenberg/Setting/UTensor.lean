/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBridge
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.SliceIntegrability
public import Tengoku

/-!
# The tensor `U` built from a mean-free velocity field

This file records the tensor that `paper/ckn.tex` attaches to the local energy
class in the proof of Lemma `lem:U-bounds` (equation `eq:Uij`): at a point
`y` of the spatial ball `B_ρ = vec3Ball x₀ ρ` and at time `t`,

`U_ij(y,t) = -u_i(y,t) * (u_j(y,t) - ⨍_{B_ρ} u_j(·,t))`,

where the second factor is the mean-free part of the velocity field, averaged
in space over `B_ρ` with `MeasureTheory.average`.  Writing

`|U| = (∑_{i,j} U_ij²)^{1/2}`,

the main result `U_bounds_of_sobolevPoincare` is the two displays
`eq:U-bounds` of the paper:

* `(∫_{B_ρ} |U|^{3/2})^{2/3} ≤ C₅ · 𝔲(t) · 𝔤(t)`;
* `∫_{B_ρ} |U| ≤ (4π/3)^{1/3} C₅ ρ · 𝔲(t) · 𝔤(t)`,

with `𝔲(t) = (∫_{B_ρ} |u(·,t)|²)^{1/2}` and
`𝔤(t) = (∫_{B_ρ} |∇u(·,t)|²)^{1/2}`.  The only analytic input is the
same-ball `L⁶` Sobolev–Poincaré inequality (equation
`eq:sobolev-poincare-6`), taken as an explicit hypothesis on the mean-free
field; everything else is the pointwise rank-one identity `|U| = |u| |v|`,
Hölder's inequality, and the volume of `B_ρ`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

namespace CKN

noncomputable section

/-- The `j`-th component of `u(·,t)` with its spatial average over
`B_ρ = vec3Ball x₀ ρ` subtracted, the mean-free component appearing in
equation `eq:Uij` of `paper/ckn.tex`. -/
def meanFreeComponent (u : ParabolicPoint → Vec3) (x₀ : Vec3) (ρ : ℝ) (t : ℝ)
    (j : Fin 3) (y : Vec3) : ℝ :=
  u (y, t) j - MeasureTheory.average
    (MeasureTheory.volume.restrict (vec3Ball x₀ ρ)) (fun z => u (z, t) j)

/-- The mean-free velocity `v = u(·,t) - ⨍_{B_ρ} u(·,t)` of equation
`eq:Uij` in `paper/ckn.tex`. -/
def meanFreeVec (u : ParabolicPoint → Vec3) (x₀ : Vec3) (ρ : ℝ) (t : ℝ)
    (y : Vec3) : Vec3 :=
  fun j => meanFreeComponent u x₀ ρ t j y

/-- The rank-one tensor `U_ij = -u_i (u_j - ⨍_{B_ρ} u_j)` of equation
`eq:Uij` in `paper/ckn.tex`. -/
def utensor (u : ParabolicPoint → Vec3) (x₀ : Vec3) (ρ t : ℝ) (i j : Fin 3)
    (y : Vec3) : ℝ :=
  - u (y, t) i * meanFreeComponent u x₀ ρ t j y

/-- The pointwise norm `|U| = (∑_{i,j} U_ij²)^{1/2}` of the tensor of
equation `eq:Uij` in `paper/ckn.tex`. -/
def utensorNorm (u : ParabolicPoint → Vec3) (x₀ : Vec3) (ρ t : ℝ) (y : Vec3) : ℝ :=
  Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, (utensor u x₀ ρ t i j y) ^ (2 : ℕ))

/-- `U` is rank one: `|U|` is the product of the norms of `u(·,t)` and of its
mean-free part.  This is the pointwise identity used in `eq:U-bounds`. -/
theorem utensorNorm_eq (u : ParabolicPoint → Vec3) (x₀ : Vec3) (ρ t : ℝ)
    (y : Vec3) :
    utensorNorm u x₀ ρ t y =
      vec3EuclideanNorm (u (y, t)) * vec3EuclideanNorm (meanFreeVec u x₀ ρ t y) := by
  have hsq : ∑ i : Fin 3, ∑ j : Fin 3, (utensor u x₀ ρ t i j y) ^ (2 : ℕ) =
      (∑ i : Fin 3, (u (y, t) i) ^ (2 : ℕ)) *
        (∑ j : Fin 3, (meanFreeVec u x₀ ρ t y j) ^ (2 : ℕ)) := by
    simp only [utensor, meanFreeVec, meanFreeComponent, neg_mul, neg_sq, mul_pow]
    exact (Finset.sum_mul_sum _ _ _ _).symm
  rw [utensorNorm, vec3EuclideanNorm, vec3EuclideanNorm, hsq]
  rw [Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg (u (y, t) i)))]

end

end CKN

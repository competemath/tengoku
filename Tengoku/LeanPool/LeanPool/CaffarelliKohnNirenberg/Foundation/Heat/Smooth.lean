/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Basic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import Tengoku

/-!
# Differentiation formulas for the heat kernel

The coordinate formulas below use the standard coordinate directions of
`Fin 3 → ℝ`.  They do not use the function space's ambient norm; all spatial
quadratic expressions are finite sums.
-/

@[expose] public section

open scoped BigOperators ENNReal Topology

open Filter Set

noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

/-- Time derivative formula for the causal heat kernel. -/
def heatKernelTimeDerivative (x : Vec3) (t : ℝ) : ℝ :=
  if 0 < t then
    heatKernel x t *
      ((∑ i, x i ^ 2) / (4 * t ^ 2) - (3 : ℝ) / (2 * t))
  else 0

/-- First spatial derivative formula for the causal heat kernel. -/
def heatKernelSpaceDerivative (x : Vec3) (t : ℝ) (i : Fin 3) : ℝ :=
  if 0 < t then -(x i) / (2 * t) * heatKernel x t else 0

/-- Pure second spatial derivative formula for the causal heat kernel. -/
def heatKernelSpaceSecondDerivative (x : Vec3) (t : ℝ) (i : Fin 3) : ℝ :=
  if 0 < t then
    ((x i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * heatKernel x t
  else 0

/-- Mixed second spatial derivative formula for the causal heat kernel. -/
def heatKernelSpaceMixedSecondDerivative (x : Vec3) (t : ℝ)
    (i j : Fin 3) : ℝ :=
  if 0 < t then
    ((x i) * (x j) / (4 * t ^ 2) -
      (if i = j then (1 : ℝ) / (2 * t) else 0)) * heatKernel x t
  else 0

/-- Third spatial derivative formula for the causal heat kernel. -/
def heatKernelSpaceThirdDerivative (x : Vec3) (t : ℝ)
    (i j k : Fin 3) : ℝ :=
  if 0 < t then
    (-(x i) * (x j) * (x k) / (8 * t ^ 3) +
      ((if i = j then x k else 0) +
        (if i = k then x j else 0) +
        (if j = k then x i else 0)) / (4 * t ^ 2)) * heatKernel x t
  else 0

/-- Fourth spatial derivative formula for the causal heat kernel. -/
def heatKernelSpaceFourthDerivative (x : Vec3) (t : ℝ)
    (i j k l : Fin 3) : ℝ :=
  if 0 < t then
    ((x i) * (x j) * (x k) * (x l) / (16 * t ^ 4) -
      ((if i = j then (x k) * (x l) else 0) +
        (if i = k then (x j) * (x l) else 0) +
        (if i = l then (x j) * (x k) else 0) +
        (if j = k then (x i) * (x l) else 0) +
        (if j = l then (x i) * (x k) else 0) +
        (if k = l then (x i) * (x j) else 0)) / (8 * t ^ 3) +
      ((if i = j then (if k = l then (1 : ℝ) else 0) else 0) +
        (if i = k then (if j = l then (1 : ℝ) else 0) else 0) +
        (if i = l then (if j = k then (1 : ℝ) else 0) else 0)) /
        (4 * t ^ 2)) * heatKernel x t
  else 0

/-- Spatial Laplacian of the heat kernel, summed over coordinate directions. -/
def heatKernelLaplacian (x : Vec3) (t : ℝ) : ℝ :=
  ∑ i, heatKernelSpaceSecondDerivative x t i

lemma heatKernel_contDiffOn_pos :
    ContDiffOn ℝ ⊤ (fun p : Vec3 × ℝ => heatKernel p.1 p.2)
      (univ ×ˢ Ioi (0 : ℝ)) := by
  intro p hp
  rcases hp with ⟨_, hp⟩
  change 0 < p.2 at hp
  have hformula : ContDiffAt ℝ ⊤
      (fun q : Vec3 × ℝ =>
        (4 * Real.pi * q.2) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(∑ i, q.1 i ^ 2) / (4 * q.2))) p := by
    fun_prop (disch := positivity)
  apply hformula.contDiffWithinAt.congr_of_eventuallyEq
  · filter_upwards [eventually_mem_nhdsWithin] with q hq
    have hqpos : 0 < q.2 := hq.2
    rw [heatKernel, ite_eq_left hqpos]
  · rw [heatKernel, ite_eq_left hp]

lemma heatKernel_time_differentiableAt {x : Vec3} {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (fun s => heatKernel x s) t := by
  have hformula : ContDiffAt ℝ ⊤
      (fun s : ℝ =>
        (4 * Real.pi * s) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(∑ i, x i ^ 2) / (4 * s))) t := by
    fun_prop (disch := positivity)
  have heq :
      (fun s : ℝ => heatKernel x s) =ᶠ[nhds t]
        (fun s : ℝ =>
          (4 * Real.pi * s) ^ (-(3 : ℝ) / 2) *
            Real.exp (-(∑ i, x i ^ 2) / (4 * s))) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    rw [heatKernel_eq_formula_sum hs]
  exact (hformula.congr_of_eventuallyEq heq).differentiableAt (by simp)

lemma coord_fderiv_eq_deriv_update {f : Vec3 → ℝ} {x : Vec3}
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    (fderiv ℝ f x) (CKN.basisVec i) =
      deriv (fun s => f (Function.update x i s)) (x i) := by
  have hcomp := HasFDerivAt.comp (x i)
    (by simpa only [Function.update_eq_self] using hf.hasFDerivAt)
    (hasFDerivAt_update (𝕜 := ℝ) (i := i) x (x i))
  have hderiv := hcomp.hasDerivAt
  have hderiv' : HasDerivAt (fun s : ℝ => f (Function.update x i s))
      ((fderiv ℝ f x ∘SL ContinuousLinearMap.pi
        (Pi.single i (ContinuousLinearMap.id ℝ ℝ))) 1) (x i) := by
    simpa only [Function.comp_def] using hderiv
  rw [hderiv'.deriv]
  have hb : ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ)) 1 =
      CKN.basisVec i := by
    ext j
    by_cases hji : j = i <;> simp [CKN.basisVec, hji]
  rw [show (fderiv ℝ f x ∘SL
      ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ))) 1 =
      (fderiv ℝ f x) (ContinuousLinearMap.pi
      (Pi.single i (ContinuousLinearMap.id ℝ ℝ)) 1) by rfl, hb]

lemma heatKernel_heat_equation {x : Vec3} {t : ℝ} (ht : 0 < t) :
    heatKernelTimeDerivative x t = heatKernelLaplacian x t := by
  rw [heatKernelTimeDerivative, ite_eq_left ht, heatKernelLaplacian]
  simp only [heatKernelSpaceSecondDerivative, ite_eq_left ht]
  rw [heatKernel_eq_formula_sum ht]
  rw [← Finset.sum_mul]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]
  simp only [Finset.sum_const, Finset.card_fin]
  ring_nf

end CKN.Foundation.Heat

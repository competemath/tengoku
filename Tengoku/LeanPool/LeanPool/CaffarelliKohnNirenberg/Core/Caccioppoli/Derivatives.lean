/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Admissibility
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus
public import Tengoku

/-!
# Derivatives

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

private lemma coord_fderiv_eq_deriv_update {f : Vec3 → ℝ} {x : Vec3}
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    (fderiv ℝ f x) (basisVec i) =
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
      basisVec i := by
    ext j
    by_cases hji : j = i <;> simp [basisVec, hji]
  rw [show (fderiv ℝ f x ∘SL
      ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ))) 1 =
      (fderiv ℝ f x) (ContinuousLinearMap.pi
        (Pi.single i (ContinuousLinearMap.id ℝ ℝ)) 1) by rfl, hb]

end CKN

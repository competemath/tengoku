/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.ConditionalTwoPointCalibration
import Tengoku.LeanPool.LeanPool.Feige.BoundaryNull
import Tengoku.LeanPool.LeanPool.Feige.StrictLocalInsertion

/-!
# Removing strict positivity from the finite two-point bound
-/

@[expose] public section

open Filter Topology

namespace Feige

noncomputable section

/-- A positive perturbation parameter tending to zero. -/
def boundaryEpsilon (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

/-- A strictly positive approximation to a nonnegative lower displacement. -/
def strictGammaApprox {m : ℕ} (γ : Fin m → ℝ) (n : ℕ) (i : Fin m) : ℝ :=
  (1 - boundaryEpsilon n) * γ i + boundaryEpsilon n / 2

theorem boundaryEpsilon_pos (n : ℕ) : 0 < boundaryEpsilon n := by
  unfold boundaryEpsilon
  positivity

theorem boundaryEpsilon_le_one (n : ℕ) : boundaryEpsilon n ≤ 1 := by
  unfold boundaryEpsilon
  exact (div_le_one (by positivity)).2 (by norm_num)

theorem strictGammaApprox_pos {m : ℕ} {γ : Fin m → ℝ}
    (hγ : ∀ i, 0 ≤ γ i) (n : ℕ) (i : Fin m) :
    0 < strictGammaApprox γ n i := by
  unfold strictGammaApprox
  have he := boundaryEpsilon_pos n
  have he1 := boundaryEpsilon_le_one n
  nlinarith [hγ i]

theorem strictGammaApprox_le_one {m : ℕ} {γ : Fin m → ℝ}
    (hγ1 : ∀ i, γ i ≤ 1)
    (n : ℕ) (i : Fin m) :
    strictGammaApprox γ n i ≤ 1 := by
  unfold strictGammaApprox
  have he := boundaryEpsilon_pos n
  have he1 := boundaryEpsilon_le_one n
  nlinarith [hγ1 i]

theorem tendsto_boundaryEpsilon :
    Tendsto boundaryEpsilon atTop (𝓝 0) := by
  unfold boundaryEpsilon
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem tendsto_strictGammaApprox {m : ℕ} (γ : Fin m → ℝ) :
    Tendsto (strictGammaApprox γ) atTop (𝓝 γ) := by
  rw [tendsto_pi_nhds]
  intro i
  unfold strictGammaApprox
  convert (((tendsto_const_nhds.sub tendsto_boundaryEpsilon).mul
    tendsto_const_nhds).add (tendsto_boundaryEpsilon.div_const 2)) using 1
  ring_nf

theorem tendsto_twoPointHighProbability_strictGammaApprox
    {m : ℕ} (γ β : Fin m → ℝ) (hγ : ∀ i, 0 ≤ γ i)
    (hβ : ∀ i, 0 < β i)
    (i : Fin m) :
    Tendsto
      (fun n => twoPointHighProbability (strictGammaApprox γ n) β i)
      atTop (𝓝 (twoPointHighProbability γ β i)) := by
  unfold twoPointHighProbability highProbability
  have ht := (tendsto_strictGammaApprox γ).apply_nhds i
  apply ht.div (ht.add tendsto_const_nhds)
  linarith [hγ i, hβ i]

theorem tendsto_highSetMass_strictGammaApprox
    {m : ℕ} (γ β : Fin m → ℝ) (hγ : ∀ i, 0 ≤ γ i)
    (hβ : ∀ i, 0 < β i)
    (S : Finset (Fin m)) :
    Tendsto
      (fun n => highSetMass
        (twoPointHighProbability (strictGammaApprox γ n) β) S)
      atTop (𝓝 (highSetMass (twoPointHighProbability γ β) S)) := by
  unfold highSetMass
  apply (tendsto_finsetProd S fun i _ =>
    tendsto_twoPointHighProbability_strictGammaApprox γ β hγ hβ i).mul
  apply tendsto_finsetProd (Finset.univ \ S)
  intro i hi
  exact tendsto_const_nhds.sub
    (tendsto_twoPointHighProbability_strictGammaApprox γ β hγ hβ i)

end

end Feige

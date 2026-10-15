/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku.LeanPool.LeanPool.Odlyzko.ExplicitFormula.TartarPoitouTransform
import Tengoku.LeanPool.LeanPool.Odlyzko.TestFunction.Fourier
public import Tengoku

/-!
# Regularized Tartar

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Filter Real
open scoped Topology

namespace NumberField.Odlyzko

/-- A regularized scaled tartar used in the Odlyzko-bound argument. -/
noncomputable def regularizedScaledTartar
    (y δ x : ℝ) : ℝ :=
  scaledTartarTestFunction y x * Real.exp (-δ * x ^ 2)

/--
@isnad1 id=eq.0h2v.s4.446379bb962e from=translated src=- shape=9bf57cd7 vocab=1fca9fb7
-/
@[simp]
theorem regularizedScaledTartar_zero (y δ : ℝ) :
    regularizedScaledTartar y δ 0 = 1 := by
  simp [regularizedScaledTartar, scaledTartarTestFunction,
    tartarTestFunction_zero]

/--
@isnad1 id=eq.0h3v.s4.805ed41b2e03 from=translated src=- shape=eaf4a99a vocab=5b12337d
-/
theorem regularizedScaledTartar_even (y δ x : ℝ) :
    regularizedScaledTartar y δ (-x) =
      regularizedScaledTartar y δ x := by
  unfold regularizedScaledTartar
  rw [scaledTartarTestFunction_even]
  simp

/--
@isnad1 id=le.0h3v.s4.486d6a027057 from=translated src=- shape=ac9c39a3 vocab=ce687541
-/
theorem regularizedScaledTartar_nonneg (y δ x : ℝ) :
    0 ≤ regularizedScaledTartar y δ x :=
  mul_nonneg (scaledTartarTestFunction_nonneg y x)
    (Real.exp_pos _).le

/--
@isnad1 id=le.1h3v.s4.62a8e33d9311 from=translated src=- shape=afa8d857 vocab=df66584f
-/
theorem regularizedScaledTartar_le_scaledTartar
    {y δ x : ℝ} (hδ : 0 ≤ δ) :
    regularizedScaledTartar y δ x ≤
      scaledTartarTestFunction y x := by
  unfold regularizedScaledTartar
  have hexp : Real.exp (-δ * x ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    simpa only [neg_mul] using
      neg_nonpos.mpr (mul_nonneg hδ (sq_nonneg x))
  exact mul_le_of_le_one_right
    (scaledTartarTestFunction_nonneg y x) hexp

/--
@isnad1 id=le.1h3v.s4.0091ef55d63e from=translated src=- shape=bd802b6e vocab=ce687541
-/
theorem regularizedScaledTartar_le_one
    {y δ x : ℝ} (hδ : 0 ≤ δ) :
    regularizedScaledTartar y δ x ≤ 1 :=
  (regularizedScaledTartar_le_scaledTartar hδ).trans
    (tartarTestFunction_le_one _)

/--
@isnad1 id=tendsto.0h2v.s5.8535a5240df1 from=translated src=- shape=a869a2f7 vocab=2aa6cf47
-/
theorem tendsto_regularizedScaledTartar_nhds_zero
    (y x : ℝ) :
    Tendsto
      (fun δ : ℝ ↦ regularizedScaledTartar y δ x)
      (𝓝 0)
      (𝓝 (scaledTartarTestFunction y x)) := by
  unfold regularizedScaledTartar
  have harg :
      Tendsto (fun δ : ℝ ↦ -δ * x ^ 2)
        (𝓝 0) (𝓝 0) := by
    have hneg :
        Tendsto (fun δ : ℝ ↦ -δ) (𝓝 0) (𝓝 0) :=
      by
        have hid :
            Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0) :=
          tendsto_id
        simpa only [id_eq, neg_zero] using hid.neg
    simpa using hneg.mul_const (x ^ 2)
  simpa using
    tendsto_const_nhds.mul
      (Real.continuous_exp.continuousAt.tendsto.comp harg)

end NumberField.Odlyzko

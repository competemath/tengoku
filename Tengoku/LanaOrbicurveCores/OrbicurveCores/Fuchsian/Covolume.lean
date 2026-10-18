/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite covolume and index bounds for subgroups of `SL(2, ℝ)`

We say that `Γ ≤ SL(2, ℝ)` has a **finite-area covering set** if some measurable `F ⊆ ℍ` of finite
hyperbolic area meets every `Γ`-orbit (`HasFiniteCovolume`). For discrete `Γ` this is the lattice
property.

* `volume_le_two_mul_of_packing`: if `U` is a packing set (`γU ∩ U = ∅` for `γ ∈ Γ ∖ {±1}`) and `F`
  meets every orbit, then `vol U ≤ 2 vol F`.
* `relIndex_ne_zero_of_discrete`: if `Γ ≤ Δ`, `Δ` is discrete and `Γ` has finite covolume, then
  `[Δ : Γ] < ∞`.
-/

open MeasureTheory Matrix UpperHalfPlane Set Topology Filter
open scoped MatrixGroups ENNReal Pointwise

namespace OrbicurveCores.Fuchsian

/-- `Γ` has a finite-area covering set: a measurable `F ⊆ ℍ` of finite hyperbolic area meeting
every orbit. -/
def HasFiniteCovolume (Γ : Subgroup SL(2, ℝ)) : Prop :=
  ∃ F : Set ℍ, MeasurableSet F ∧ volume F < ∞ ∧ ∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ F

lemma measurable_smul_SL (g : SL(2, ℝ)) : Measurable fun z : ℍ ↦ g • z :=
  (continuous_const_smul g).measurable

/-- Nonempty balls have positive hyperbolic area. -/
lemma volume_ball_pos (z : ℍ) {r : ℝ} (hr : 0 < r) : 0 < volume (Metric.ball z r) := by
  rw [volume_eq_lintegral]
  have hmeas : Measurable fun w : ℂ ↦ ((((1 / ‖w.im‖₊) ^ 2 : NNReal)) : ℝ≥0∞) := by fun_prop
  rw [setLIntegral_pos_iff hmeas]
  have hopen : IsOpen ((↑) '' Metric.ball z r : Set ℂ) :=
    isOpenEmbedding_coe.isOpenMap _ Metric.isOpen_ball
  have hsub : ((↑) '' Metric.ball z r : Set ℂ) ⊆ Function.support
      fun w : ℂ ↦ ((((1 / ‖w.im‖₊) ^ 2 : NNReal)) : ℝ≥0∞) := by
    rintro _ ⟨w, -, rfl⟩
    simp [w.im_ne_zero]
  rw [Set.inter_eq_self_of_subset_right hsub]
  exact hopen.measure_pos _ ⟨z, z, Metric.mem_ball_self hr, rfl⟩

end OrbicurveCores.Fuchsian

import Tengoku.Degiorgi.DeGiorgi.Common

/-!
# Chapter 02: Oscillation BMO Prelude

This module packages the BMO definitions, basic John-Nirenberg geometry, and
preliminary iteration and covering lemmas.
-/

noncomputable section

open MeasureTheory Metric Filter Set
open scoped ENNReal NNReal Topology

namespace DeGiorgi

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ## Constants -/

/-- The John-Nirenberg constant. -/
noncomputable def C_JN (d : ℕ) : ℝ :=
  16 * 36 ^ d

/-- The constant in the simple iteration lemma with exponent ξ = 2.
  Using δ = 1/4 gives C_iter = 4 · 144 = 576; we round up to 1024 for margin. -/
noncomputable def C_iter : ℝ := 1024

theorem C_iter_pos : 0 < C_iter := by
  unfold C_iter; positivity

/-! ## BMO -/

/-- The BMO seminorm on a set `U`. -/
noncomputable def bmoNorm (u : E → ℝ) (U : Set E) : ℝ :=
  sSup {t : ℝ | ∃ (x₀ : E) (r : ℝ), 0 < r ∧
    Metric.closedBall x₀ r ⊆ U ∧
    t = (⨍ x in Metric.ball x₀ r, ‖u x - ⨍ y in Metric.ball x₀ r, u y ∂volume‖ ∂volume)}

/-! ## John-Nirenberg Geometry -/

/-- Balls inside a fixed ambient ball, used in the Calderón-Zygmund selection behind the
John-Nirenberg argument. -/
structure JNBall (x₀ : E) (R : ℝ) where
  center : E
  radius : ℝ
  radius_pos : 0 < radius
  radius_le : radius ≤ R
  center_mem : center ∈ Metric.ball x₀ R

namespace JNBall

def carrier {x₀ : E} {R : ℝ} (b : JNBall x₀ R) : Set E :=
  Metric.ball b.center b.radius

def fivefold {x₀ : E} {R : ℝ} (b : JNBall x₀ R) : Set E :=
  Metric.ball b.center (5 * b.radius)

end JNBall

/-! ## Simple Iteration Lemma (AKM, Lemma C.6) -/

/-! ## Vitali Covering Lemma -/

end DeGiorgi

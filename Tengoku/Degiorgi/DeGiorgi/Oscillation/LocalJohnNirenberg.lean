import Tengoku.Degiorgi.DeGiorgi.Oscillation.BMO

/-!
# Chapter 02: Local John-Nirenberg Theory

This module contains the selected-ball decay machinery and the local
John-Nirenberg inequality.
-/

noncomputable section

open MeasureTheory Metric Filter Set
open scoped ENNReal NNReal Topology

namespace DeGiorgi

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ## Auxiliary Lemmas for Local John-Nirenberg -/

private def JNBadCenterSet
    (w : E → ℝ) (x₀ : E) (R lam : ℝ) : Set E :=
  {x ∈ Metric.ball x₀ R | ∃ r, 0 < r ∧ r ≤ R ∧
    lam < ⨍ y in Metric.ball x r, w y ∂volume}

/-- A raw bad witness ball for the John-Nirenberg Calderón-Zygmund decomposition. -/
private structure JNBadWitness
    (w : E → ℝ) (x₀ : E) (R lam : ℝ) where
  center : E
  witnessRadius : ℝ
  center_mem : center ∈ Metric.ball x₀ R
  radius_pos : 0 < witnessRadius
  radius_le : witnessRadius ≤ R
  bad : lam < ⨍ y in Metric.ball center witnessRadius, w y ∂volume

private noncomputable def weakenBadWitness
    {w : E → ℝ} {x₀ : E} {R lam₁ lam₂ : ℝ}
    (hlam : lam₁ ≤ lam₂) (p : JNBadWitness w x₀ R lam₂) :
    JNBadWitness w x₀ R lam₁ where
  center := p.center
  witnessRadius := p.witnessRadius
  center_mem := p.center_mem
  radius_pos := p.radius_pos
  radius_le := p.radius_le
  bad := lt_of_le_of_lt hlam p.bad

private noncomputable def witnessStepRadius
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (p : JNBadWitness w x₀ R lam) (n : ℕ) : ℝ :=
  min (((n + 1 : ℕ) : ℝ) * p.witnessRadius) R

private lemma exists_nonbad_stepIndex
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (_hR : 0 < R)
    (p : JNBadWitness w x₀ R lam)
    (havg_base : ∀ x ∈ Metric.ball x₀ R,
      ⨍ y in Metric.ball x R, w y ∂volume ≤ lam) :
    ∃ n : ℕ,
      ⨍ y in Metric.ball p.center (witnessStepRadius p n), w y ∂volume ≤ lam := by
  let N : ℕ := Nat.ceil (R / p.witnessRadius)
  have hRN : R ≤ ((N : ℕ) : ℝ) * p.witnessRadius := by
    exact (div_le_iff₀ p.radius_pos).mp (Nat.le_ceil (R / p.witnessRadius))
  have hstepN : witnessStepRadius p N = R := by
    rw [witnessStepRadius, min_eq_right]
    have hNsucc : (((N + 1 : ℕ) : ℝ) * p.witnessRadius) ≥ ((N : ℕ) : ℝ) * p.witnessRadius := by
      have hsucc : ((N : ℕ) : ℝ) ≤ (((N + 1 : ℕ) : ℝ)) := by
        exact_mod_cast (Nat.le_succ N)
      exact mul_le_mul_of_nonneg_right hsucc p.radius_pos.le
    exact le_trans hRN hNsucc
  refine ⟨N, ?_⟩
  rw [hstepN]
  exact havg_base p.center p.center_mem

private noncomputable def stoppingIndexBad
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (hR : 0 < R)
    (havg_base : ∀ x ∈ Metric.ball x₀ R,
      ⨍ y in Metric.ball x R, w y ∂volume ≤ lam)
    (p : JNBadWitness w x₀ R lam) : ℕ :=
  Nat.find (exists_nonbad_stepIndex hR p havg_base)

private noncomputable def stoppingRadiusBad
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (hR : 0 < R)
    (havg_base : ∀ x ∈ Metric.ball x₀ R,
      ⨍ y in Metric.ball x R, w y ∂volume ≤ lam)
    (p : JNBadWitness w x₀ R lam) : ℝ :=
  witnessStepRadius p (stoppingIndexBad hR havg_base p - 1)

private noncomputable def stoppingParentRadiusBad
    {w : E → ℝ} {x₀ : E} {R lam : ℝ}
    (hR : 0 < R)
    (havg_base : ∀ x ∈ Metric.ball x₀ R,
      ⨍ y in Metric.ball x R, w y ∂volume ≤ lam)
    (p : JNBadWitness w x₀ R lam) : ℝ :=
  witnessStepRadius p (stoppingIndexBad hR havg_base p)

end DeGiorgi

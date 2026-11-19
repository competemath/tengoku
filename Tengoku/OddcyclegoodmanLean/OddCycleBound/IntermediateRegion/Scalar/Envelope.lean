import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.Scalar.EigenvalueAlgebra
import Tengoku.Seed.Topology.Order.Compact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Set

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

theorem continuous_envelopeObjective (xi rho : Real) :
    Continuous (envelopeObjective xi rho) := by
  unfold envelopeObjective
  fun_prop

theorem envelopeObjective_image_nonempty (xi rho : Real) :
    (envelopeObjective xi rho '' Icc (0 : Real) 1).Nonempty := by
  exact ⟨envelopeObjective xi rho 0, ⟨0, by constructor <;> norm_num, rfl⟩⟩

theorem envelopeObjective_nonneg {xi rho v : Real}
    (hrho : 0 ≤ rho) :
    0 ≤ envelopeObjective xi rho v := by
  unfold envelopeObjective
  exact add_nonneg (mul_nonneg hrho (sq_nonneg v)) (le_max_right _ _)

theorem exists_envelope_minimizer (xi rho : Real) :
    ∃ v ∈ Icc (0 : Real) 1,
      psi xi rho = envelopeObjective xi rho v := by
  have hcompact : IsCompact
      (envelopeObjective xi rho '' Icc (0 : Real) 1) :=
    isCompact_Icc.image (continuous_envelopeObjective xi rho)
  have hmem := hcompact.sInf_mem (envelopeObjective_image_nonempty xi rho)
  rcases hmem with ⟨v, hv, hvalue⟩
  refine ⟨v, hv, ?_⟩
  unfold psi
  exact hvalue.symm

theorem psi_nonneg {xi rho : Real} (hrho : 0 <= rho) :
    0 <= psi xi rho := by
  rcases exists_envelope_minimizer xi rho with ⟨v, hv, hvalue⟩
  rw [hvalue]
  exact envelopeObjective_nonneg hrho

lemma mul_le_max_zero {lambda t : Real}
    (hlambda : lambda ∈ Icc (0 : Real) 1) :
    lambda * t ≤ max t 0 := by
  by_cases ht : 0 ≤ t
  · rw [max_eq_left ht]
    nlinarith [mul_le_mul_of_nonneg_right hlambda.2 ht]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    rw [max_eq_right ht']
    exact mul_nonpos_of_nonneg_of_nonpos hlambda.1 ht'

theorem envelopeDual_le_envelopeObjective
    {xi rho lambda v : Real}
    (hrho : 0 ≤ rho)
    (hlambda : lambda ∈ Icc (0 : Real) 1) :
    envelopeDual xi rho lambda ≤ envelopeObjective xi rho v := by
  have hmax := mul_le_max_zero
    (t := xi - v + v ^ 2) hlambda
  by_cases ha : rho + lambda = 0
  · have hrho0 : rho = 0 := by nlinarith [hlambda.1]
    have hlambda0 : lambda = 0 := by nlinarith
    rw [hrho0, hlambda0]
    simp [envelopeDual, envelopeObjective]
  · have ha0 : 0 < rho + lambda := by
      have : 0 ≤ rho + lambda := add_nonneg hrho hlambda.1
      exact lt_of_le_of_ne this (Ne.symm ha)
    have hquad :
        -(lambda ^ 2) / (4 * (rho + lambda)) ≤
          (rho + lambda) * v ^ 2 - lambda * v := by
      rw [div_le_iff₀ (by positivity : 0 < 4 * (rho + lambda))]
      nlinarith [sq_nonneg (2 * (rho + lambda) * v - lambda)]
    unfold envelopeDual envelopeObjective
    calc
      lambda * xi - lambda ^ 2 / (4 * (rho + lambda)) ≤
          lambda * xi + ((rho + lambda) * v ^ 2 - lambda * v) := by
            calc
              lambda * xi - lambda ^ 2 / (4 * (rho + lambda)) =
                  lambda * xi + (-(lambda ^ 2) / (4 * (rho + lambda))) := by ring
              _ ≤ _ := by
                simpa [add_comm] using add_le_add_left hquad (lambda * xi)
      _ = rho * v ^ 2 +
          lambda * (xi - v + v ^ 2) := by ring
      _ ≤ rho * v ^ 2 + max (xi - v + v ^ 2) 0 :=
        by simpa [add_comm] using add_le_add_right hmax (rho * v ^ 2)

theorem envelopeDual_le_psi
    {xi rho lambda : Real}
    (hrho : 0 ≤ rho)
    (hlambda : lambda ∈ Icc (0 : Real) 1) :
    envelopeDual xi rho lambda ≤ psi xi rho := by
  unfold psi
  apply le_csInf (envelopeObjective_image_nonempty xi rho)
  intro y hy
  rcases hy with ⟨v, hv, rfl⟩
  exact envelopeDual_le_envelopeObjective hrho hlambda

theorem psi_ge_dual_one {xi rho : Real} (hrho : 0 ≤ rho) :
    xi - 1 / (4 * (rho + 1)) ≤ psi xi rho := by
  simpa [envelopeDual] using
    (envelopeDual_le_psi (xi := xi) (rho := rho) (lambda := 1) hrho
      (by constructor <;> norm_num))

end OddCycleBound.IntermediateRegion.Scalar

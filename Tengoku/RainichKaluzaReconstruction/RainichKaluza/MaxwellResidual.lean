import Tengoku.RainichKaluzaReconstruction.RainichKaluza.ReconstructionEquation
import Tengoku.Seed.Tactic.NoncommRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The reconstructed Maxwell residual

Given a Ricci-like endomorphism `R` and an accepted rank-one scalar candidate
`V`, define the residual `S=R-V`.  This file proves that, once the scalar
square law is imposed, the Sylvester reconstruction equation is *equivalent*
to the central algebraic Maxwell--Rainich identity `S²=q²I`.

This reaches the algebraic entrance to Phase III.  It does not yet construct a
Maxwell two-form square root, impose the energy condition, or solve the
differential complexion equations.
-/

namespace RainichKaluza

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Residual after subtracting the reconstructed scalar contribution.-/
def maxwellResidual (R V : A) : A :=
  R - V

omit [Algebra ℝ A] in
/-- The residual and scalar contribution reconstruct the original operator.-/
theorem maxwellResidual_add_scalar (R V : A) :
    maxwellResidual R V + V = R := by
  unfold maxwellResidual
  abel

/-- **Residual Maxwell square theorem.** The reconstruction equation and the
rank-one scalar square law force the residual to square to `q²I`.-/
theorem maxwellResidual_sq_of_reconstructionEquation
    (R V : A) (traceV qSq : ℝ)
    (hV : V * V = traceV • V)
    (hrecon : R * V + V * R - traceV • V =
      R * R - qSq • (1 : A)) :
    maxwellResidual R V * maxwellResidual R V = qSq • (1 : A) := by
  unfold maxwellResidual
  calc
    (R - V) * (R - V) = R * R - R * V - V * R + V * V := by
      noncomm_ring
    _ = R * R - (R * V + V * R - traceV • V) := by
      rw [hV]
      noncomm_ring
    _ = R * R - (R * R - qSq • (1 : A)) := by rw [hrecon]
    _ = qSq • (1 : A) := by noncomm_ring

/-- **Exact algebraic Phase-III interface.** Under the scalar square law, the
Sylvester reconstruction equation is equivalent to the Maxwell residual
square identity.-/
theorem reconstructionEquation_iff_maxwellResidual_sq
    (R V : A) (traceV qSq : ℝ)
    (hV : V * V = traceV • V) :
    (R * V + V * R - traceV • V =
        R * R - qSq • (1 : A)) ↔
      (maxwellResidual R V * maxwellResidual R V =
        qSq • (1 : A)) := by
  constructor
  · exact maxwellResidual_sq_of_reconstructionEquation R V traceV qSq hV
  · intro hresidual
    exact reconstructionEquation_of_eq_add R (maxwellResidual R V) V
      traceV qSq (maxwellResidual_add_scalar R V).symm hresidual hV

/-- If `R` and `V` have the same supplied trace, their residual is tracefree.
This is stated for an arbitrary real-linear trace functional.-/
theorem maxwellResidual_trace_zero
    (trace : A →ₗ[ℝ] ℝ) (R V : A) (traceV : ℝ)
    (hR : trace R = traceV) (hV : trace V = traceV) :
    trace (maxwellResidual R V) = 0 := by
  simp [maxwellResidual, hR, hV]

end RainichKaluza

import Tengoku.Seed.LinearAlgebra.Matrix.Trace
import Tengoku.Seed.Tactic.FinCases
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionSelfAdjointCarrier
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.OuterProductScaling

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms trace_grouped` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms top_left_projector_equation` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms adjugate_of_actual_projector` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms same_a_actual_projector_fibre` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.ProjectorBlockBridge

open AlbertLean.Generic.QuaternionRow.ScalarFibre
open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Half the ordinary six-dimensional trace, fixed as the quaternionic
Jordan-trace convention.-/
def jordanTrace (P : Mat6 K) : K := (2 : K)⁻¹ * Matrix.trace P

theorem trace_grouped (a : Mat3 K) (u v : Vec3 K) :
    Matrix.trace (grouped a u v) = 2 * Matrix.trace a := by
  simp [Matrix.trace, grouped, Fintype.sum_sum_type, Fin.sum_univ_succ,
    Matrix.transpose_apply]
  ring

@[simp] theorem jordanTrace_grouped (a : Mat3 K) (u v : Vec3 K) :
    jordanTrace (grouped a u v) = Matrix.trace a := by
  rw [jordanTrace, trace_grouped]
  field_simp

/-- The top-left block of the actual matrix projector equation.-/
theorem top_left_projector_equation
    (a : Mat3 K) (u v : Vec3 K)
    (hidem : grouped a u v * grouped a u v = grouped a u v) :
    a * a - a = -(hat u * hat v) := by
  apply sub_eq_iff_eq_add.mpr
  ext i j
  have h := congrFun (congrFun hidem (Sum.inl i)) (Sum.inl j)
  fin_cases i <;> fin_cases j <;>
    simp [grouped, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_succ] at h ⊢ <;> linear_combination h

theorem grouped_trace_one
    (a : Mat3 K) (u v : Vec3 K)
    (htrace : jordanTrace (grouped a u v) = 1) : Matrix.trace a = 1 := by
  simpa using htrace

/-- An actual trace-one idempotent in the self-adjoint carrier supplies the
exact hypotheses of the adjugate scalar-fibre theorem.-/
theorem adjugate_of_actual_projector
    (P : Carrier K) (a : Mat3 K) (u v : Vec3 K)
    (hP : (P : Mat6 K) = grouped a u v)
    (hidem : (P : Mat6 K) * P = P)
    (htrace : jordanTrace (K := K) (P : Mat6 K) = 1) :
    Matrix.adjugate a = -outer v u := by
  apply adjugate_of_projector_trace_one a u v
  · apply top_left_projector_equation a u v
    simpa [hP] using hidem
  · apply grouped_trace_one a u v
    simpa [hP] using htrace

/-- Honest same-`a` fibre theorem whose premises are actual carrier
idempotence and half-trace one, rather than pre-supplied block equations.-/
theorem same_a_actual_projector_fibre
    (P P' : Carrier K) (a : Mat3 K) (u v u' v' : Vec3 K)
    (hP : (P : Mat6 K) = grouped a u v)
    (hP' : (P' : Mat6 K) = grouped a u' v')
    (hidem : (P : Mat6 K) * P = P)
    (hidem' : (P' : Mat6 K) * P' = P')
    (htrace : jordanTrace (K := K) (P : Mat6 K) = 1)
    (hadj : Matrix.adjugate a ≠ 0) :
    ∃ t : K, t ≠ 0 ∧ u' = t • u ∧ v' = t⁻¹ • v := by
  apply same_a_scalar_fibre a u v u' v'
  · apply top_left_projector_equation a u v
    simpa [hP] using hidem
  · apply top_left_projector_equation a u' v'
    simpa [hP'] using hidem'
  · apply grouped_trace_one a u v
    simpa [hP] using htrace
  · exact hadj

end AlbertLean.Generic.QuaternionRow.ProjectorBlockBridge

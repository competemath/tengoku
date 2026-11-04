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

/--
@isnad1 id=eq.0h4v.s7.f2be08d81533 from=translated src=- shape=c1324433 vocab=3f6e80d8
-/
theorem trace_grouped (a : Mat3 K) (u v : Vec3 K) :
    Matrix.trace (grouped a u v) = 2 * Matrix.trace a := by
  simp [Matrix.trace, grouped, Fintype.sum_sum_type, Fin.sum_univ_succ,
    Matrix.transpose_apply]
  ring

/--
@isnad1 id=eq.0h4v.s5.1c284b2e0fa6 from=translated src=- shape=09b92073 vocab=f0a4e526
-/
@[simp] theorem jordanTrace_grouped (a : Mat3 K) (u v : Vec3 K) :
    jordanTrace (grouped a u v) = Matrix.trace a := by
  rw [jordanTrace, trace_grouped]
  field_simp

/-- The top-left block of the actual matrix projector equation.
@isnad1 id=eq.1h4v.s8.9dc079641c52 from=translated src=- shape=745b4c3c vocab=ce0d166b
-/
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

/--
@isnad1 id=eq.1h4v.s6.309f7b13e987 from=translated src=- shape=ec75f878 vocab=f0a4e526
-/
theorem grouped_trace_one
    (a : Mat3 K) (u v : Vec3 K)
    (htrace : jordanTrace (grouped a u v) = 1) : Matrix.trace a = 1 := by
  simpa using htrace

/-- An actual trace-one idempotent in the self-adjoint carrier supplies the
exact hypotheses of the adjugate scalar-fibre theorem.
@isnad1 id=eq.3h5v.s10.43333a9862e0 from=translated src=- shape=273d45f3 vocab=b3b5c3f5
-/
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
idempotence and half-trace one, rather than pre-supplied block equations.
@isnad1 id=ex.6h8v.s11.ebc064ee5bc8 from=translated src=- shape=1a0c57ff vocab=96b11e42
-/
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

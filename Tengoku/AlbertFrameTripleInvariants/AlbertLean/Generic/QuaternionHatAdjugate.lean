import Tengoku.Seed.LinearAlgebra.Matrix.Adjugate
import Tengoku.Seed.LinearAlgebra.Matrix.Trace
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms hat_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms adjugate_fin_three_trace` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms adjugate_of_projector_trace_one` (it only prints; the queue checks the axioms of every declaration). -/

/-! The grouped `W ⊕ W*` coordinates used by the quaternionic shortcut.
This module deliberately does not identify them definitionally with the
interleaved `Fin 3 × Fin 2` coordinates of `Mat2Star`: that permutation is a
separate bridge. -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.ScalarFibre

universe u
variable {K : Type u} [Field K] [CharZero K]

abbrev Vec3 (K : Type u) := Fin 3 → K
abbrev Mat3 (K : Type u) := Matrix (Fin 3) (Fin 3) K

/-- The cross-product matrix in the literal grouped-basis sign convention.-/
def hat (u : Vec3 K) : Mat3 K :=
  !![0, -u 2, u 1; u 2, 0, -u 0; -u 1, u 0, 0]

/-- The ordinary coordinate pairing between `W` and `W*`.-/
def dot (u v : Vec3 K) : K := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- Column times row, with the first argument supplying the column.-/
def outer (v u : Vec3 K) : Mat3 K := fun i j => v i * u j

/-- The decisive sign-sensitive cross-product identity.-/
theorem hat_mul (u v : Vec3 K) :
    hat u * hat v = outer v u - dot u v • (1 : Mat3 K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hat, outer, dot, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- The trace-polynomial form of the three-dimensional adjugate identity.-/
theorem adjugate_fin_three_trace (a : Mat3 K) :
    Matrix.adjugate a =
      a * a - Matrix.trace a • a +
        (((Matrix.trace a) ^ 2 - Matrix.trace (a * a)) / 2) •
          (1 : Mat3 K) := by
  rw [Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- For the top-left block of a trace-one grouped self-adjoint projector,
the adjugate is the outer-product datum carried by the two skew blocks.
The projector hypothesis needed here is exactly its top-left block equation.-/
theorem adjugate_of_projector_trace_one
    (a : Mat3 K) (u v : Vec3 K)
    (hblock : a * a - a = -(hat u * hat v))
    (htrace : Matrix.trace a = 1) :
    Matrix.adjugate a = -outer v u := by
  have hhat := hat_mul u v
  have hsq : a * a = a - outer v u + dot u v • (1 : Mat3 K) := by
    calc
      a * a = (a * a - a) + a := by abel
      _ = -(hat u * hat v) + a := by rw [hblock]
      _ = -(outer v u - dot u v • (1 : Mat3 K)) + a := by rw [hhat]
      _ = a - outer v u + dot u v • (1 : Mat3 K) := by abel
  have htrsq : Matrix.trace (a * a) = 1 + 2 * dot u v := by
    have h := congrArg Matrix.trace hsq
    simp [Matrix.trace, Fin.sum_univ_succ, outer, dot] at h htrace ⊢
    linear_combination h + htrace
  rw [adjugate_fin_three_trace, htrace, htrsq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hsq, outer] <;> ring

end AlbertLean.Generic.QuaternionRow.ScalarFibre

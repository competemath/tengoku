import Tengoku.RainichKaluzaReconstruction.RainichKaluza.MaxwellResidual
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Module
import Tengoku.Seed.Tactic.NoncommRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Maxwell principal-plane projectors

A non-null algebraic Maxwell residual satisfies `S²=q²I` with `q≠0`.
Normalizing by `q` therefore gives an involution.  Its `±1` projectors recover
the two Maxwell principal subspaces without choosing eigenvectors.  The
remaining Phase-III problem is the two-form square root and its duality
complexion, not the stress principal-plane splitting.
-/

namespace RainichKaluza

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Unit-normalized non-null Maxwell residual.-/
noncomputable def normalizedMaxwellResidual (S : A) (q : ℝ) : A :=
  q⁻¹ • S

/-- A non-null normalized residual is involutive.-/
theorem normalizedMaxwellResidual_sq
    (S : A) (q : ℝ) (hq : q ≠ 0)
    (hS : S * S = q ^ 2 • (1 : A)) :
    normalizedMaxwellResidual S q * normalizedMaxwellResidual S q = 1 := by
  unfold normalizedMaxwellResidual
  rw [smul_mul_smul, hS, smul_smul]
  have hcoeff : q⁻¹ * q⁻¹ * q ^ 2 = 1 := by
    field_simp [hq]
  rw [hcoeff, one_smul]

/-- `+1` projector of an involution.-/
noncomputable def involutionPlusProjector (J : A) : A :=
  (2 : ℝ)⁻¹ • (1 + J)

/-- `-1` projector of an involution.-/
noncomputable def involutionMinusProjector (J : A) : A :=
  (2 : ℝ)⁻¹ • (1 - J)

/-- The positive projector is idempotent.-/
theorem involutionPlusProjector_sq
    (J : A) (hJ : J * J = 1) :
    involutionPlusProjector J * involutionPlusProjector J =
      involutionPlusProjector J := by
  unfold involutionPlusProjector
  rw [smul_mul_smul]
  have hprod : (1 + J) * (1 + J) = (2 : ℝ) • (1 + J) := by
    calc
      (1 + J) * (1 + J) = 1 + J + J + J * J := by noncomm_ring
      _ = (2 : ℝ) • (1 + J) := by rw [hJ]; module
  rw [hprod, smul_smul]
  norm_num

/-- The negative projector is idempotent.-/
theorem involutionMinusProjector_sq
    (J : A) (hJ : J * J = 1) :
    involutionMinusProjector J * involutionMinusProjector J =
      involutionMinusProjector J := by
  unfold involutionMinusProjector
  rw [smul_mul_smul]
  have hprod : (1 - J) * (1 - J) = (2 : ℝ) • (1 - J) := by
    calc
      (1 - J) * (1 - J) = 1 - J - J + J * J := by noncomm_ring
      _ = (2 : ℝ) • (1 - J) := by rw [hJ]; module
  rw [hprod, smul_smul]
  norm_num

/-- The two principal projectors are orthogonal.-/
theorem involutionProjectors_orthogonal
    (J : A) (hJ : J * J = 1) :
    involutionPlusProjector J * involutionMinusProjector J = 0 := by
  unfold involutionPlusProjector involutionMinusProjector
  rw [smul_mul_smul]
  have hprod : (1 + J) * (1 - J) = 0 := by
    calc
      (1 + J) * (1 - J) = 1 - J * J := by noncomm_ring
      _ = 0 := by rw [hJ]; noncomm_ring
  rw [hprod, smul_zero]

/-- The principal projectors resolve the identity.-/
theorem involutionProjectors_sum (J : A) :
    involutionPlusProjector J + involutionMinusProjector J = 1 := by
  unfold involutionPlusProjector involutionMinusProjector
  module

/-- The normalized residual acts by `+1` on the positive projector.-/
theorem involution_mul_plusProjector
    (J : A) (hJ : J * J = 1) :
    J * involutionPlusProjector J = involutionPlusProjector J := by
  unfold involutionPlusProjector
  rw [mul_smul_comm]
  congr 1
  calc
    J * (1 + J) = J + J * J := by rw [mul_add, mul_one]
    _ = 1 + J := by rw [hJ]; abel

/-- The normalized residual acts by `-1` on the negative projector.-/
theorem involution_mul_minusProjector
    (J : A) (hJ : J * J = 1) :
    J * involutionMinusProjector J = -involutionMinusProjector J := by
  unfold involutionMinusProjector
  rw [mul_smul_comm, ← smul_neg]
  congr 1
  calc
    J * (1 - J) = J - J * J := by rw [mul_sub, mul_one]
    _ = -(1 - J) := by rw [hJ]; noncomm_ring

/-- Positive Maxwell principal projector reconstructed directly from `S`.-/
noncomputable def maxwellPlusProjector (S : A) (q : ℝ) : A :=
  involutionPlusProjector (normalizedMaxwellResidual S q)

/-- Negative Maxwell principal projector reconstructed directly from `S`.-/
noncomputable def maxwellMinusProjector (S : A) (q : ℝ) : A :=
  involutionMinusProjector (normalizedMaxwellResidual S q)

/-- On the non-null branch, the reconstructed positive Maxwell projector is
idempotent.-/
theorem maxwellPlusProjector_sq
    (S : A) (q : ℝ) (hq : q ≠ 0)
    (hS : S * S = q ^ 2 • (1 : A)) :
    maxwellPlusProjector S q * maxwellPlusProjector S q =
      maxwellPlusProjector S q :=
  involutionPlusProjector_sq _
    (normalizedMaxwellResidual_sq S q hq hS)

/-- On the non-null branch, the reconstructed negative Maxwell projector is
idempotent.-/
theorem maxwellMinusProjector_sq
    (S : A) (q : ℝ) (hq : q ≠ 0)
    (hS : S * S = q ^ 2 • (1 : A)) :
    maxwellMinusProjector S q * maxwellMinusProjector S q =
      maxwellMinusProjector S q :=
  involutionMinusProjector_sq _
    (normalizedMaxwellResidual_sq S q hq hS)

/-- The two reconstructed Maxwell principal projectors resolve the identity.-/
theorem maxwellProjectors_sum (S : A) (q : ℝ) :
    maxwellPlusProjector S q + maxwellMinusProjector S q = 1 :=
  involutionProjectors_sum _

end RainichKaluza

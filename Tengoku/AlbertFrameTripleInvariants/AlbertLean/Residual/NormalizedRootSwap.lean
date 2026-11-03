import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.ResidualMatrices
import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms NormalizedResidualSectionRootSwapTheorem` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Root exchange on the normalized residual section

This module isolates the source-independent algebra of the normalized
residual section.  A point consists of a matrix `M`, a nonzero determinant
root `Delta`, and the nonvanishing of `det M`.  The second root is derived as
`det M / Delta`; it is not free data.  The normalized representative is
`X0 = diag(1,1,1,Delta)` and `A0 = M * X0⁻¹`.

The root exchange below is an involution of these explicit section records.
It is not the free-label swap in `FrameIdeal`, the intrinsic automorphism of
`RootPairAlgebra`, a source outer transition, or a global deck involution.
No quotient, function-field degree, connected-cover, Albert, or physics claim
is made.
-/

namespace AlbertLean.Residual.NormalizedRootSwap

open Matrix

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- A normalized residual-section point on the open where both `Delta` and
`det M` are nonzero.-/
@[ext]
structure NormalizedResidualSection (K : Type u) [Field K] where
  M : Matrix (Fin 4) (Fin 4) K
  Delta : K
  Delta_ne_zero : Delta ≠ 0
  detM_ne_zero : Matrix.det M ≠ 0

/-- The second determinant root, derived from the printed hypersurface
relation rather than stored as independent data.-/
def DeltaStar (s : NormalizedResidualSection K) : K :=
  Matrix.det s.M / s.Delta

/-- The symmetric root sum retained by the base of the section fibre.-/
def Sb (s : NormalizedResidualSection K) : K :=
  s.Delta + DeltaStar s

/-- The locked normal representative `diag(1,1,1,Delta)`.-/
def X0 (s : NormalizedResidualSection K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.diagonal ![1, 1, 1, s.Delta]

/-- The locked normalized covector matrix `M * X0⁻¹`.-/
def A0 (s : NormalizedResidualSection K) : Matrix (Fin 4) (Fin 4) K :=
  s.M * (X0 s)⁻¹

/-- The normalized vector representative has determinant `Delta`.
@isnad1 id=eq.0h2v.s5.4681af6b12c4 from=translated src=- shape=33e72a07 vocab=8599fa62
-/
@[simp] theorem det_X0 (s : NormalizedResidualSection K) :
    Matrix.det (X0 s) = s.Delta := by
  simp [X0, Matrix.det_diagonal, Fin.prod_univ_succ]

private theorem isUnit_det_X0 (s : NormalizedResidualSection K) :
    IsUnit (Matrix.det (X0 s)) := by
  rw [det_X0]
  exact isUnit_iff_ne_zero.mpr s.Delta_ne_zero

/-- The two derived roots multiply to `det M`.
@isnad1 id=eq.0h2v.s5.8b88092fde55 from=translated src=- shape=1225a8d8 vocab=4b2ab994
-/
theorem Delta_mul_DeltaStar (s : NormalizedResidualSection K) :
    s.Delta * DeltaStar s = Matrix.det s.M := by
  simp only [DeltaStar]
  field_simp [s.Delta_ne_zero]

/-- The normalized pair reconstructs the retained evaluation matrix.
@isnad1 id=eq.0h2v.s6.6e654e88a390 from=translated src=- shape=bd118414 vocab=29fa0171
-/
theorem A0_mul_X0 (s : NormalizedResidualSection K) :
    A0 s * X0 s = s.M := by
  rw [A0, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_det_X0 s), Matrix.mul_one]

/-- The normalized covector representative has determinant `DeltaStar`.
@isnad1 id=eq.0h2v.s5.619b84ca347a from=translated src=- shape=33e72a07 vocab=abed6ed1
-/
@[simp] theorem det_A0 (s : NormalizedResidualSection K) :
    Matrix.det (A0 s) = DeltaStar s := by
  rw [A0, Matrix.det_mul, Matrix.det_nonsing_inv, det_X0]
  simp only [Ring.inverse_eq_inv, DeltaStar, div_eq_mul_inv]

/-- Exchange the actual section root while fixing `M`.-/
def rootSwap (s : NormalizedResidualSection K) : NormalizedResidualSection K where
  M := s.M
  Delta := DeltaStar s
  Delta_ne_zero := div_ne_zero s.detM_ne_zero s.Delta_ne_zero
  detM_ne_zero := s.detM_ne_zero

/--
@isnad1 id=eq.0h2v.s5.a65c48f8239d from=translated src=- shape=9cb91734 vocab=2b653247
-/
@[simp] theorem rootSwap_M (s : NormalizedResidualSection K) :
    (rootSwap s).M = s.M := rfl

/--
@isnad1 id=eq.0h2v.s4.ec63a0783d7f from=translated src=- shape=0800dc30 vocab=3bed4afc
-/
@[simp] theorem rootSwap_Delta (s : NormalizedResidualSection K) :
    (rootSwap s).Delta = DeltaStar s := rfl

/--
@isnad1 id=eq.0h2v.s6.3f2f9f16a83f from=translated src=- shape=55aba948 vocab=8684550b
-/
@[simp] theorem rootSwap_detM (s : NormalizedResidualSection K) :
    Matrix.det (rootSwap s).M = Matrix.det s.M := rfl

/-- The derived second root after exchange is the original first root.
@isnad1 id=eq.0h2v.s4.1d2f3a2af589 from=translated src=- shape=0800dc30 vocab=3bed4afc
-/
@[simp] theorem rootSwap_DeltaStar (s : NormalizedResidualSection K) :
    DeltaStar (rootSwap s) = s.Delta := by
  simp only [DeltaStar, rootSwap_M, rootSwap_Delta]
  field_simp [s.Delta_ne_zero, s.detM_ne_zero]

/-- The symmetric root sum is fixed by section root exchange.
@isnad1 id=eq.0h2v.s4.9ff2c7abbdc7 from=translated src=- shape=660825d4 vocab=5034783e
-/
@[simp] theorem rootSwap_Sb (s : NormalizedResidualSection K) :
    Sb (rootSwap s) = Sb s := by
  simp [Sb, add_comm]

/-- The section root exchange is an involution.
@isnad1 id=eq.0h2v.s4.672481d28580 from=translated src=- shape=2896fe98 vocab=85fdc97c
-/
@[simp] theorem rootSwap_involutive (s : NormalizedResidualSection K) :
    rootSwap (rootSwap s) = s := by
  apply NormalizedResidualSection.ext
  · rfl
  · exact rootSwap_DeltaStar s

/-- The first actual root satisfies the section quadratic.
@isnad1 id=eq.0h2v.s7.4e93fc6268f0 from=translated src=- shape=e63fe959 vocab=e5048f07
-/
theorem Delta_root_relation (s : NormalizedResidualSection K) :
    s.Delta ^ 2 - Sb s * s.Delta + Matrix.det s.M = 0 := by
  rw [Sb, ← Delta_mul_DeltaStar s]
  ring

/-- The derived second root satisfies the same section quadratic.
@isnad1 id=eq.0h2v.s7.2dd22ff38179 from=translated src=- shape=e63fe959 vocab=937cc271
-/
theorem DeltaStar_root_relation (s : NormalizedResidualSection K) :
    DeltaStar s ^ 2 - Sb s * DeltaStar s + Matrix.det s.M = 0 := by
  rw [Sb, ← Delta_mul_DeltaStar s]
  ring

/-- After exchange, the two normalized determinant representatives exchange
their determinant values.
@isnad1 id=and.0h2v.s6.da18745869a5 from=translated src=- shape=00637325 vocab=221a0eb3
-/
theorem rootSwap_exchanges_normalized_determinants
    (s : NormalizedResidualSection K) :
    Matrix.det (X0 (rootSwap s)) = DeltaStar s ∧
      Matrix.det (A0 (rootSwap s)) = s.Delta := by
  exact ⟨det_X0 (rootSwap s), by simp⟩

/-- the complete normalized-section
root-exchange package.  It is a statement about explicit matrix coordinates,
not a descended or global action.
@isnad1 id=and.0h2v.s9.9813b9cadf98 from=translated src=- shape=17ce6f57 vocab=ece901d9
-/
theorem NormalizedResidualSectionRootSwapTheorem
    (s : NormalizedResidualSection K) :
    rootSwap (rootSwap s) = s ∧
      (rootSwap s).M = s.M ∧
      DeltaStar (rootSwap s) = s.Delta ∧
      Sb (rootSwap s) = Sb s ∧
      Matrix.det (X0 s) = s.Delta ∧
      Matrix.det (A0 s) = DeltaStar s ∧
      A0 s * X0 s = s.M ∧
      s.Delta * DeltaStar s = Matrix.det s.M ∧
      Matrix.det (X0 (rootSwap s)) = DeltaStar s ∧
      Matrix.det (A0 (rootSwap s)) = s.Delta ∧
      s.Delta ^ 2 - Sb s * s.Delta + Matrix.det s.M = 0 ∧
      DeltaStar s ^ 2 - Sb s * DeltaStar s + Matrix.det s.M = 0 := by
  exact ⟨rootSwap_involutive s, rootSwap_M s, rootSwap_DeltaStar s,
    rootSwap_Sb s, det_X0 s, det_A0 s, A0_mul_X0 s,
    Delta_mul_DeltaStar s, (rootSwap_exchanges_normalized_determinants s).1,
    (rootSwap_exchanges_normalized_determinants s).2,
    Delta_root_relation s, DeltaStar_root_relation s⟩

end

end AlbertLean.Residual.NormalizedRootSwap

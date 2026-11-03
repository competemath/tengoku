import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.GenericNormalizedFrameChart

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms omitted_diagonal` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms solve_diagonal_pair` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms actual_diagonal_systems` (it only prints; the queue checks the axioms of every declaration). -/

/-! The actual four scalar systems needed after finite V-pair readback.
No residual action, normalization existence, or generic-open assertion is
assumed or concluded by this small algebraic attachment. -/
noncomputable section
namespace AlbertLean.Generic.SourceChartDiagonalReadback

open AlbertLean.Residual.FrameIdeal
open AlbertLean.Generic.ChartBridge
open AlbertLean.Generic.GenericNormalizedFrameChart

universe u
variable {K : Type u} [Field K] [CharZero K]

def parameters (q : ExplicitFrameChart K) : Parameters K where
  dA0 := q.diagA 0
  dA1 := q.diagA 1
  dB0 := q.diagB 0
  dB1 := q.diagB 1
  a := q.z1
  b := q.r2
  c := q.z2
  offDiag ij _ := matrixM q ij.1 ij.2
  Delta := Matrix.det (residualPairOfChart q).X

/-- The two trace laws reconstruct the omitted diagonal source entries.
@isnad1 id=and.1h2v.s6.9de347a1d510 from=translated src=- shape=50ab849f vocab=2fcd33e3
-/
theorem omitted_diagonal (q : ExplicitFrameChart K)
    (hq : EquationsVanish (explicitFrameEquationValues q)) :
    dA2 (parameters q) = q.diagA 2 ∧ dB2 (parameters q) = q.diagB 2 := by
  rcases hq with ⟨hTA, _, _, hTB, _, _⟩
  change q.diagA 0 + q.diagA 1 + q.diagA 2 = 0 at hTA
  change q.diagB 0 + q.diagB 1 + q.diagB 2 = 0 at hTB
  constructor
  · change -q.diagA 0 - q.diagA 1 = q.diagA 2
    linear_combination -hTA
  · change -q.diagB 0 - q.diagB 1 = q.diagB 2
    linear_combination -hTB

/-- This is the exact scalar inversion used by all four diagonal M entries.
@isnad1 id=and.3h7v.s8.61c5a0ff138d from=translated src=- shape=739799e6 vocab=4c76edc2
-/
theorem solve_diagonal_pair (d₁ d₂ S N x y : K)
    (hp : d₁ - d₂ ≠ 0) (hS : x + y = S)
    (hN : d₁ * x + d₂ * y = N) :
    (N - d₂ * S) / (d₁ - d₂) = x ∧
      S - (N - d₂ * S) / (d₁ - d₂) = y := by
  have hx : (N - d₂ * S) / (d₁ - d₂) = x := by
    apply (div_eq_iff hp).2
    linear_combination -hN + d₂ * hS
  refine ⟨hx, ?_⟩
  rw [hx]
  linear_combination -hS

/-- Read the four systems from the actual six source equations. The only
extra hypothesis is r1=1, already supplied by targetFirst normalization.
@isnad1 id=and.2h2v.s9.a0d3383e4702 from=translated src=- shape=9ce94e5b vocab=76bd10ab
-/
theorem actual_diagonal_systems (q : ExplicitFrameChart K)
    (hr : q.r1 = 1)
    (hq : EquationsVanish (explicitFrameEquationValues q)) :
    matrixM q 0 0 + matrixM q 2 2 = spurSumA (parameters q) ∧
    q.diagA 1 * matrixM q 0 0 + q.diagA 2 * matrixM q 2 2 =
      normWeightedA (parameters q) ∧
    matrixM q 1 1 + matrixM q 3 3 = spurSumB (parameters q) ∧
    q.diagB 1 * matrixM q 1 1 + q.diagB 2 * matrixM q 3 3 =
      normWeightedB (parameters q) := by
  have hdiag := omitted_diagonal q hq
  rcases hq with ⟨_, hSA, hNA, _, hSB, hNB⟩
  simp only [explicitFrameEquationValues, hr, one_mul] at hSA hNA hSB hNB
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [spurSumA, hdiag.1]
    change matrixM q 0 0 + matrixM q 2 2 =
      q.diagA 0 * q.diagA 1 + q.diagA 0 * q.diagA 2 +
        q.diagA 1 * q.diagA 2 - q.z1 + 1
    linear_combination -hSA
  · rw [normWeightedA, hdiag.1]
    simp [rawOffDiag, parameters]
    linear_combination -hNA
  · rw [spurSumB, hdiag.2]
    change matrixM q 1 1 + matrixM q 3 3 =
      q.diagB 0 * q.diagB 1 + q.diagB 0 * q.diagB 2 +
        q.diagB 1 * q.diagB 2 - q.r2 * q.z2 + 1
    linear_combination -hSB
  · rw [normWeightedB, hdiag.2]
    simp [rawOffDiag, parameters]
    linear_combination -hNB

end AlbertLean.Generic.SourceChartDiagonalReadback

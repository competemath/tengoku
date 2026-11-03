import Tengoku
import Tengoku.Seed.Algebra.Field.Rat
import Tengoku.Seed.Algebra.Module.Equiv.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reconstruction on a fixed rational matrix chart

This module states a reconstruction proposition for an explicit open subset
of a fixed-moment rational matrix stratum. The chart gives ordered frames in
Tau Ceti's split Albert algebra. On this chart, a rational-linear unital Jordan
automorphism relates two triples exactly when their measurement tables and
trace-cube detectors agree. The proposition also specifies two inequivalent
representatives of each measurement fiber within the chart.

The proof is in `TauReconstruction.lean`. This restricted chart result is
separate from the full raw-function-field theorem in `OneBit.oneBit`.
-/
noncomputable section

namespace AlbertLean.Generic.SecondStatement

abbrev Coord := Fin 27 → ℚ
abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℚ
local instance : Invertible (2 : ℚ) := invertibleOfNonzero (by decide)

/-- The fixed accepted residual moment `A*X`.-/
def M : Mat4 :=
  ![![3/2, -2, -245/54, -3/2],
    ![-2, 1, -3/2, 1],
    ![0, -2, -35/18, 2],
    ![3/2, -91/27, 0, -13/9]]

/-- A covector-row matrix and a vector-column matrix: 32 visible variables.-/
structure MatrixPair where
  A : Mat4
  X : Mat4

/-- Diagonal normal form used for determinant-root parameter `t`.-/
def diagonal4 (t : ℚ) : Mat4 := Matrix.diagonal ![1, 1, 1, t]

/-- `P(t) = (M diag(1,1,1,t^-1), diag(1,1,1,t))`.-/
def normalizedPair (t : ℚ) : MatrixPair :=
  ⟨M * diagonal4 t⁻¹, diagonal4 t⟩

/-- The exact 27 pair moments and 27 centered joint moments.-/
structure Ledger where
  P : Fin 3 → Fin 3 → ℚ
  Q : Fin 3 → Fin 3 → ℚ
  R : Fin 3 → Fin 3 → ℚ
  C0 : Fin 3 → Fin 3 → Fin 3 → ℚ

/-- The accepted reciprocal determinant product.-/
def m : ℚ := 410231 / 5832

end AlbertLean.Generic.SecondStatement

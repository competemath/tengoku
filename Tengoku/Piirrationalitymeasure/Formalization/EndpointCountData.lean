import Tengoku.Piirrationalitymeasure.Formalization.SavingEndpointGerm
import Tengoku.Piirrationalitymeasure.Formalization.SectorCertificate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Computable rational data for the actual endpoint germs at the candidate. -/

namespace PiIrrationality

def quadraticFloorGermRat (x l q : ℚ) : ℤ :=
  if x = (⌊x⌋ : ℚ) ∧ (l < 0 ∨ (l = 0 ∧ q < 0)) then ⌊x⌋ - 1 else ⌊x⌋

theorem quadraticFloorGerm_ratCast (x l q : ℚ) :
    quadraticFloorGerm (x : ℝ) (l : ℝ) (q : ℝ) = quadraticFloorGermRat x l q := by
  have hx : (x : ℝ) = (⌊x⌋ : ℝ) ↔ x = (⌊x⌋ : ℚ) := by norm_cast
  have hl : (l : ℝ) < 0 ↔ l < 0 := by norm_cast
  have hl0 : (l : ℝ) = 0 ↔ l = 0 := by norm_cast
  have hq : (q : ℝ) < 0 ↔ q < 0 := by norm_cast
  simp only [quadraticFloorGerm, quadraticFloorGermRat, quadraticPerturbationNegative,
    Rat.floor_cast, hx, hl, hl0, hq]

def candidateEndpointSlopeRat : SavingEndpointType → ℚ
  | .A => 1857 | .B => 3714 | .C => 5570 | .Q => 3715

def candidateEndpointShiftRat : SavingEndpointType → ℚ
  | .A => 1 / 2 | .B => 0 | .C => 0 | .Q => 1 / 2

def candidateEndpointGradientRat (v : ℚ × ℚ) : SavingEndpointType → ℚ
  | .A => v.1 | .B => v.2 | .C => 0 | .Q => v.1 + 2 * v.2

def candidateEndpointBaseRat (T : SavingEndpointType) (j : ℤ) : ℚ :=
  ((j : ℚ) - candidateEndpointShiftRat T) / candidateEndpointSlopeRat T

def candidateEndpointVelocityRat (v : ℚ × ℚ) (T : SavingEndpointType) : ℚ :=
  -candidateEndpointGradientRat v T / candidateEndpointSlopeRat T

def candidateEndpointFloorGermRat (v : ℚ × ℚ) (T : SavingEndpointType)
    (j : ℤ) (side : ℚ) (S : SavingEndpointType) : ℤ :=
  quadraticFloorGermRat
    (candidateEndpointSlopeRat S * candidateEndpointBaseRat T j + candidateEndpointShiftRat S)
    (candidateEndpointSlopeRat S * candidateEndpointVelocityRat v T + candidateEndpointGradientRat v S)
    (candidateEndpointSlopeRat S * side)

def candidateEndpointChiGermRat (v : ℚ × ℚ) (T : SavingEndpointType) (j : ℤ) (side : ℚ) : ℤ :=
  if candidateEndpointFloorGermRat v T j side .Q <
      candidateEndpointFloorGermRat v T j side .A +
        2 * candidateEndpointFloorGermRat v T j side .B -
          candidateEndpointFloorGermRat v T j side .C then 1 else 0

def candidateEndpointSize : SavingEndpointType → ℕ
  | .A => 1857 | .B => 3714 | .C => 5570 | .Q => 3715

def candidateEndpointStart : SavingEndpointType → ℤ
  | .A => 1 | .B => 0 | .C => 0 | .Q => 1

def candidateEndpointIndices (T : SavingEndpointType) : Finset ℤ :=
  (Finset.range (candidateEndpointSize T)).map
    ⟨fun n : ℕ => (n : ℤ) + candidateEndpointStart T, by
      intro i j h
      exact_mod_cast (add_right_cancel h)⟩

def candidateEndpointCount (v : ℚ × ℚ) (T : SavingEndpointType) : ℤ :=
  ∑ j ∈ candidateEndpointIndices T,
    (candidateEndpointChiGermRat v T j (-1) - candidateEndpointChiGermRat v T j 1)

def candidateSectorDirection (i : Fin 12) : ℚ × ℚ :=
  ![(2, 1), (1, 1), (1, 3), (-1, 2), (-1, 1), (-3, 1),
    (-2, -1), (-1, -1), (-1, -3), (1, -2), (1, -1), (3, -1)] i

def candidateSectorRow (i : Fin 12) : SectorData :=
  sectorRows[i.1]'(by simpa only [sectorRows_length] using i.2)

def candidateExpectedCount (i : Fin 12) : SavingEndpointType → ℤ
  | .A => (candidateSectorRow i).nA
  | .B => (candidateSectorRow i).nB
  | .C => (candidateSectorRow i).nC
  | .Q => (candidateSectorRow i).nQ

end PiIrrationality

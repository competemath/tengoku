import Tengoku.Piirrationalitymeasure.Formalization.RoundedLogApproximation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The six exact finite logarithm certificates used in (A.25)--(A.27). -/

namespace PiIrrationality

def saddleLogInput (i : Fin 6) : ℚ :=
  match i.val with
  | 0 => 4710661776618520503155596 / 10 ^ 24
  | 1 => 4710661776618520503155597 / 10 ^ 24
  | 2 => 265339959117980760581398972 / 10 ^ 24
  | 3 => 265339959117980760581398973 / 10 ^ 24
  | 4 => 725697065335997235474816912 / 10 ^ 24
  | _ => 725697065335997235474816913 / 10 ^ 24

def saddleLogScale (i : Fin 6) : ℤ :=
  match i.val with
  | 0 | 1 => 2
  | 2 | 3 => 8
  | _ => 9

def saddleLogRounded (i : Fin 6) : ℤ :=
  match i.val with
  | 0 => 1549828402748400408888347380040172059133046229242962664551329
  | 1 => 1549828402748400408888347592324570179907350629707249604380789
  | 2 => 5581011868414668100069534623042591549273555028109114719603884
  | 3 => 5581011868414668100069534626811341658846610308604353739257617
  | 4 => 6587132662367959890666838393148565255518779673028604844756643
  | _ => 6587132662367959890666838394526550709458848587254716797408453

set_option maxRecDepth 100000 in
theorem saddleLogInput_range (i : Fin 6) :
    2 ^ saddleLogScale i ≤ saddleLogInput i ∧
      saddleLogInput i ≤ 2 * 2 ^ saddleLogScale i ∧ |saddleLogScale i| ≤ 9 := by
  revert i
  decide +kernel

-- All floors in the 120-term sums are checked by kernel reduction.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem saddleLogRounded_value (i : Fin 6) :
    roundedScaledLog (saddleLogInput i) (saddleLogScale i) 120 (10 ^ 60) =
      saddleLogRounded i := by
  revert i
  decide +kernel

theorem saddleLog_enclosure (i : Fin 6) :
    |Real.log (saddleLogInput i : ℝ) - (saddleLogRounded i : ℝ) / 10 ^ 60| <
      (2000 : ℝ) / 10 ^ 60 := by
  obtain ⟨hL, hU, hk⟩ := saddleLogInput_range i
  have h := roundedScaledLog_real_error (saddleLogScale i) hL hU
  rw [saddleLogRounded_value] at h
  have hk' : |(saddleLogScale i : ℝ)| ≤ 9 := by exact_mod_cast hk
  apply h.trans_le
  calc
    _ ≤ 10 * ((964 : ℝ) / 10 ^ 120 + 120 / 10 ^ 60) := by gcongr; linarith
    _ ≤ _ := by norm_num

end PiIrrationality

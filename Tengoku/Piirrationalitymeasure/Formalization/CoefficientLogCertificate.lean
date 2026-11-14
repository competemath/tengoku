import Tengoku.Piirrationalitymeasure.Formalization.RoundedLogApproximation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact finite logarithm certificates for the inputs of (4.12). -/

namespace PiIrrationality

def coefficientZLowerRat : ℚ :=
  23918337643845311771849563937315852029007245250806 / 10 ^ 50

def coefficientZUpperRat : ℚ :=
  23918337643845311771849563937315852029007245250807 / 10 ^ 50

def coefficientPRat (z : ℚ) : ℚ := 2 + 6 * z + 9 * z ^ 2 + 6 * z ^ 3 + 2 * z ^ 4

def coefficientLogInput (i : Fin 10) : ℚ :=
  match i.val with
  | 0 => 2
  | 1 => 25
  | 2 => 1 + coefficientZLowerRat
  | 3 => 1 + coefficientZUpperRat
  | 4 => coefficientPRat coefficientZLowerRat
  | 5 => coefficientPRat coefficientZUpperRat
  | 6 => 1 - coefficientZLowerRat
  | 7 => 1 - coefficientZUpperRat
  | 8 => coefficientZLowerRat
  | _ => coefficientZUpperRat

def coefficientLogScale (i : Fin 10) : ℤ :=
  match i.val with
  | 1 => 4
  | 4 | 5 => 2
  | 6 | 7 => -1
  | 8 | 9 => -3
  | _ => 0

def coefficientLogRounded (i : Fin 10) : ℤ :=
  match i.val with
  | 0 => 693147180559945309417232121458176568075500134360255254120652
  | 1 => 3218875824868200749201518666452375279051202708537035443825163
  | 2 => 214452595277842382484089693928407366741309505878584161324158
  | 3 => 214452595277842382484089693928407366741309505878592231154816
  | 4 => 1395904118364809283197089479517439447010325485350574174463614
  | 5 => 1395904118364809283197089479517439447010325485350602512142958
  | 6 => -273362917882480914754447140620841235217431231028202727319635
  | 7 => -273362917882480914754447140620841235217431231028215871091328
  | 8 => -1430524755815414876252477425368007643175816560622935401176150
  | _ => -1430524755815414876252477425368007643175816560622893592250506

set_option maxRecDepth 100000 in
theorem coefficientLogInput_range (i : Fin 10) :
    2 ^ coefficientLogScale i ≤ coefficientLogInput i ∧
      coefficientLogInput i ≤ 2 * 2 ^ coefficientLogScale i ∧
        |coefficientLogScale i| ≤ 4 := by
  revert i
  decide +kernel

-- Kernel reduction checks the integer floors of the 120-term rational sums.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem coefficientLogRounded_value (i : Fin 10) :
    roundedScaledLog (coefficientLogInput i) (coefficientLogScale i) 120 (10 ^ 60) =
      coefficientLogRounded i := by
  revert i
  decide +kernel

theorem coefficientLog_enclosure (i : Fin 10) :
    |Real.log (coefficientLogInput i : ℝ) - (coefficientLogRounded i : ℝ) / 10 ^ 60| <
      (1000 : ℝ) / 10 ^ 60 := by
  obtain ⟨hL, hU, hk⟩ := coefficientLogInput_range i
  have h := roundedScaledLog_real_error (coefficientLogScale i) hL hU
  rw [coefficientLogRounded_value] at h
  have hk' : |(coefficientLogScale i : ℝ)| ≤ 4 := by exact_mod_cast hk
  apply h.trans_le
  calc
    _ ≤ 5 * ((964 : ℝ) / 10 ^ 120 + 120 / 10 ^ 60) := by gcongr; linarith
    _ ≤ _ := by norm_num

end PiIrrationality

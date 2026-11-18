import Tengoku
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.Positivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

namespace SevenEighths.Endpoint

noncomputable section

def denominator (y : ℝ) : ℝ := (37 + 34 * y) / 18

def primeWeight (y : ℝ) : ℝ := (7 + 18 * y + 8 * y ^ 2) / 9

def balanceDenominator (δ y : ℝ) : ℝ :=
  (5 / 6 - δ) * denominator y + δ * primeWeight y

def certificateWeight (y : ℝ) : ℝ := 51 + 41 * y

def balancedCutoff (δ y : ℝ) : ℝ :=
  1 + δ * primeWeight y / (2 * balanceDenominator δ y)

def balancedRowCount (δ y : ℝ) : ℝ :=
  1 - 5 / 6 + (5 / 6 - δ) * balancedCutoff δ y

def balancedExponent (δ y : ℝ) : ℝ :=
  -(1 / 48) + (2 / 3) * δ + δ * (1 / 2 - y) / 6 -
    (13 / 16) * (1 - balancedRowCount δ y)

/--
@isnad1 id=and.2h1v.s6.0122cfe8d77a from=translated src=- shape=25808fcc vocab=32099c93
-/
theorem denominator_bounds {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    7 / 9 ≤ denominator y ∧ denominator y ≤ 3 := by
  dsimp [denominator]
  constructor <;> linarith

/--
@isnad1 id=and.2h1v.s6.c575ad5b0394 from=translated src=- shape=25808fcc vocab=d03a84d2
-/
theorem primeWeight_bounds {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    7 / 9 ≤ primeWeight y ∧ primeWeight y ≤ 2 := by
  have hs := sq_nonneg y
  have ht := mul_nonneg hy0 (sub_nonneg.mpr hy1)
  dsimp [primeWeight]
  constructor <;> nlinarith

/--
@isnad1 id=and.4h2v.s7.d5cdab7fd649 from=translated src=- shape=122359de vocab=66c4ae14
-/
theorem balanceDenominator_bounds {δ y : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    35 / 54 ≤ balanceDenominator δ y ∧ balanceDenominator δ y ≤ 5 / 2 := by
  obtain ⟨hd0, hd1⟩ := denominator_bounds hy0 hy1
  obtain ⟨hp0, hp1⟩ := primeWeight_bounds hy0 hy1
  have ha : 0 ≤ 5 / 6 - δ := sub_nonneg.mpr hδ1
  have hl1 := mul_le_mul_of_nonneg_left hd0 ha
  have hl2 := mul_le_mul_of_nonneg_left hp0 hδ0
  have hu1 := mul_le_mul_of_nonneg_left hd1 ha
  have hu2 := mul_le_mul_of_nonneg_left (le_trans hp1 (by norm_num : (2 : ℝ) ≤ 3)) hδ0
  dsimp [balanceDenominator]
  constructor <;> nlinarith

/--
@isnad1 id=eq.1h2v.s8.fa7185c2708a from=translated src=- shape=687180df vocab=e5fbd399
-/
theorem endpoint_identity (δ y : ℝ) (hJ : balanceDenominator δ y ≠ 0) :
    10368 * certificateWeight y * balanceDenominator δ y * (-balancedExponent δ y) =
      (3 + 5 * y) * ((4 * certificateWeight y * δ - 79) ^ 2 + 49) +
      4 * y * (4 * certificateWeight y * δ *
        ((1 + 3 * y) * (15 + 32 * y) * δ + 9 - 13 * y) + 265 + 3485 * y) := by
  unfold balancedExponent balancedRowCount balancedCutoff
  field_simp
  simp only [balanceDenominator, denominator, primeWeight, certificateWeight]
  ring

/--
@isnad1 id=le.4h2v.s6.ee5df9e9137e from=translated src=- shape=01aaf6bc vocab=95e9a47c
-/
theorem balanced_endpoint_margin {δ y : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    (49 : ℝ) / 440640 ≤ -balancedExponent δ y := by
  obtain ⟨hJlo, hJhi⟩ := balanceDenominator_bounds hδ0 hδ1 hy0 hy1
  have hJpos : 0 < balanceDenominator δ y := by linarith
  have hvpos : 0 < certificateWeight y := by dsimp [certificateWeight]; linarith
  have hinner : 0 ≤ (1 + 3 * y) * (15 + 32 * y) * δ + 9 - 13 * y := by
    have hp : 0 ≤ (1 + 3 * y) * (15 + 32 * y) * δ := by positivity
    linarith
  have hrest : 0 ≤ 4 * y * (4 * certificateWeight y * δ *
      ((1 + 3 * y) * (15 + 32 * y) * δ + 9 - 13 * y) + 265 + 3485 * y) := by
    positivity
  have hsq : 0 ≤ (3 + 5 * y) * (4 * certificateWeight y * δ - 79) ^ 2 := by
    positivity
  have hid := endpoint_identity δ y (ne_of_gt hJpos)
  have hcert : 49 * (3 + 5 * y) ≤
      10368 * certificateWeight y * balanceDenominator δ y * (-balancedExponent δ y) := by
    nlinarith only [hid, hrest, hsq]
  have hvhi : certificateWeight y ≤ 17 * (3 + 5 * y) := by
    dsimp [certificateWeight]
    linarith
  have hscaled : 49 * certificateWeight y ≤
      176256 * certificateWeight y * balanceDenominator δ y * (-balancedExponent δ y) := by
    nlinarith only [hcert, hvhi]
  have hcancel : 49 ≤ 176256 * balanceDenominator δ y * (-balancedExponent δ y) := by
    nlinarith only [hscaled, hvpos]
  have hEpos : 0 < -balancedExponent δ y := by
    by_contra hn
    have hn' : -balancedExponent δ y ≤ 0 := le_of_not_gt hn
    have hp := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hJpos) hn'
    nlinarith only [hcancel, hp]
  have hup := mul_le_mul_of_nonneg_right hJhi (le_of_lt hEpos)
  nlinarith only [hcancel, hup]

/--
@isnad1 id=lt.4h2v.s6.653030e2d14c from=translated src=- shape=b678ed45 vocab=36e524d6
-/
theorem balanced_endpoint_strict {δ y : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    balancedExponent δ y < -(1 / 10000 : ℝ) := by
  have h := balanced_endpoint_margin hδ0 hδ1 hy0 hy1
  norm_num at *
  linarith

end

end SevenEighths.Endpoint

end OAI

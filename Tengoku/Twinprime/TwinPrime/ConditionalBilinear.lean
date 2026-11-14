import Tengoku.Twinprime.TwinPrime.Analytic.Decomposition
import Tengoku.Twinprime.TwinPrime.Analytic.Cutoff
import Tengoku.Twinprime.TwinPrime.Analytic.MixedCorrelation
import Tengoku.Twinprime.TwinPrime.Analytic.TypeICorrection
import Tengoku.Twinprime.TwinPrime.Analytic.MertensReduction
import Tengoku.Twinprime.TwinPrime.Analytic.PrimeToMertens
import Tengoku.Twinprime.TwinPrime.HardyLittlewood

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Conditional analytic endpoints

All estimates remain explicit hypotheses. The theorem below does not prove the
signed bilinear estimate, the mixed-correlation estimate, or the Type I estimate.
The cutoffs may vary with `X`; their finite support conditions are checked at
every sufficiently large input. Only the signed estimate is required cofinally.
The sublinear prime-power error is proved in `Correlation.lean`; the final
three-estimate version below discharges that obligation automatically.
The most refined endpoint also derives the ordinary Mertens estimate from
the named BV hypothesis. BV and the signed bilinear bound remain inputs.
-/

noncomputable section

namespace TwinPrime

open Analytic Filter

/-- The numerical budget in PLAN.md, Section 7.2.
@isnad1 id=le.5h7v.s7.21c1b5b7ace4 from=translated src=- shape=4d3b6fc1 vocab=b59c7e53
-/
theorem four_obligation_budget {A K B E W C x : ℝ}
    (hD : W = A + K + B)
    (hA : |A - C * x| ≤ C * x / 8)
    (hK : |K| ≤ C * x / 8)
    (hB : -(C * x) / 2 ≤ B)
    (hE : E ≤ C * x / 8) : C * x / 8 ≤ W - E := by
  have hAlower := (abs_le.mp hA).1
  have hKlower := (abs_le.mp hK).1
  linarith

/-- A positive proportion of the mixed main term surviving the exact signed
decomposition, after proper prime powers are removed, gives infinitely many twins.
This is a conditional theorem with all four analytic obligations visible.
@isnad1 id=twinprim.6h4v.s8.7b6bc123f8dd from=translated src=- shape=c4ad69db vocab=794a47bf
-/
theorem twinPrimeConjecture_of_bilinear_budget
    (U V : ℕ → ℕ) (C : ℝ) (hC : 0 < C) (X₀ : ℕ)
    (hcutoff : ∀ X ≥ X₀, 0 < U X ∧ V X ≤ X)
    (hA : ∀ X ≥ X₀, |mixedCorrelation (U X) X - C * X| ≤ C * X / 8)
    (hK : ∀ X ≥ X₀, |typeICorrection (U X) (V X) X| ≤ C * X / 8)
    (hE : ∀ X ≥ X₀, Epp X ≤ C * X / 8)
    (hB : ∀ Y : ℕ, ∃ X ≥ max Y X₀,
      -(C * X) / 2 ≤ bilinearTerm (U X) (V X) X) : TwinPrimeConjecture := by
  apply twinPrimeConjecture_of_cofinal_W2_gt_Epp
  intro Y
  obtain ⟨X, hX, hBX⟩ := hB (max Y 1)
  have hXX₀ : X₀ ≤ X := le_trans (le_max_right _ _) hX
  have hYX : Y ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXpos : 0 < X := by omega
  have hcut := hcutoff X hXX₀
  have hbudget := four_obligation_budget
    (correlation_decomposition (U X) (V X) X hcut.1 hcut.2)
    (hA X hXX₀) (hK X hXX₀) hBX (hE X hXX₀)
  have hmain : 0 < C * (X : ℝ) / 8 := by positivity
  exact ⟨X, hYX, by linarith⟩

/-- Specialization to the existing, proved positive twin-prime constant.
@isnad1 id=twinprim.5h3v.s8.3de2a5aae970 from=translated src=- shape=4531f0a3 vocab=84dc85c4
-/
theorem twinPrimeConjecture_of_bilinear_budget_twinConstant
    (U V : ℕ → ℕ) (X₀ : ℕ)
    (hcutoff : ∀ X ≥ X₀, 0 < U X ∧ V X ≤ X)
    (hA : ∀ X ≥ X₀,
      |mixedCorrelation (U X) X - (2 * twinPrimeConstant) * X| ≤
        (2 * twinPrimeConstant) * X / 8)
    (hK : ∀ X ≥ X₀, |typeICorrection (U X) (V X) X| ≤
      (2 * twinPrimeConstant) * X / 8)
    (hE : ∀ X ≥ X₀, Epp X ≤ (2 * twinPrimeConstant) * X / 8)
    (hB : ∀ Y : ℕ, ∃ X ≥ max Y X₀,
      -((2 * twinPrimeConstant) * X) / 2 ≤ bilinearTerm (U X) (V X) X) :
    TwinPrimeConjecture :=
  twinPrimeConjecture_of_bilinear_budget U V (2 * twinPrimeConstant)
    (mul_pos (by norm_num) twinPrimeConstant_pos) X₀ hcutoff hA hK hE hB

/-- The prime-power obligation is already discharged by `tendsto_Epp_div`.
The two known analytic estimates and the new signed estimate remain assumptions.
@isnad1 id=twinprim.5h4v.s7.9f17dcc69b3f from=translated src=- shape=fa5356f6 vocab=873b043c
-/
theorem twinPrimeConjecture_of_bilinear_estimates
    (U V : ℕ → ℕ) (C : ℝ) (hC : 0 < C) (X₀ : ℕ)
    (hcutoff : ∀ X ≥ X₀, 0 < U X ∧ V X ≤ X)
    (hA : ∀ X ≥ X₀, |mixedCorrelation (U X) X - C * X| ≤ C * X / 8)
    (hK : ∀ X ≥ X₀, |typeICorrection (U X) (V X) X| ≤ C * X / 8)
    (hB : ∀ Y : ℕ, ∃ X ≥ max Y X₀,
      -(C * X) / 2 ≤ bilinearTerm (U X) (V X) X) : TwinPrimeConjecture := by
  apply twinPrimeConjecture_of_cofinal_W2_linear (c := C / 4) (by positivity)
  intro Y
  obtain ⟨X, hX, hBX⟩ := hB Y
  have hXX₀ : X₀ ≤ X := le_trans (le_max_right _ _) hX
  refine ⟨X, le_trans (le_max_left _ _) hX, ?_⟩
  have hcut := hcutoff X hXX₀
  have hD := correlation_decomposition (U X) (V X) X hcut.1 hcut.2
  have hAlower := (abs_le.mp (hA X hXX₀)).1
  have hKlower := (abs_le.mp (hK X hXX₀)).1
  linarith

/-- The precise primary-route endpoint: fixed fifth-root cutoffs, the existing
twin-prime constant, and only the three as-yet unproved analytic estimates.
@isnad1 id=twinprim.3h1v.s7.0daf0d338390 from=translated src=- shape=8e92c667 vocab=0ba5cb00
-/
theorem twinPrimeConjecture_of_primary_estimates (X₀ : ℕ)
    (hA : ∀ X ≥ X₀,
      |mixedCorrelation (primaryCutoff X) X - (2 * twinPrimeConstant) * X| ≤
        (2 * twinPrimeConstant) * X / 8)
    (hK : ∀ X ≥ X₀, |typeICorrection (primaryCutoff X) (primaryCutoff X) X| ≤
      (2 * twinPrimeConstant) * X / 8)
    (hB : ∀ Y : ℕ, ∃ X ≥ max Y X₀,
      -((2 * twinPrimeConstant) * X) / 2 ≤
        bilinearTerm (primaryCutoff X) (primaryCutoff X) X) : TwinPrimeConjecture := by
  apply twinPrimeConjecture_of_bilinear_estimates primaryCutoff primaryCutoff
    (2 * twinPrimeConstant) (mul_pos (by norm_num) twinPrimeConstant_pos) (max X₀ 1)
  · intro X hX
    have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
    exact ⟨primaryCutoff_pos hX1, primaryCutoff_le hX1⟩
  · intro X hX
    exact hA X (le_trans (le_max_left _ _) hX)
  · intro X hX
    exact hK X (le_trans (le_max_left _ _) hX)
  · intro Y
    obtain ⟨X, hX, hBX⟩ := hB (max Y 1)
    exact ⟨X, by omega, hBX⟩

end TwinPrime

/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
module

public import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.Definitions
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.BlockLocalization
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.DegreeBookkeeping
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.ImportedAnalyticInputs
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.ProductBasisAndAnnuli
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic
import Tengoku.Seed.Combinatorics.Matroid.Init
import Tengoku.Seed.Data.Nat.Factorial.DoubleFactorial
import Tengoku.Seed.Tactic.NormNum.Parity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # ProductAnnulusCircle -/

@[expose] public section

open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Hermite1DimdLEAN

/-!
# ProductAnnulusCircle

Orbitwise circle inequalities lifted to a fixed product annulus.
Scaffolding notes: `ScaffoldingNotes/Circle/product_annulus_circle.md`.
-/

/-- Reverse-triangle comparison for modulus defects. -/
theorem rhoPointwise
    (a u v : ℂ) :
    rho a u ≤ rho a v + ‖u - v‖ := by
  unfold rho
  let A : ℝ := ‖a + u‖ - ‖a‖
  let B : ℝ := ‖a + v‖ - ‖a‖
  have hAB : |A - B| ≤ ‖u - v‖ := by
    calc
      |A - B| = |‖a + u‖ - ‖a + v‖| := by simp [A, B]
      _ ≤ ‖(a + u) - (a + v)‖ := abs_norm_sub_norm_le (a + u) (a + v)
      _ = ‖u - v‖ := by
        simp_all
  calc
    |A| = |(A - B) + B| := by ring_nf
    _ ≤ |A - B| + |B| := abs_add_le _ _
    _ ≤ ‖u - v‖ + |B| := by gcongr
    _ = rho a v + ‖u - v‖ := by simp [rho, B, add_comm]

/-- Quadratic defect comparison derived from `rhoPointwise`. -/
theorem rhoPointwiseSq
    (a u v : ℂ) :
    rho a u ^ 2 ≤ 2 * rho a v ^ 2 + 2 * ‖u - v‖ ^ 2 := by
  have h := rhoPointwise a u v
  have hsq : (rho a u) ^ 2 ≤ (rho a v + ‖u - v‖) ^ 2 := by
    have hnonneg : 0 ≤ rho a u := abs_nonneg _
    have hneg0 : -(rho a v + ‖u - v‖) ≤ 0 := by
      nlinarith [abs_nonneg (rho a v), norm_nonneg (u - v)]
    have hneg : -(rho a v + ‖u - v‖) ≤ rho a u := le_trans hneg0 hnonneg
    exact sq_le_sq' hneg h
  have hsum : (rho a v + ‖u - v‖) ^ 2 ≤ 2 * rho a v ^ 2 + 2 * ‖u - v‖ ^ 2 := by
    nlinarith [two_mul_le_add_sq (rho a v) ‖u - v‖]
  exact le_trans hsq hsum

/-- Orbitwise coefficient grouped by total degree. -/
private def orbitCoeff
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ)
    (G : FiniteHermiteSum d) (z : CSpace d) (n : ℕ) : ℂ :=
  ∑ α ∈ (localPart j M G).support.filter (fun α => totalDegree α = n),
    (localPart j M G).coeff α * PhiKappaAlpha κ α z

/-- Phase-corrected local orbit on a fixed product annulus. -/
private def localOrbit
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ)
    (G : FiniteHermiteSum d) (z : CSpace d) (t : Circle) : ℂ :=
  (fourier (totalDegree κ : ℤ) t : ℂ) *
    evalHermiteSum κ (localPart j M G)
      (fun q => (fourier (1 : ℤ) t : ℂ) * z q)

end Hermite1DimdLEAN

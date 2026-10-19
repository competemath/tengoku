/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
module

public import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.Definitions
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite.MissingMathlib
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.ImportedAnalyticInputs
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.ProductBasisAndAnnuli
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermitek.TrueLevelBasis
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic
import Tengoku.Seed.Combinatorics.Matroid.Init
import Tengoku.Seed.Data.Nat.Factorial.DoubleFactorial
import Tengoku.Seed.Tactic.NormNum.Parity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BlockLocalization -/

@[expose] public section

open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Hermite1DimdLEAN

/-!
# BlockLocalization

Square-block support decomposition and leakage.
Scaffolding notes: `ScaffoldingNotes/Blocks/block_localization.md`.
-/

/-- Explicit local and far support sets relative to an annulus and width. -/
theorem explicitLocalAndFarSupport
    {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    Disjoint (localCoeffSet j M G) (farCoeffSet j M G) ∧
      localCoeffSet j M G ∪ farCoeffSet j M G = G.support ∧
      (localPart j M G).support = localCoeffSet j M G ∧
      (remainderPart j M G).support = farCoeffSet j M G := by
  /-
  Scaffolding guidance:
  later files need the explicit finite sets, not an opaque decomposition lemma.
  This is where regrouping by total degree starts.
  -/
  classical
  have hdisj : Disjoint (localCoeffSet j M G) (farCoeffSet j M G) := by
    refine Finset.disjoint_left.mpr fun α hlocal hfar => ?_
    exact absurd (Finset.mem_filter.mp hfar).2 (not_lt_of_ge (Finset.mem_filter.mp hlocal).2)
  have hunion : localCoeffSet j M G ∪ farCoeffSet j M G = G.support := by
    ext α
    simp only [localCoeffSet, farCoeffSet, mem_union, mem_filter]
    constructor
    · rintro (⟨hsupp, _⟩ | ⟨hsupp, _⟩) <;> exact hsupp
    · intro hsupp
      by_cases hlocal : blockDistance j (blockIndexMulti α) ≤ M
      · exact Or.inl ⟨hsupp, hlocal⟩
      · exact Or.inr ⟨hsupp, Nat.lt_of_not_ge hlocal⟩
  have hlocal_support : (localPart j M G).support = localCoeffSet j M G := by
    ext α
    simp [FiniteHermiteSum.support, localPart, localCoeffSet, Finsupp.mem_support_iff, and_comm]
  have hfar_support : (remainderPart j M G).support = farCoeffSet j M G := by
    ext α
    simp [FiniteHermiteSum.support, remainderPart, farCoeffSet, Finsupp.mem_support_iff, and_comm]
  exact ⟨hdisj, hunion, hlocal_support, hfar_support⟩

/-- The shell finset `cube \ inner` carrying the block-distance-`r` offsets. -/
private def shellFinset (d r : ℕ) : Finset (Fin d → ℤ) :=
  (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) (r : ℤ))) \
    Fintype.piFinset (fun _ : Fin d => Finset.Icc (-((r - 1 : ℕ) : ℤ)) (((r - 1 : ℕ) : ℤ)))

/-- Crude shell-count helper for sup-norm block shells. -/
theorem shellCountingFormula
    (d r : ℕ) :
    (2 * r + 1) ^ d - (2 * r - 1) ^ d ≤ (2 * r + 1) ^ d := by
  /-
  Scaffolding guidance:
  replace this placeholder inequality with exact shell-count formulas on
  `ℤ^d` once the finite shell enumerators are fixed.
  -/
  exact Nat.sub_le _ _

private lemma summable_exp_neg_mul_sq {a : ℝ} (ha : 0 < a) :
    Summable (fun r : ℕ => Real.exp (-a * (r : ℝ) ^ 2)) := by
  refine Real.summable_exp_nat_mul_of_ge ?_ ?_
  · linarith
  · intro i
    have hreal : (i : ℝ) ≤ (i : ℝ) * (i : ℝ) := by exact_mod_cast Nat.le_mul_self i
    simpa [pow_two] using hreal

private lemma polynomialGaussianTailMajorant_summable
    {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Summable (fun r : ℕ => (1 + (r : ℝ) ^ k) * Real.exp (-a * (r : ℝ) ^ 2)) := by
  obtain ⟨C, hCpos, hbound⟩ :=
    HermiteLEAN.polynomial_times_gaussian_le_gaussian ha k
  exact Summable.of_nonneg_of_le
      (f := fun r : ℕ => C * Real.exp (-(a / 2) * (r : ℝ) ^ 2))
      (g := fun r : ℕ => (1 + (r : ℝ) ^ k) * Real.exp (-a * (r : ℝ) ^ 2))
      (fun r => by positivity)
      (fun r => hbound (r : ℝ) (by positivity))
      ((summable_exp_neg_mul_sq (by linarith)).mul_left C)

/-- Gaussian tails with polynomial weights are summable. -/
theorem polynomialGaussianSeriesSummable
    (m : ℕ) (c : ℝ) (hc : 0 < c) :
    Summable (fun r : ℕ => (r : ℝ) ^ m * Real.exp (-c * r ^ 2)) :=
  Summable.of_nonneg_of_le
    (f := fun r : ℕ => (1 + (r : ℝ) ^ m) * Real.exp (-c * (r : ℝ) ^ 2))
    (g := fun r : ℕ => (r : ℝ) ^ m * Real.exp (-c * (r : ℝ) ^ 2))
    (fun r => by positivity)
    (fun r => mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    (polynomialGaussianTailMajorant_summable hc m)

end Hermite1DimdLEAN

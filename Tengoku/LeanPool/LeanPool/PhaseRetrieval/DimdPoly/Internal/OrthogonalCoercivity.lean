/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
module

public import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Definitions
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.CoefficientLimitRigidity
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.FiniteBaseAnnulusEstimate
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.ImportedAnalyticInputs
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermitek.TrueLevelBasis
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.ProductAnnulusLocalization
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.TensorBasis
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic
import Tengoku.Seed.Combinatorics.Matroid.Init
import Tengoku.Seed.Data.Nat.Factorial.DoubleFactorial
import Tengoku.Seed.MeasureTheory.Function.LpSeminorm.LpNorm
import Tengoku.Seed.Tactic.NormNum.Parity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # OrthogonalCoercivity -/

@[expose] public section

open MeasureTheory Complex
open scoped BigOperators

noncomputable section

namespace DimdPolyLEAN

/-!
# OrthogonalCoercivity

Terminal finite assembly scaffold. This file should expose one coercivity
theorem and no new analytic content.
-/

section

variable {d : Nat} (kappa : MultiIndex d)

local notation "Pk" => Pkappa d kappa

/-- `coeffPk`: coeff Pk. -/
def coeffPk (H : Pk) (alpha : Idx d) : ℂ := coeffPkappa H alpha

/-- `OrthogonalToPk`: Orthogonal To Pk. -/
def OrthogonalToPk (F G : Pk) : Prop := orthogonalToPk F G

/-- `defectPk`: defect Pk. -/
def defectPk (F G : Pk) : ℝ := defect F G

/-- `lowAnnulusMassPk`: low Annulus Mass Pk. -/
def lowAnnulusMassPk (J : Nat) (H : Pk) : ℝ := lowAnnulusMass J (ofPkappa kappa H)

/-- `highAnnulusMassPk`: high Annulus Mass Pk. -/
def highAnnulusMassPk (J : Nat) (H : Pk) : ℝ := highAnnulusMass J (ofPkappa kappa H)

private def defectFunctionPkappa_wip
    {d : Nat} (kappa : MultiIndex d) (F G : Pkappa d kappa) :
    Cd d → ℝ :=
  fun z => |‖evalPkappa kappa (F + G) z‖ - ‖evalPkappa kappa F z‖|

end

end DimdPolyLEAN

/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBallWeak
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBridge
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.PoincareSobolevL1Ball
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareConstantFinite
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareConstantPos
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBallFaithfulL1
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.W1p.Basic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.GradientNorm
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.NormTriangle
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.BallMemLp
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.LpConvergence
public import Tengoku

/-!
# The scale-explicit Sobolev–Poincaré inequalities on Euclidean balls

This file records the three clauses of the ball lemma together with one
constant chosen independently of the ball and the functions.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic

namespace CKN

noncomputable section

/-- A single absolute constant for all three clauses of the ball lemma. -/
noncomputable def sobolevPoincareFaithfulC5 : ℝ :=
  1 + sobolevPoincareL6Constant.toReal +
    (2 * sobolevPoincareL6Constant +
      2 * sobolevPoincareBallFullConstant).toReal +
    Real.sqrt 3 * poincareSobolevL1Constant.toReal *
      (Real.pi * 4 / 3) ^ (1 / 3 : ℝ)

/-- The constant in the existing mean-zero L⁶ estimate is nonnegative. -/
theorem sobolevPoincareL6Constant_nonneg :
    0 ≤ sobolevPoincareL6Constant.toReal := ENNReal.toReal_nonneg

/-- `C₅` is positive. -/
theorem sobolevPoincareFaithfulC5_pos : 0 < sobolevPoincareFaithfulC5 := by
  dsimp [sobolevPoincareFaithfulC5]
  positivity

end
end CKN

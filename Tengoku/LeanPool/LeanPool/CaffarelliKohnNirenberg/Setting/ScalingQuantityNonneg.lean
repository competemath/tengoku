/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Statements.Theta
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Statements.Gamma
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Statements.Lambda

/-!
# Scaling Quantity Nonneg

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- The velocity energy quantity α is nonnegative.
@isnad1 id=le.1h3v.s5.c624219dc930 from=translated src=- shape=cc645bb2 vocab=95e8c7f9
-/
theorem alpha_nonneg (u : ParabolicPoint → Vec3) (z : ParabolicPoint)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ alpha u z r := by
  unfold alpha
  refine Real.rpow_nonneg ?_ (1 / 2 : ℝ)
  refine mul_nonneg (inv_nonneg.mpr hr) ?_
  exact ENNReal.toReal_nonneg

/-- The gradient quantity β is nonnegative.
@isnad1 id=le.1h4v.s5.f0c32ed557da from=translated src=- shape=e1fc98b6 vocab=d536754e
-/
theorem beta_nonneg (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ beta u Du z r := by
  unfold beta
  refine Real.rpow_nonneg ?_ (1 / 2 : ℝ)
  refine mul_nonneg (inv_nonneg.mpr hr) ?_
  exact ENNReal.toReal_nonneg

/-- The velocity cubic quantity γ is nonnegative.
@isnad1 id=le.1h3v.s5.2d030fd8acf5 from=translated src=- shape=cc645bb2 vocab=40e9f79d
-/
theorem gamma_nonneg (u : ParabolicPoint → Vec3) (z : ParabolicPoint)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ gamma u z r := by
  unfold gamma
  refine Real.rpow_nonneg ?_ (1 / 3 : ℝ)
  refine mul_nonneg (Real.rpow_nonneg hr (-2 : ℝ)) ?_
  exact ENNReal.toReal_nonneg

/-- The force quantity λ is nonnegative.
@isnad1 id=le.1h4v.s5.9d6dd91be7a4 from=translated src=- shape=a842effd vocab=22fcacca
-/
theorem lambda_nonneg (q : ℝ) (f : ParabolicPoint → Vec3) (z : ParabolicPoint)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ lambda q f z r := by
  unfold lambda
  refine mul_nonneg (Real.rpow_nonneg hr (3 - 5 / q)) ?_
  refine Real.rpow_nonneg ENNReal.toReal_nonneg (1 / q : ℝ)

end CKN

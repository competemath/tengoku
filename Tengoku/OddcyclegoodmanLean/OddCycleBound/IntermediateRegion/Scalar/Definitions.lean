import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Set

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

noncomputable def leadingEigenvalueRadius (q : Real) : Real :=
  (Real.sqrt (q ^ 2 + 4 * q) - q) / 2

structure AdmissibleParams where
  q : Real
  alpha : Real
  m : Nat
  q_gt_third : 1 / 3 < q
  q_lt_half : q < 1 / 2
  alpha_gt_q : q < alpha
  alpha_le_radius : alpha <= leadingEigenvalueRadius q
  m_odd : Odd m
  m_ge_nine : 9 <= m

namespace AdmissibleParams

variable (P : AdmissibleParams)

def p : Real := 1 - P.q
def d : Real := P.alpha - P.q
def e : Real := 1 - 2 * P.alpha

noncomputable def L : Real :=
  Real.sqrt (P.p * P.q - P.alpha ^ 2)

noncomputable def f : Real := P.alpha - P.L

noncomputable def k (lambda : Real) : Real :=
  (P.p ^ (P.m - 1) - lambda ^ (P.m - 1)) / (P.p + lambda)

noncomputable def A : Real :=
  2 * P.L ^ (P.m - 2) + P.m * P.k P.alpha

noncomputable def B : Real :=
  2 * P.L ^ (P.m - 2) + P.m * P.k P.L

noncomputable def R : Real :=
  P.alpha ^ P.m + P.L ^ P.m - P.p * P.q ^ (P.m - 1)

noncomputable def C : Real :=
  P.B * P.f * Real.sqrt (2 * P.alpha) * P.e ^ 2 /
    (4 * P.alpha ^ 2)

noncomputable def xi : Real :=
  4 * P.alpha ^ 2 * P.d / P.e ^ 2

noncomputable def rho : Real :=
  (P.A / P.B) *
    (Real.sqrt P.alpha / (2 * Real.sqrt 2 * P.f))

def tau : Real := P.q / P.alpha

def kappa : Real := P.d / P.e

end AdmissibleParams

noncomputable def envelopeObjective (xi rho v : Real) : Real :=
  rho * v ^ 2 + max (xi - v + v ^ 2) 0

noncomputable def psi (xi rho : Real) : Real :=
  sInf (envelopeObjective xi rho '' Icc (0 : Real) 1)

noncomputable def envelopeDual (xi rho lambda : Real) : Real :=
  lambda * xi - lambda ^ 2 / (4 * (rho + lambda))

end OddCycleBound.IntermediateRegion.Scalar

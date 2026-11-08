module
public import Tengoku.Seed.Analysis.Complex.Exponential
public import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Basic
public import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Basic
public import Tengoku.Seed.MeasureTheory.Integral.IntegrableOn
import Tengoku.SpherePackingExt.SpherePacking.ForMathlib.IntegrablePowMulExp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Laplace Kernel Tools

This file collects elementary estimates used in the Laplace-analysis part of the proof.

## Main statements
* `norm_kernelExp`
* `abs_re_sub_le_norm`
* `re_ge_of_mem_ball`
* `integrableOn_pow_mul_exp_neg_mul_Ioi_one`
-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceFourierCont.LaplaceBKernelAnalytic

noncomputable section

open scoped Topology

open Complex Filter MeasureTheory Real Set

end

end SpherePacking.Dim24.LaplaceTmp.LaplaceFourierCont.LaplaceBKernelAnalytic

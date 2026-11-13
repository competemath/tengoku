import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.CStarAlgebra.TracialPositivePowers
import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.CStarAlgebra.GramNormPerturbation
import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.WeightedSquareOptimization
import Tengoku.Nlalib.NLAlib.ForMathlib.MeasureTheory.PositiveMomentAffine

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Actual rooted tracial Gram moments are stable under norm perturbations

Positive trace-power monotonicity, the positive-square Young inequality,
and scalar Lp on the actual spectrum measure prove the genuine native Gram
moment estimate. Noncommutative Minkowski is derived in the particular
norm-perturbation form needed for the mean-uniform free-resolvent estimate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ComplexOrder ContinuousFunctionalCalculus

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end

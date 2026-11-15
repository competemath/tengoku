import Tengoku.Seed.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Tengoku.Seed.NumberTheory.NumberField.Discriminant.Defs
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open NumberField NumberField.mixedEmbedding
open scoped nonZeroDivisors

noncomputable section

namespace Deep.Analytic

variable (K : Type*) [Field K] [NumberField K]

open Classical in

def euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (mixedEmbedding.idealLattice K I) (euclidean.toMixed K).toLinearMap

end Deep.Analytic

namespace M4aP2

variable (K : Type*) [Field K] [NumberField K]

def heckeScale (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ :=
  (|(discr K : ℝ)| * (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ 2)
    ^ (-(1 : ℝ) / (Module.finrank ℚ K : ℝ))

end M4aP2

end

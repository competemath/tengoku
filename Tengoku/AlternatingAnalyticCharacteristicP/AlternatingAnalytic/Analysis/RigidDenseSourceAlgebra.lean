import Tengoku.Seed.RingTheory.AlgebraicIndependent.Basic
import Tengoku.Seed.RingTheory.MvPolynomial.Homogeneous
import Tengoku.Seed.LinearAlgebra.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coefficient comparison for rigid sources

The algebraic core of Lemma H.5: if an `L`-linear endomorphism of `L^I` has columns in `K^I + K a`
and sends `a` into `K^I + K a`, then comparing homogeneous degrees in the independent `a_i`
shows it is a scalar in `K`. Similarly a functional with values in `K` on the `e_i` and on `a`
is zero.
-/

noncomputable section
open scoped BigOperators
namespace AlternatingAnalytic.RigidDenseSource
open MvPolynomial

variable {K L I : Type*} [Field K] [Field L] [Algebra K L] [Fintype I]

private def linearPolynomial (c : I → K) : MvPolynomial I K :=
  ∑ j, C (c j) * X j

end AlternatingAnalytic.RigidDenseSource

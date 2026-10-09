module
public import Tengoku.Causalean.Causalean.Mathlib.LinearAlgebra.Tensor.SymmetricPencil.Basic

/-!
# Conditioning of compressed lifted factors

This module records how an orthonormal basis of the lifted column space preserves the signal
singular values.  It then derives explicit lower and upper bounds for the contracted matrices
which form the denominator and numerators of a tensor pencil.
-/

@[expose] public section

namespace Causalean.Mathlib.LinearAlgebra.Tensor.SymmetricPencil

open scoped BigOperators

/-- A finite matrix has orthonormal columns when its transpose times itself is the identity. With [its explicit inputs](hyp:U), [the defined object](goal) is [given by the displayed formula](step:1). -/
def OrthonormalColumns {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι κ ℝ) : Prop :=
  U.transpose * U = 1

/-- Two finite matrices have the same column space when their associated Euclidean linear maps
have equal ranges. With [its explicit inputs](hyp:U,V), [the defined object](goal) is [given by the displayed formula](step:1). -/
def SameColumnSpace {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (U V : Matrix ι κ ℝ) : Prop :=
  U.toEuclideanLin.range = V.toEuclideanLin.range

/-- A positive lower bound for the last column singular value implies full column rank. Under [the listed assumptions](hyp:hsigma,hsv), [the stated conclusion follows](goal). -/
-- Proof route: positivity rules out
-- `singularValues_eq_zero_iff_le_finrank_range` at the last domain index.  Hence the range has
-- full domain finrank, so rank--nullity makes the kernel trivial.  (The existing expansion lemma
-- itself assumes injectivity, so it cannot be used contrapositively here.)
theorem injective_of_pos_le_leastColumnSingularValue {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (A : Matrix ι κ ℝ) {sigma : ℝ} (hsigma : 0 < sigma)
    (hsv : sigma ≤ leastColumnSingularValue A) :
    Function.Injective A.toEuclideanLin := by
  let T := A.toEuclideanLin
  have hpos : 0 < T.singularValues (Fintype.card κ - 1) :=
    lt_of_lt_of_le hsigma hsv
  have hrank_not : ¬ Module.finrank ℝ T.range ≤ Fintype.card κ - 1 := by
    intro hrank
    have hz := T.singularValues_eq_zero_iff_le_finrank_range.mpr hrank
    rw [hz] at hpos
    exact lt_irrefl 0 hpos
  have hcard_le : Fintype.card κ ≤ Module.finrank ℝ T.range := by omega
  have hrank_le : Module.finrank ℝ T.range ≤ Fintype.card κ := by
    simpa [T, finrank_euclideanSpace] using T.finrank_range_le
  have hker : Module.finrank ℝ T.ker = 0 := by
    have hrank_null : Module.finrank ℝ T.range + Module.finrank ℝ T.ker =
        Fintype.card κ := by
      simpa [finrank_euclideanSpace] using T.finrank_range_add_finrank_ker
    omega
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.finrank_eq_zero.mp hker

end Causalean.Mathlib.LinearAlgebra.Tensor.SymmetricPencil

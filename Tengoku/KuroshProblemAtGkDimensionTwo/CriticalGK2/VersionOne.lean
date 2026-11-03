import Tengoku.KuroshProblemAtGkDimensionTwo.CriticalGK2.Unitization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Algebraicity of matrix unitizations

Over an arbitrary field, nilpotence of every positive-order matrix over a
non-unital algebra implies algebraicity of every positive-order matrix over
its unitization. The theorems use Mathlib's unitization and matrix algebra.
-/

namespace CriticalGK2.VersionOne

variable {K A : Type*} [Field K] [NonUnitalRing A] [Module K A]
  [IsScalarTower K A A] [SMulCommClass K A A]

/-- Algebraicity of matrix unitizations in every positive order.
@isnad1 id=isalgebr.2h3v.s8.22ab3e0fe82a from=translated src=- shape=42419b8a vocab=367ffbd1
-/
theorem capstone
    (matrixNil : ∀ r : ℕ, 0 < r → ∀ M : Matrix (Fin r) (Fin r) A,
      ∃ e : ℕ, CriticalGK2.positivePower M e = 0) :
    ∀ r : ℕ, 0 < r →
      Algebra.IsAlgebraic K (Matrix (Fin r) (Fin r) (Unitization K A)) := by
  intro r hr
  exact CriticalGK2.unitization_matrix_algebraic (matrixNil r hr)

/-- Every matrix over the unitization is algebraic when all positive-order
matrices over the underlying algebra are nilpotent.
@isnad1 id=isalgebr.2h4v.s9.1c2d8bbea1da from=translated src=- shape=6cdc97b2 vocab=a0164db4
-/
theorem capstone_pointwise
    (matrixNil : ∀ r : ℕ, 0 < r → ∀ M : Matrix (Fin r) (Fin r) A,
      ∃ e : ℕ, CriticalGK2.positivePower M e = 0)
    (r : ℕ) (hr : 0 < r)
    (Y : Matrix (Fin r) (Fin r) (Unitization K A)) : IsAlgebraic K Y := by
  exact CriticalGK2.unitization_matrix_isAlgebraic (matrixNil r hr) Y

end CriticalGK2.VersionOne

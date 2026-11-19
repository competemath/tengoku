import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.RootDegree
import Tengoku.Seed.FieldTheory.RatFunc.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

/-!
# The degree-m root interface for Lemma 6.46

Absolute irreducibility of

    Y^m - f(X)

implies that a root has degree `m` over `F_q(X)`.  The existing
`Lemma646.RootDegree` file already proves that such a degree-m root makes
`1,Y,...,Y^(m-1)` linearly independent.

We package the required data here.  `KummerGaussBridge` constructs it
from polynomial irreducibility, and `AbsoluteIrreducibility` derives
the normalized irreducibility hypothesis used in the complete proof.
-/

variable {F : Type*} [Field F]

structure KummerRootData (m : ℕ) (f : Polynomial F) where
  L : Type*
  instFieldL : Field L
  instAlgebra : Algebra (RatFunc F) L
  Y : L
  minpoly_degree : (minpoly (RatFunc F) Y).natDegree = m
  pow_eq :
    Y ^ m =
      algebraMap (RatFunc F) L
        ((algebraMap (Polynomial F) (RatFunc F)) f)

attribute [instance] KummerRootData.instFieldL
attribute [instance] KummerRootData.instAlgebra

/--
@isnad1 id=eq.1h6v.s9.e8176050804b from=translated src=- shape=03ec1aa0 vocab=f68b60be
-/
theorem KummerRootData.coefficients_zero
    {m : ℕ} {f : Polynomial F}
    (K : KummerRootData m f)
    (a : Fin m → RatFunc F)
    (hrel :
      ∑ i : Fin m,
        algebraMap (RatFunc F) K.L (a i) * K.Y ^ (i : ℕ) = 0) :
    ∀ i, a i = 0 := by
  exact coefficients_zero_of_relation_of_minpoly_degree
    K.Y m K.minpoly_degree a hrel

end LN97
end MagicSquares

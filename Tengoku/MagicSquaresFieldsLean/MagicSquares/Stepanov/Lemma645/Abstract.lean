import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma645.Sets
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

/-!
# A compact interface for LN97 Lemma 6.45

The proof of Theorem 6.53 only uses two numerical conclusions of 6.45:

    N = |T0| + m|T1|,
    |T0| + |T1| + |T2| = q.

We package these as a numerical interface.  `PowerFibers` proves the
group-theoretic fiber count for `y ↦ y^m`; `Complete` proves the field
partition and constructs this interface from the actual solution set.
-/

/-- Numerical output of Lemma 6.45.-/
structure Lemma645Counts where
  q : ℕ
  m : ℕ
  N : ℕ
  t0 : ℕ
  t1 : ℕ
  t2 : ℕ
  solutions : N = t0 + m * t1
  partition : t0 + t1 + t2 = q

/-- The concrete counts attached to the finite sets from 6.45.-/
noncomputable def concrete645Counts
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (m N : ℕ) (f : Polynomial F)
    (hsol : N = (stepanovT0 f).card + m * (stepanovT1 m f).card)
    (hpart : (stepanovT0 f).card + (stepanovT1 m f).card +
      (stepanovT2 m f).card = Fintype.card F) :
    Lemma645Counts :=
  { q := Fintype.card F
    m := m
    N := N
    t0 := (stepanovT0 f).card
    t1 := (stepanovT1 m f).card
    t2 := (stepanovT2 m f).card
    solutions := hsol
    partition := hpart }

end LN97
end MagicSquares

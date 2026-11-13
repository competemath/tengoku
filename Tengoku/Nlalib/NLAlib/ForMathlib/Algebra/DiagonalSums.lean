import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Piecewise

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Removing the diagonal of a finite double sum

Source: the finite contraction calculation in operator manuscript
`sh:count-second`; supports `sparse-ose`.
-/

namespace NLAlib

/-- The off-diagonal double sum equals the full double sum minus its diagonal.
Source: finite sum decomposition in manuscript `sh:count-second`;
supports `sparse-ose`.
@isnad1 id=eq.0h3v.s6.0e69937b1f51 from=translated src=- shape=1c352a6d vocab=3073a310
-/
theorem sum_sum_ite_ne_eq_sub_diag {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup R] (f : ι → ι → R) :
    (∑ i, ∑ j, if i = j then 0 else f i j) =
      (∑ i, ∑ j, f i j) - ∑ i, f i i := by
  have hpoint (i j : ι) : (if i = j then 0 else f i j) =
      f i j - if i = j then f i j else 0 := by split_ifs <;> simp
  simp_rw [hpoint, Finset.sum_sub_distrib]
  simp

end NLAlib

module
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Basic

/-!
# Counting coordinate directions

A list of coordinate directions of length `m` determines a multiindex of total
degree `m`. This translates between sequence and multiindex Hölder conventions.
-/

@[expose] public section

open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- The multiplicity of coordinate `i` in a sequence of coordinate directions. -/
def coordCount {d m : ℕ} (f : Fin m → Fin d) (i : Fin d) : ℕ :=
  (Finset.univ.filter (fun k => f k = i)).card

/-- For [a sequence of m coordinate directions](hyp:f), [the numbers of times each coordinate
occurs in the sequence add up to m](goal).
@isnad1 id=eq.0h3v.s4.870247a45e30 from=translated src=- shape=476104a2 vocab=b12c22e7
-/
theorem sum_coordCount {d m : ℕ} (f : Fin m → Fin d) :
    (∑ i : Fin d, coordCount f i) = m := by
  classical
  simpa only [coordCount, Finset.sum_card_fiberwise_eq_card_filter,
    Finset.mem_univ, true_and, Finset.filter_true, Finset.card_fin]
    using (Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin m)) (Finset.univ : Finset (Fin d)) f)

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

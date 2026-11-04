import Tengoku.ErdosLean.ErdosLean.Erdos612All.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős 612 (all `r`), part: total weight of `(List.range N).map G`
-/

namespace Erdos612All

open Erdos612

/--
@isnad1 id=eq.0h2v.s5.8ef52f9ad153 from=translated src=- shape=a92e7046 vocab=117fdefa
-/
theorem total_map_range (N : ℕ) (G : ℕ → List ℕ) :
    Layers.total ((List.range N).map G) = ∑ m ∈ Finset.range N, (G m).sum := by
  induction N with
  | zero => rfl
  | succ n ih =>
    simp only [Layers.total, List.range_succ, List.map_append, List.sum_append,
      Finset.sum_range_succ] at ih ⊢
    rw [ih]
    simp

/-- Group a sum over `range (3n)` into consecutive triples.
@isnad1 id=eq.0h2v.s6.225e7132c9ad from=translated src=- shape=fb6eec21 vocab=d17cb838
-/
theorem sum_range_three (n : ℕ) (f : ℕ → ℕ) :
    ∑ m ∈ Finset.range (3 * n), f m = ∑ j ∈ Finset.range n, (f (3 * j) + f (3 * j + 1) + f (3 * j + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

end Erdos612All

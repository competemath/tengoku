module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Minimum distance for linear binary codes

`minDist C` is defined as the infimum of Hamming distances between distinct words in `C`.
For a linear binary code, distances are weights of sums, so lower bounds on the weight of nonzero
words translate into lower bounds on `minDist`.

## Main statements
* `CodingTheory.minDist_le_weight_of_nonzero_mem`
* `CodingTheory.le_minDist_of_linear_of_weight_ge`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21

noncomputable section

open scoped BigOperators
open Uniqueness.BS81.CodingTheory

namespace CodingTheory

private lemma eq_of_add_eq_zero {n : ℕ} {x y : BinWord n}
    (h : (fun i => x i + y i) = 0) : x = y := by
  funext i
  have : x i = -y i :=
    (add_eq_zero_iff_eq_neg).1 (by simpa using congrArg (fun f : BinWord n => f i) h)
  simpa [ZMod.neg_eq_self_mod_two] using this

end CodingTheory

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21

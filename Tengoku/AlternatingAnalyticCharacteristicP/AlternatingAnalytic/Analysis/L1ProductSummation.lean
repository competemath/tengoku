import Tengoku.Seed.Analysis.Normed.Lp.lpSpace
import Tengoku.Seed.Analysis.Normed.Ring.InfiniteSum
import Tengoku.Seed.Data.Fin.Tuple.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Norm sums in ℓ¹

The coordinate norms of `x ∈ ℓ¹(J, K)` sum to `‖x‖`, and for a tuple `x₁, …, x_d` the
products `∏ r, ‖x r (a r)‖` over words `a : Fin d → J` sum to `∏ r, ‖x r‖`.
-/

open scoped lp BigOperators

namespace L1Coordinates

variable {K J : Type*} [NontriviallyNormedField K]

/-- The coordinate norms of an element of `ℓ¹` sum to its norm.-/
theorem hasSum_norm (x : lp (fun _ : J => K) 1) :
    HasSum (fun j => ‖x j‖) ‖x‖ := by
  simpa using lp.hasSum_norm (p := 1) (by simp) x

/-- The products of coordinate norms over all words `a : Fin d → J` sum to the product of
the norms.-/
theorem hasSum_prod_norm (d : ℕ) (x : Fin d → lp (fun _ : J => K) 1) :
    HasSum (fun a : Fin d → J => ∏ r, ‖x r (a r)‖) (∏ r, ‖x r‖) := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have h₀ := hasSum_norm (x 0)
      have ht := ih (fun r => x r.succ)
      have hs := h₀.summable.mul_of_nonneg ht.summable
        (fun j => norm_nonneg (x 0 j))
        (fun a => Finset.prod_nonneg fun r _ => norm_nonneg (x r.succ (a r)))
      have hp := h₀.mul ht hs
      apply (Fin.consEquiv (fun _ : Fin (d + 1) => J)).hasSum_iff.mp
      simpa [Fin.prod_univ_succ, Fin.consEquiv, Function.comp_def] using hp

end L1Coordinates

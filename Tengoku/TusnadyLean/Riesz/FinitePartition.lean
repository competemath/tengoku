import Tengoku
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset
import Tengoku.Seed.Logic.Equiv.Basic
import Tengoku.Seed.Data.Fintype.Card
import Tengoku.Seed.Data.Fintype.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Independent finite variables grouped by their rectangle

Each sample is assigned to exactly one rectangle. Regrouping coordinates by
that assignment gives the exact product factorization needed within one shape.
-/

namespace Riesz
noncomputable section
open scoped BigOperators

/-- The finite sum factors over disjoint coordinate groups. Empty groups are
included and have one possible tuple.
@isnad1 id=eq.0h5v.s7.bd93b6efa65a from=translated src=- shape=fd631c7c vocab=e0d550a7
-/
theorem sum_grouped_product {ι κ Ω : Type*} [Fintype ι] [Fintype κ] [Fintype Ω]
    [DecidableEq ι] [DecidableEq κ] (a : ι → κ)
    (F : (c : κ) → ({i : ι // a i = c} → Ω) → ℝ) :
    (∑ x : ι → Ω, ∏ c, F c (fun i => x i.1)) =
      ∏ c, ∑ y : {i : ι // a i = c} → Ω, F c y := by
  let e : (ι → Ω) ≃ ((c : κ) → ({i : ι // a i = c} → Ω)) :=
    Equiv.piCongrFiberwise (f := a) (fun _ => Equiv.refl _)
  calc
    (∑ x : ι → Ω, ∏ c, F c (fun i => x i.1)) =
        ∑ y : (c : κ) → ({i : ι // a i = c} → Ω), ∏ c, F c (y c) :=
      Equiv.sum_comp e (fun y => ∏ c, F c (y c))
    _ = _ := (Fintype.prod_sum F).symm

/--
@isnad1 id=eq.0h3v.s5.e95600fba5c3 from=translated src=- shape=222acfa9 vocab=0c9175d4
-/
lemma card_eq_sum_fiber_card {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (a : ι → κ) :
    Fintype.card ι = ∑ c : κ, Fintype.card {i : ι // a i = c} := by
  rw [← Fintype.card_sigma]
  exact (Fintype.card_congr (Equiv.sigmaFiberEquiv a)).symm

/-- Uniform product averages factor over the same disjoint groups.
@isnad1 id=eq.0h5v.s8.f60146cc356f from=translated src=- shape=00e574ba vocab=6a319e81
-/
theorem uniform_average_grouped_product {ι κ Ω : Type*}
    [Fintype ι] [Fintype κ] [Fintype Ω] [DecidableEq ι] [DecidableEq κ]
    (a : ι → κ) (F : (c : κ) → ({i : ι // a i = c} → Ω) → ℝ) :
    (∑ x : ι → Ω, ∏ c, F c (fun i => x i.1)) / (Fintype.card Ω : ℝ) ^ Fintype.card ι =
      ∏ c, ((∑ y : {i : ι // a i = c} → Ω, F c y) /
        (Fintype.card Ω : ℝ) ^ Fintype.card {i : ι // a i = c}) := by
  rw [sum_grouped_product, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum,
    ← card_eq_sum_fiber_card a]

end
end Riesz

import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SemialgebraicSets
import Tengoku.Seed.Algebra.BigOperators.Field

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Clearing positive denominators preserves polynomial sign descriptions. -/

namespace DuistermaatVanDerKallen
noncomputable section
open scoped BigOperators

theorem sum_div_mul_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (hb : ∀ i, b i ≠ 0) :
    (∑ i, a i / b i) * (∏ i, b i) =
      ∑ i, a i * ∏ j ∈ Finset.univ.erase i, b j := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_prod_erase Finset.univ b (Finset.mem_univ i),
    ← mul_assoc, div_mul_cancel₀ _ (hb i)]

theorem IsSemialgebraic.sum_div_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → MvPolynomial κ ℝ) (q : MvPolynomial κ ℝ)
    (hb : ∀ x i, 0 < MvPolynomial.eval x (b i)) :
    IsSemialgebraic κ {x | (∑ i, MvPolynomial.eval x (a i) /
      MvPolynomial.eval x (b i)) ≤ MvPolynomial.eval x q} := by
  let D : MvPolynomial κ ℝ := ∏ i, b i
  let N : MvPolynomial κ ℝ := ∑ i, a i * ∏ j ∈ Finset.univ.erase i, b j
  have hD (x : κ → ℝ) : 0 < MvPolynomial.eval x D := by
    simp only [D, map_prod]
    exact Finset.prod_pos (fun i _ => hb x i)
  have he (x : κ → ℝ) : (∑ i, MvPolynomial.eval x (a i) /
      MvPolynomial.eval x (b i)) * MvPolynomial.eval x D = MvPolynomial.eval x N := by
    simpa [D, N] using sum_div_mul_prod (fun i => MvPolynomial.eval x (a i))
      (fun i => MvPolynomial.eval x (b i)) (fun i => ne_of_gt (hb x i))
  convert IsSemialgebraic.le N (q * D) using 1
  ext x
  simp only [Set.mem_ofPred_eq, map_mul, ← he x, mul_le_mul_iff_left₀ (hD x)]

end
end DuistermaatVanDerKallen

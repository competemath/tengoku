import Tengoku.ErdosLean.ErdosLean.Erdos494.Defs
import Tengoku.ErdosLean.ErdosLean.Erdos494.Parts.DysonBinomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Erdős 494, part D2: the Ridout special case needed by [GFS62], via Mahler's trick.

Claim: for coprime `P`-smooth `x, y`, `|x - y| ≥ max(x,y)^{1-δ}` once `max(x,y)` is large.
(GFS quote Ridout's `p`-adic Thue–Siegel–Roth theorem; we only need an *archimedean*
approximation theorem with exponent `o(r)` for `r`-th roots of rationals.)

Proof from `dyson_binomial`: fix `r` with `r δ ≥ 10 √r + 2`.  Write `x = a u^r`, `y = b v^r`
with `a, b` `r`-th-power-free `P`-smooth (finitely many choices: `a ∣ ∏_{p<P} p^{r-1}`).
If infinitely many bad pairs exist, pigeonhole fixes `(a,b)`; then
`|(u/v)^r - b/a| ≤ |x-y|/(a v^r) ≤ C v^{-rδ}` and, as `|α^r - β^r| ≥ |α - β| β^{r-1}`,
`|u/v - (b/a)^{1/r}| ≤ C' v^{-rδ} < v^{-(10√r)}` for `v` large; `u/v ≠ (b/a)^{1/r}` since
`x ≠ y` (coprime, `max > 1`).  Distinct pairs give distinct `(u,v)`, contradicting
`dyson_binomial`. -/

namespace Erdos494

/-- Mahler decomposition: a `P`-smooth `x` is `a * u ^ r` with `a` bounded in terms of `P, r`.
@isnad1 id=ex.2h3v.s6.6623934f9deb from=translated src=- shape=a6d89360 vocab=1b214023
-/
lemma ridout_decomp (P r : ℕ) (hr : 0 < r) (x : ℕ) (hx : x ∈ Nat.smoothNumbers P) :
    ∃ a u : ℕ, 0 < a ∧ a ≤ ((P + 1) ^ r) ^ P ∧ 0 < u ∧ x = a * u ^ r := by
  have hx0 : x ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hx
  have hsub : x.primeFactors ⊆ Finset.range P :=
    ((Nat.mem_smoothNumbers_iff_primeFactors_subset.1 hx).2).trans (Finset.filter_subset _ _)
  refine ⟨∏ p ∈ x.primeFactors, p ^ (x.factorization p % r),
    ∏ p ∈ x.primeFactors, p ^ (x.factorization p / r), ?_, ?_, ?_, ?_⟩
  · exact Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  · calc ∏ p ∈ x.primeFactors, p ^ (x.factorization p % r)
          ≤ ∏ _p ∈ x.primeFactors, (P + 1) ^ r := by
            apply Finset.prod_le_prod' fun p hp => ?_
            have hpP : p < P := Finset.mem_range.1 (hsub hp)
            have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
            calc p ^ (x.factorization p % r) ≤ p ^ r :=
                  Nat.pow_le_pow_right hp1 (Nat.mod_lt _ hr).le
              _ ≤ (P + 1) ^ r := Nat.pow_le_pow_left (by omega) _
        _ = ((P + 1) ^ r) ^ x.primeFactors.card := Finset.prod_const _
        _ ≤ ((P + 1) ^ r) ^ P := by
            apply Nat.pow_le_pow_right (Nat.pos_of_ne_zero (by positivity))
            simpa using Finset.card_le_card hsub
  · exact Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  · conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hx0]
    rw [Finsupp.prod, Nat.support_factorization, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_mul, ← pow_add, mul_comm (x.factorization p / r) r, Nat.mod_add_div]

/-- `|α - β| β^(n-1) ≤ |α^n - β^n|` for `α, β ≥ 0`, `n ≥ 1`.
@isnad1 id=le.3h3v.s6.39b5f16253ba from=translated src=- shape=3c243832 vocab=623f8879
-/
lemma ridout_pow_sub_pow (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) (hn : 1 ≤ n) :
    |α - β| * β ^ (n - 1) ≤ |α ^ n - β ^ n| := by
  rw [← geom_sum₂_mul, abs_mul, mul_comm]
  gcongr
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => by positivity)]
  have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.2 (by omega)
  have := Finset.single_le_sum (f := fun i => α ^ i * β ^ (n - 1 - i))
    (fun i _ => by positivity) h0
  simpa using this

end Erdos494

namespace Erdos494

end Erdos494

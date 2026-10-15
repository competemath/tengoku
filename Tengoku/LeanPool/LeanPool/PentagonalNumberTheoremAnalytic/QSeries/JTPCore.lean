/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
module

public import Tengoku.LeanPool.LeanPool.PentagonalNumberTheoremAnalytic.QSeries.JTPKeyIdentity

/-!
# Core lemmas for the Jacobi triple product proof

The proof strategy: Show $(q;q)_∞ (-z;q)_∞ (-q/z;q)_∞ = g(z)$ by:
1. Dividing both sides by $(-q/z;q)_∞$ (nonzero for ‖q/z‖ < 1)
2. Showing $g(z) / (-q/z;q)_∞ = (q;q)_∞ (-z;q)_∞$
3. This follows from the Cauchy product and the Euler 2nd identity

Key identity: $(q;q)_∞ / (q;q)_n = (q^{n+1};q)_∞$ (telescoping)
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace QSeries

noncomputable section

/-- Telescoping factorisation: $(q;q)_\infty = (q;q)_n \cdot (q \cdot q^n; q)_\infty$.
@isnad1 id=eq.1h2v.s5.b01edd2f5484 from=translated src=- shape=c6479eb7 vocab=13d4325a
-/
theorem qPochhammerInf_self_eq_qPochhammer_mul {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    qPochhammerInf q q = qPochhammer q q n * qPochhammerInf (q * q ^ n) q := by
  rw [qPochhammerInf_mul_pow_eq_div hq n, mul_div_cancel₀ _ (qPochhammer_self_ne_zero hq n)]

/-- Euler's second identity evaluated at $z = -q^{n+1}$, giving $(q^{n+1}; q)_\infty$.
@isnad1 id=hassum.1h2v.s7.34a2f36b5519 from=translated src=- shape=7205b447 vocab=89110169
-/
theorem euler_second_identity_neg_pow {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    HasSum (fun m : ℕ => q ^ m.choose 2 * (-q ^ (n + 1)) ^ m / qPochhammer q q m)
      (qPochhammerInf (q ^ (n + 1)) q) := by
  convert euler_second_identity hq ?_ using 1
  · norm_num
  · simpa using pow_lt_one₀ (norm_nonneg q) hq (by omega)

/-- The product $(q;q)_\infty (-z;q)_\infty$ equals
$\sum_n q^{\binom{n}{2}} z^n (q^{n+1};q)_\infty$, via Euler's second identity.
@isnad1 id=hassum.2h2v.s7.7ea241ad3c7e from=translated src=- shape=5c6943da vocab=9d01afcb
-/
theorem hasSum_pow_choose_two_mul_pow_mul_qPochhammerInf {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => q ^ n.choose 2 * z ^ n * qPochhammerInf (q * q ^ n) q)
      (qPochhammerInf q q * qPochhammerInf (-z) q) := by
  refine ((euler_second_identity hq hz).mul_left (qPochhammerInf q q)).congr_fun fun n => ?_
  rw [qPochhammerInf_mul_pow_eq_div hq n]
  ring

/-- Key identity: the n-th coefficient of the product (q;q)_∞ (-z;q)_∞
expanded using Euler 2nd, multiplied by (q;q)_∞, gives the JTP coefficient.
Specifically: qPochhammerInf (q * q^n) q = qPochhammerInf (q^(n+1)) q.
@isnad1 id=eq.0h2v.s5.2fb10db3c1d3 from=translated src=- shape=feb0862e vocab=dc4ab73c
-/
theorem qPochhammerInf_mul_pow {q : ℂ} (n : ℕ) :
    qPochhammerInf (q * q ^ n) q = qPochhammerInf (q ^ (n + 1)) q := by
  congr 1; ring

/-- The Jacobi triple product identity at $q = 0$, verified directly.
@isnad1 id=eq.1h1v.s7.95227bb6e71a from=translated src=- shape=1ce99236 vocab=4399cc27
-/
theorem jacobiTripleProduct_zero {z : ℂ} (hz' : z ≠ 0) :
    qPochhammerInf 0 0 * qPochhammerInf (-z) 0 * qPochhammerInf (-0 / z) 0 =
    (∑' k : ℕ, z ^ k * (0 : ℂ) ^ k.choose 2) +
    (∑' m : ℕ, z⁻¹ ^ (m + 1) * (0 : ℂ) ^ (m + 2).choose 2) := by
  norm_num [qPochhammerInf]
  rw [tprod_eq_prod]
  any_goals exact {0}
  · rw [tsum_eq_sum, tsum_eq_single 0] <;> norm_num
    any_goals exact {0, 1}
    · norm_num [Finset.sum_pair]
    · exact fun n hn => Or.inr <| Nat.ne_of_gt <| Nat.choose_pos <| by omega
    · intro b hb; rcases b with (_ | _ | b) <;> simp_all [Nat.choose]
  · aesop

/-- Euler's second identity evaluated at $z = -q/z$, giving $(-q/z; q)_\infty$.
@isnad1 id=hassum.3h2v.s7.cc1ad3a7abd8 from=translated src=- shape=9498a473 vocab=84c7722d
-/
theorem euler_second_identity_div {q z : ℂ} (hq : ‖q‖ < 1) (hzq : ‖q‖ < ‖z‖)
    (hz' : z ≠ 0) :
    HasSum (fun m : ℕ => q ^ m.choose 2 * q ^ m * z⁻¹ ^ m / qPochhammer q q m)
      (qPochhammerInf (-q / z) q) := by
  have hnorm : ‖q / z‖ < 1 := by
    rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hz')).2 hzq
  rw [neg_div]
  exact (euler_second_identity hq hnorm).congr_fun fun n => by ring

/-! ### The diagonal splitting of a double series over `ℕ × ℕ` -/

/-- The diagonal splitting equivalence `(ℕ × ℕ) ⊕ (ℕ × ℕ) ≃ ℕ × ℕ`: the left summand
enumerates the pairs on or below the diagonal as `(m + k, m)`, the right summand
enumerates the pairs strictly above it as `(n, n + l + 1)`. -/
private def diagonalEquiv : (ℕ × ℕ) ⊕ (ℕ × ℕ) ≃ ℕ × ℕ where
  toFun s := match s with
    | .inl p => (p.2 + p.1, p.2)
    | .inr p => (p.2, p.2 + (p.1 + 1))
  invFun p := if p.2 ≤ p.1 then .inl (p.1 - p.2, p.2) else .inr (p.2 - p.1 - 1, p.1)
  left_inv := by rintro (⟨k, m⟩ | ⟨l, n⟩) <;> simp
  right_inv := by rintro ⟨a, b⟩; dsimp only; split_ifs with h <;> simp <;> omega

/-- `HasSum` form of the diagonal splitting of a family indexed by `ℕ × ℕ`. -/
private theorem hasSum_split_diagonal {f : ℕ × ℕ → ℂ} {a b : ℂ}
    (h1 : HasSum (fun p : ℕ × ℕ => f (p.2 + p.1, p.2)) a)
    (h2 : HasSum (fun p : ℕ × ℕ => f (p.2, p.2 + (p.1 + 1))) b) :
    HasSum f (a + b) :=
  diagonalEquiv.hasSum_iff.mp (HasSum.sum (f := f ∘ diagonalEquiv) h1 h2)

/-- Splitting a summable family over `ℕ × ℕ` along the diagonal:
$\sum_p f(p) = \sum_k \sum_m f(m+k, m) + \sum_l \sum_n f(n, n+l+1)$.
@isnad1 id=eq.1h1v.s7.a15713e8b6e8 from=translated src=- shape=2cdb25ba vocab=bce2b672
-/
theorem tsum_split_diagonal {f : ℕ × ℕ → ℂ} (hf : Summable f) :
    ∑' p : ℕ × ℕ, f p =
      (∑' k : ℕ, ∑' m : ℕ, f (m + k, m)) + ∑' l : ℕ, ∑' n : ℕ, f (n, n + (l + 1)) := by
  have hc : Summable (f ∘ diagonalEquiv) := diagonalEquiv.summable_iff.mpr hf
  have hl : Summable fun p : ℕ × ℕ => f (p.2 + p.1, p.2) := hc.comp_injective Sum.inl_injective
  have hr : Summable fun p : ℕ × ℕ => f (p.2, p.2 + (p.1 + 1)) :=
    hc.comp_injective Sum.inr_injective
  rw [(hasSum_split_diagonal hl.hasSum hr.hasSum).tsum_eq, hl.tsum_prod, hr.tsum_prod]

/-! ### The Jacobi triple product from two `HasSum` inputs -/

end

end QSeries

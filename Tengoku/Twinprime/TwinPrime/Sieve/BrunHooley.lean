import Tengoku
import Tengoku.Twinprime.TwinPrime.Sieve.Bonferroni
import Tengoku.Twinprime.TwinPrime.Sieve.Rankin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Brun–Hooley lower-bound sieve

Following Ford–Halberstam, *The Brun–Hooley sieve* (2000).  The sifting primes are split into
pairwise coprime blocks `P_j` (`j : Fin r`), and on each block the Möbius function is truncated:
`U_j(n) = ∑_{d ∣ (n, P_j), ω d ≤ 2k_j} μ d ≥ e_j(n) = [(n, P_j) = 1]` and
`L_j(n) = ∑_{d ∣ (n, P_j), ω d ≤ 2k_j + 1} μ d ≤ e_j(n)`.  The elementary inequality

  `∏_j e_j ≥ ∏_j U_j − ∑_j (U_j − L_j) ∏_{i ≠ j} U_i`

(`prod_ge_prod_sub_sum`) then gives a lower bound for the sifted sum in which every term is a
product over blocks, hence factorises by multiplicativity.  This file proves the pointwise
inequality, the even-truncation Bonferroni bound, and the resulting sieve inequality
`siftedSum_ge_brunHooley` for an arbitrary `BoundingSieve` whose `prodPrimes` is a product of
coprime blocks.
-/

noncomputable section

open Finset Real Nat ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius ArithmeticFunction.omega

namespace TwinPrime.Sieve

/-! ### The pointwise inequality -/

/-- If `0 ≤ e i ≤ u i` and `l i ≤ e i` on `s`, then
`∏ e ≥ ∏ u − ∑_j (u j − l j) ∏_{i ≠ j} u i`.
@isnad1 id=le.3h5v.s7.bed39e298367 from=translated src=- shape=b18f7710 vocab=e80c8dad
-/
theorem prod_ge_prod_sub_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (e u l : ι → ℝ)
    (he0 : ∀ i ∈ s, 0 ≤ e i) (heu : ∀ i ∈ s, e i ≤ u i) (hle : ∀ i ∈ s, l i ≤ e i) :
    ∏ i ∈ s, u i - ∑ j ∈ s, (u j - l j) * ∏ i ∈ s.erase j, u i ≤ ∏ i ∈ s, e i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have he0' : ∀ i ∈ s, 0 ≤ e i := fun i hi => he0 i (mem_insert_of_mem hi)
    have heu' : ∀ i ∈ s, e i ≤ u i := fun i hi => heu i (mem_insert_of_mem hi)
    have hle' : ∀ i ∈ s, l i ≤ e i := fun i hi => hle i (mem_insert_of_mem hi)
    have ih' := ih he0' heu' hle'
    have hu0 : ∀ i ∈ s, 0 ≤ u i := fun i hi => le_trans (he0' i hi) (heu' i hi)
    have hprod_u : 0 ≤ ∏ i ∈ s, u i := prod_nonneg hu0
    -- the correction sum is nonnegative
    have hT : 0 ≤ ∑ j ∈ s, (u j - l j) * ∏ i ∈ s.erase j, u i := by
      apply sum_nonneg
      intro j hj
      apply mul_nonneg
      · linarith [hle' j hj, heu' j hj]
      · exact prod_nonneg fun i hi => hu0 i (mem_of_mem_erase hi)
    have hea0 := he0 a (mem_insert_self a s)
    have heau := heu a (mem_insert_self a s)
    have hlea := hle a (mem_insert_self a s)
    rw [prod_insert ha, prod_insert ha, sum_insert ha, erase_insert ha]
    have hsum : ∑ j ∈ s, (u j - l j) * ∏ i ∈ (insert a s).erase j, u i =
        u a * ∑ j ∈ s, (u j - l j) * ∏ i ∈ s.erase j, u i := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      have hja : j ≠ a := fun h => ha (h ▸ hj)
      rw [erase_insert_of_ne hja.symm, prod_insert (fun h => ha (mem_of_mem_erase h))]
      ring
    rw [hsum]
    -- goal: u a * ∏ u - ((u a - l a) * ∏ u + u a * T) ≤ e a * ∏ e
    have h1 : e a * (∏ i ∈ s, u i - ∑ j ∈ s, (u j - l j) * ∏ i ∈ s.erase j, u i) ≤
        e a * ∏ i ∈ s, e i := mul_le_mul_of_nonneg_left ih' hea0
    nlinarith [mul_le_mul_of_nonneg_right heau hT, mul_le_mul_of_nonneg_right hlea hprod_u]

/-! ### Even truncation: an upper-bound sieve -/

/-- **Bonferroni (upper)**: for squarefree `g` and even `m`, `[g = 1] ≤ ∑_{d ∣ g} truncMoebius m d`.
@isnad1 id=le.2h2v.s5.3546497d7c5c from=translated src=- shape=25a76d12 vocab=bba7f389
-/
theorem le_sum_truncMoebius {g : ℕ} (hg : Squarefree g) {m : ℕ} (hm : Even m) :
    (if g = 1 then (1 : ℝ) else 0) ≤ ∑ d ∈ g.divisors, truncMoebius m d := by
  rw [sum_divisors_truncMoebius hg]
  by_cases h1 : g = 1
  · subst h1
    rw [ite_eq_left rfl]
    simp only [cardDistinctFactors_one]
    rw [sum_range_succ', Nat.choose_zero_right]
    simp only [Nat.choose_zero_succ, Nat.cast_zero, mul_zero, sum_const_zero, zero_add, pow_zero,
      Nat.cast_one, mul_one]
    exact le_rfl
  · rw [ite_eq_right h1]
    have hω : 1 ≤ ω g := by
      rw [← card_primeFactors_eq]
      apply Finset.card_pos.mpr
      rw [Nat.nonempty_primeFactors]
      have := hg.ne_zero
      omega
    have := sum_neg_one_pow_choose (ω g) m hω
    have hcast : ∑ j ∈ range (m + 1), (-1 : ℝ) ^ j * ((ω g).choose j : ℝ) =
        (((-1 : ℤ) ^ m * ((ω g - 1).choose m : ℤ) : ℤ) : ℝ) := by
      rw [← this]; push_cast; rfl
    rw [hcast]
    obtain ⟨k, rfl⟩ := hm
    push_cast
    rw [← two_mul, pow_mul]
    simp only [neg_one_sq, one_pow, one_mul]
    positivity

/-! ### Block sieves -/

/-- A block decomposition of the sifting primes: `r` pairwise coprime squarefree numbers whose
product is `P`.-/
structure Blocks (P : ℕ) (r : ℕ) where
  block : Fin r → ℕ
  block_squarefree : ∀ j, Squarefree (block j)
  block_coprime : ∀ i j, i ≠ j → Nat.Coprime (block i) (block j)
  prod_block : ∏ j, block j = P

variable {P r : ℕ} (B : Blocks P r)

/--
@isnad1 id=dvd.0h4v.s4.61f56494c257 from=translated src=- shape=f749fafd vocab=4f0a5523
-/
theorem Blocks.block_dvd (j : Fin r) : B.block j ∣ P :=
  calc B.block j ∣ ∏ i, B.block i := Finset.dvd_prod_of_mem _ (mem_univ j)
    _ = P := B.prod_block

/--
@isnad1 id=ne.0h4v.s4.d0977f266ef2 from=translated src=- shape=76133477 vocab=183dd5b6
-/
theorem Blocks.block_ne_zero (j : Fin r) : B.block j ≠ 0 := (B.block_squarefree j).ne_zero

/-- `(n, P) = 1` iff `(n, P_j) = 1` for every block.
@isnad1 id=iff.0h4v.s4.e9905aef720d from=translated src=- shape=5668f613 vocab=2848b673
-/
theorem Blocks.coprime_iff (n : ℕ) :
    Nat.Coprime P n ↔ ∀ j, Nat.Coprime (B.block j) n := by
  have h := Nat.coprime_prod_left_iff (t := Finset.univ) (s := B.block) (x := n)
  rw [B.prod_block] at h
  simpa using h

/-- The truncated block sum `∑_{d ∣ (n, P_j)} truncMoebius m d`, written as a sum over the
divisors of the block.-/
def blockSum (Pj : ℕ) (m : ℕ) (n : ℕ) : ℝ :=
  ∑ d ∈ Pj.divisors, if d ∣ n then truncMoebius m d else 0

/--
@isnad1 id=eq.1h3v.s5.8997230dc173 from=translated src=- shape=405fcaf0 vocab=1c9a0b53
-/
theorem blockSum_eq_sum_gcd {Pj : ℕ} (hPj : Pj ≠ 0) (m n : ℕ) :
    blockSum Pj m n = ∑ d ∈ (Nat.gcd Pj n).divisors, truncMoebius m d := by
  unfold blockSum
  rw [← sum_filter, ← Nat.divisors_filter_dvd_of_dvd hPj (Nat.gcd_dvd_left _ _)]
  apply sum_congr
  · ext x
    simp +contextual [dvd_gcd_iff]
  · intros; rfl

/-- Lower truncation (odd `m`): `blockSum ≤ [(n, P_j) = 1]`.
@isnad1 id=le.2h3v.s5.aa0f042d9034 from=translated src=- shape=604a26cb vocab=06241501
-/
theorem blockSum_le_of_odd {Pj : ℕ} (hPj : Squarefree Pj) {m : ℕ} (hm : Odd m) (n : ℕ) :
    blockSum Pj m n ≤ if Nat.Coprime Pj n then 1 else 0 := by
  rw [blockSum_eq_sum_gcd hPj.ne_zero]
  have := sum_truncMoebius_le (hPj.squarefree_of_dvd (Nat.gcd_dvd_left Pj n)) hm
  simpa [Nat.Coprime] using this

/-- Upper truncation (even `m`): `[(n, P_j) = 1] ≤ blockSum`.
@isnad1 id=le.2h3v.s5.27f93bdf6ec9 from=translated src=- shape=ab3d4d60 vocab=341221cd
-/
theorem le_blockSum_of_even {Pj : ℕ} (hPj : Squarefree Pj) {m : ℕ} (hm : Even m) (n : ℕ) :
    (if Nat.Coprime Pj n then (1 : ℝ) else 0) ≤ blockSum Pj m n := by
  rw [blockSum_eq_sum_gcd hPj.ne_zero]
  have := le_sum_truncMoebius (hPj.squarefree_of_dvd (Nat.gcd_dvd_left Pj n)) hm
  simpa [Nat.Coprime] using this

/-- The Brun–Hooley pointwise lower bound for the indicator of `(n, P) = 1`, with even
truncations `2 k j` on every block and the odd truncation `2 k j + 1` on the "defective" block.
@isnad1 id=le.0h5v.s7.edac87dd03ea from=translated src=- shape=932416dc vocab=27f20e89
-/
theorem Blocks.indicator_ge (k : Fin r → ℕ) (n : ℕ) :
    ∏ j, blockSum (B.block j) (2 * k j) n -
        ∑ j, (blockSum (B.block j) (2 * k j) n - blockSum (B.block j) (2 * k j + 1) n) *
          ∏ i ∈ Finset.univ.erase j, blockSum (B.block i) (2 * k i) n ≤
      if Nat.Coprime P n then 1 else 0 := by
  have key := prod_ge_prod_sub_sum (Finset.univ : Finset (Fin r))
    (fun j => if Nat.Coprime (B.block j) n then (1 : ℝ) else 0)
    (fun j => blockSum (B.block j) (2 * k j) n)
    (fun j => blockSum (B.block j) (2 * k j + 1) n)
    (fun j _ => by split_ifs <;> norm_num)
    (fun j _ => le_blockSum_of_even (B.block_squarefree j) ⟨k j, by ring⟩ n)
    (fun j _ => blockSum_le_of_odd (B.block_squarefree j) ⟨k j, rfl⟩ n)
  refine le_trans key (le_of_eq ?_)
  by_cases h : Nat.Coprime P n
  · rw [ite_eq_left h]
    apply prod_eq_one
    intro j _
    rw [ite_eq_left ((B.coprime_iff n).mp h j)]
  · rw [ite_eq_right h]
    have hnot : ¬ ∀ j, Nat.Coprime (B.block j) n := fun hall => h ((B.coprime_iff n).mpr hall)
    obtain ⟨j, hj⟩ := not_forall.mp hnot
    apply prod_eq_zero (mem_univ j)
    rw [ite_eq_right hj]

end TwinPrime.Sieve

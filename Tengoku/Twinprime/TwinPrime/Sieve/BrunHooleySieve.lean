import Tengoku
import Tengoku.Twinprime.TwinPrime.Sieve.BrunHooley

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Brun–Hooley sieve inequality, expanded over block divisors

For a `BoundingSieve` `s` whose `prodPrimes` is a product of `r` pairwise coprime blocks
(`Blocks s.prodPrimes r`), and truncation parameters `k : Fin r → ℕ`, we expand the pointwise
Brun–Hooley inequality into sums over tuples `D : Fin r → ℕ` of block divisors:

  `siftedSum ≥ ∑_D (∏_j μ_{2k_j}(D_j)) A_{∏ D} − ∑_j ∑_D (∏_i f^{(j)}_i(D_i)) A_{∏ D}`

where `f^{(j)}_i = μ_{2k_i}` for `i ≠ j` and `f^{(j)}_j = μ_{2k_j} − μ_{2k_j+1}`
(`siftedSum_ge_brunHooley`).  The main terms factorise over blocks by multiplicativity of `ν`
(`sum_prod_mul_nu`).
-/

noncomputable section

open Finset Real Nat ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius ArithmeticFunction.omega

namespace TwinPrime.Sieve

/-! ### Products of pairwise coprime divisors -/

theorem prod_dvd_of_pairwise_coprime {ι : Type*} [DecidableEq ι] (s : Finset ι) (D : ι → ℕ)
    (n : ℕ) (hcop : (s : Set ι).Pairwise (Function.onFun Nat.Coprime D)) (hdvd : ∀ i ∈ s, D i ∣ n) :
    ∏ i ∈ s, D i ∣ n := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha]
    have hcop' : (s : Set ι).Pairwise (Function.onFun Nat.Coprime D) :=
      hcop.mono (Finset.coe_subset.mpr (subset_insert a s))
    have h1 : Nat.Coprime (D a) (∏ i ∈ s, D i) := by
      apply Nat.Coprime.prod_right
      intro i hi
      exact hcop (Finset.mem_coe.mpr (mem_insert_self a s)) (Finset.mem_coe.mpr (mem_insert_of_mem hi))
        (fun h => ha (h ▸ hi))
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h1 (hdvd a (mem_insert_self _ _))
      (ih hcop' fun i hi => hdvd i (mem_insert_of_mem hi))

variable {P r : ℕ}

theorem Blocks.pairwise_coprime_of_dvd (B : Blocks P r) (D : Fin r → ℕ)
    (hD : ∀ j, D j ∣ B.block j) : Pairwise (Function.onFun Nat.Coprime D) := by
  intro i j hij
  exact Nat.Coprime.coprime_dvd_right (hD j)
    (Nat.Coprime.coprime_dvd_left (hD i) (B.block_coprime i j hij))

/-! ### Block sums with general weights -/

/-- `∑_{d ∣ P_j, d ∣ n} f d`.-/
def blockSumF (Pj : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ Pj.divisors, if d ∣ n then f d else 0

theorem blockSum_eq_blockSumF (Pj m n : ℕ) : blockSum Pj m n = blockSumF Pj (truncMoebius m) n := rfl

theorem blockSumF_sub (Pj : ℕ) (f g : ℕ → ℝ) (n : ℕ) :
    blockSumF Pj f n - blockSumF Pj g n = blockSumF Pj (fun d => f d - g d) n := by
  unfold blockSumF
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  split_ifs <;> simp

/-- **Expansion**: `∑_n a_n ∏_j blockSumF (P_j) (f j) n = ∑_D (∏_j f j (D j)) · A_{∏ D}`.-/
theorem sum_weights_prod_blockSumF (s : BoundingSieve) (B : Blocks s.prodPrimes r)
    (f : Fin r → ℕ → ℝ) :
    ∑ n ∈ s.support, s.weights n * ∏ j, blockSumF (B.block j) (f j) n =
      ∑ D ∈ Fintype.piFinset (fun j => (B.block j).divisors),
        (∏ j, f j (D j)) * s.multSum (∏ j, D j) := by
  classical
  unfold blockSumF
  simp_rw [prod_univ_sum, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro D hD
  rw [Fintype.mem_piFinset] at hD
  have hDdvd : ∀ j, D j ∣ B.block j := fun j => dvd_of_mem_divisors (hD j)
  have hcop := B.pairwise_coprime_of_dvd D hDdvd
  simp only [multSum]
  rw [mul_sum]
  apply sum_congr rfl
  intro n _
  by_cases h : ∏ j, D j ∣ n
  · rw [ite_eq_left h]
    have hall : ∀ j, D j ∣ n := fun j => (Finset.dvd_prod_of_mem D (mem_univ j)).trans h
    rw [prod_congr rfl (fun j _ => ite_eq_left (hall j))]
    ring
  · rw [ite_eq_right h]
    have : ∃ j, ¬ D j ∣ n := by
      by_contra hall
      apply h
      apply prod_dvd_of_pairwise_coprime Finset.univ D n (hcop.set_pairwise _)
      intro j _
      exact not_not.mp (not_exists.mp hall j)
    obtain ⟨j, hj⟩ := this
    rw [prod_eq_zero (mem_univ j) (ite_eq_right hj)]
    ring

/-- The main term factorises over blocks.-/
theorem sum_prod_mul_nu (s : BoundingSieve) (B : Blocks s.prodPrimes r) (f : Fin r → ℕ → ℝ) :
    ∑ D ∈ Fintype.piFinset (fun j => (B.block j).divisors),
        (∏ j, f j (D j)) * s.nu (∏ j, D j) =
      ∏ j, ∑ d ∈ (B.block j).divisors, f j d * s.nu d := by
  classical
  rw [prod_univ_sum]
  apply sum_congr rfl
  intro D hD
  rw [Fintype.mem_piFinset] at hD
  have hcop := B.pairwise_coprime_of_dvd D (fun j => dvd_of_mem_divisors (hD j))
  rw [IsMultiplicative.map_prod D s.nu_mult Finset.univ (hcop.set_pairwise _), ← prod_mul_distrib]

/-! ### The sieve inequality -/

/-- The weight family for the `j`-th defective term.-/
def defect (k : Fin r → ℕ) (j : Fin r) : Fin r → ℕ → ℝ := fun i d =>
  if i = j then truncMoebius (2 * k j) d - truncMoebius (2 * k j + 1) d
  else truncMoebius (2 * k i) d

theorem prod_blockSumF_defect (B : Blocks P r) (k : Fin r → ℕ) (j : Fin r) (n : ℕ) :
    ∏ i, blockSumF (B.block i) (defect k j i) n =
      (blockSum (B.block j) (2 * k j) n - blockSum (B.block j) (2 * k j + 1) n) *
        ∏ i ∈ Finset.univ.erase j, blockSum (B.block i) (2 * k i) n := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ _ (mem_univ j)]
  congr 1
  · unfold defect
    simp only [ite_true]
    rw [blockSum_eq_blockSumF, blockSum_eq_blockSumF, blockSumF_sub]
  · apply prod_congr rfl
    intro i hi
    have hij : i ≠ j := (mem_erase.mp hi).1
    rw [blockSum_eq_blockSumF]
    unfold defect
    congr 1
    ext d
    simp [hij]

/-- **The Brun–Hooley sieve inequality** (expanded over block divisors).-/
theorem siftedSum_ge_brunHooley (s : BoundingSieve) (B : Blocks s.prodPrimes r) (k : Fin r → ℕ) :
    ∑ D ∈ Fintype.piFinset (fun j => (B.block j).divisors),
        (∏ j, truncMoebius (2 * k j) (D j)) * s.multSum (∏ j, D j) -
      ∑ j, ∑ D ∈ Fintype.piFinset (fun j => (B.block j).divisors),
        (∏ i, defect k j i (D i)) * s.multSum (∏ i, D i) ≤ s.siftedSum := by
  classical
  rw [siftedSum_eq_sum_support_mul_ite]
  have hexp1 := sum_weights_prod_blockSumF s B (fun j => truncMoebius (2 * k j))
  have hexp2 : ∀ j, ∑ n ∈ s.support, s.weights n * ∏ i, blockSumF (B.block i) (defect k j i) n =
      ∑ D ∈ Fintype.piFinset (fun j => (B.block j).divisors),
        (∏ i, defect k j i (D i)) * s.multSum (∏ i, D i) :=
    fun j => sum_weights_prod_blockSumF s B (defect k j)
  rw [← hexp1]
  simp_rw [← hexp2]
  rw [Finset.sum_comm, ← sum_sub_distrib]
  apply sum_le_sum
  intro n _
  rw [← mul_sum, ← mul_sub]
  apply mul_le_mul_of_nonneg_left _ (s.weights_nonneg n)
  have := B.indicator_ge k n
  simp only [Nat.coprime_iff_gcd_eq_one] at this
  simp only [prod_blockSumF_defect, ← blockSum_eq_blockSumF]
  exact this

end TwinPrime.Sieve

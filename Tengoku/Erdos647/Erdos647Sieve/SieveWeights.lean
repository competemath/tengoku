/-
The two concrete weight lists for the finite-moment sieve.
NEW IMPLEMENTATION: not compiled in the assistant environment.
Indices are enumerated; equal weight VALUES are never deduplicated.
The integer n and interval translation A are unrestricted throughout.
-/
import Tengoku.Erdos647.Erdos647Sieve.BonferroniMajorant
import Tengoku.Erdos647.Erdos647Sieve.HitCountBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace Erdos647Sieve
open Bonferroni

/-- Enumerating finite indices preserves a sum even when values repeat.-/
theorem sum_map_toList_eq_sum (s : Finset ℕ) (w : ℕ → ℝ) :
    (s.toList.map w).sum = ∑ p ∈ s, w p := by
  classical
  simpa only [Finset.toList_toFinset] using (List.sum_toFinset w s.nodup_toList).symm

/-- Enumerating finite indices preserves a product even when values repeat.-/
theorem prod_map_toList_eq_prod (s : Finset ℕ) (w : ℕ → ℝ) :
    (s.toList.map w).prod = ∏ p ∈ s, w p := by
  classical
  simpa only [Finset.toList_toFinset] using (List.prod_toFinset w s.nodup_toList).symm

theorem avoidProduct_map_toList (s : Finset ℕ) (w : ℕ → ℝ) :
    avoidProduct (s.toList.map w) = ∏ p ∈ s, (1 - w p) := by
  classical
  rw [avoidProduct_eq_prod, List.map_map]
  simpa only [Function.comp_def] using prod_map_toList_eq_prod s (fun p => 1 - w p)

/-- A product of constant-or-one factors, without any probabilistic assumptions.-/
theorem prod_ite_eq_pow_card_filter (s : Finset ℕ) (P : ℕ → Prop)
    [DecidablePred P] (z : ℝ) :
    (∏ p ∈ s, if P p then z else 1) = z ^ (s.filter P).card := by
  calc
    (∏ p ∈ s, if P p then z else 1)
        = ∏ _p ∈ s.filter P, z :=
          (Finset.prod_filter (s := s) P (fun _ : ℕ => z)).symm
    _ = z ^ (s.filter P).card := Finset.prod_const z

/-- Pointwise weights for the selected primes. All integer values n are allowed.-/
def hitWeights (H : ℕ) (y z : ℝ) (n : ℤ) : List ℝ := by
  classical
  exact (selectedPrimes H y).toList.map
    (fun p : ℕ => if (p : ℤ) ∣ windowPolynomial H n then 1 - z else 0)

/-- Mean weights (1-z)H/p, indexed by primes rather than distinct weight values.-/
def meanWeights (H : ℕ) (y z : ℝ) : List ℝ :=
  (selectedPrimes H y).toList.map (fun p : ℕ => (1 - z) * (H : ℝ) / (p : ℝ))

theorem hitWeights_bounds (H : ℕ) (y z : ℝ) (n : ℤ)
    (hz0 : 0 < z) (hz1 : z < 1) :
    ∀ a ∈ hitWeights H y z n, 0 ≤ a ∧ a ≤ 1 := by
  classical
  intro a ha
  change a ∈ (selectedPrimes H y).toList.map
    (fun p : ℕ => if (p : ℤ) ∣ windowPolynomial H n then 1 - z else 0) at ha
  obtain ⟨p, _hp, rfl⟩ := List.mem_map.mp ha
  split_ifs <;> constructor <;> linarith

/-- Exact connection to the protected hitCount, including polynomial zeros.-/
theorem avoidProduct_hitWeights (H : ℕ) (y z : ℝ) (n : ℤ) :
    avoidProduct (hitWeights H y z n) = z ^ hitCount H y n := by
  classical
  unfold hitWeights
  rw [avoidProduct_map_toList]
  calc
    (∏ p ∈ selectedPrimes H y,
        (1 - if (p : ℤ) ∣ windowPolynomial H n then 1 - z else 0))
        = ∏ p ∈ selectedPrimes H y,
          (if (p : ℤ) ∣ windowPolynomial H n then z else 1) := by
            apply Finset.prod_congr rfl
            intro p _hp
            split_ifs <;> ring
    _ = z ^ ((selectedPrimes H y).filter
          (fun p : ℕ => (p : ℤ) ∣ windowPolynomial H n)).card :=
      prod_ite_eq_pow_card_filter (selectedPrimes H y)
        (fun p : ℕ => (p : ℤ) ∣ windowPolynomial H n) z
    _ = z ^ hitCount H y n := by rw [hitCount_eq_nat_filter_card]

/-- The exact mean sum; no analytic prime-distribution estimate is involved.-/
theorem meanWeights_sum (H : ℕ) (y z : ℝ) :
    (meanWeights H y z).sum = (1 - z) * primeMass H y := by
  classical
  unfold meanWeights
  rw [sum_map_toList_eq_sum]
  calc
    (∑ p ∈ selectedPrimes H y, (1 - z) * (H : ℝ) / (p : ℝ))
        = ∑ p ∈ selectedPrimes H y,
            ((1 - z) * (H : ℝ)) * ((1 : ℝ) / (p : ℝ)) := by
              apply Finset.sum_congr rfl
              intro p _hp
              ring
    _ = ((1 - z) * (H : ℝ)) *
          (∑ p ∈ selectedPrimes H y, (1 : ℝ) / (p : ℝ)) :=
      (Finset.mul_sum _ _ _).symm
    _ = (1 - z) * primeMass H y := by unfold primeMass; ring

/-- Every selected prime is larger than H. This controls each mean weight.-/
theorem meanWeights_bounds (H : ℕ) (y z : ℝ)
    (hz0 : 0 < z) (hz1 : z < 1) :
    ∀ a ∈ meanWeights H y z, 0 ≤ a ∧ a ≤ 1 := by
  classical
  intro a ha
  change a ∈ (selectedPrimes H y).toList.map
    (fun p : ℕ => (1 - z) * (H : ℝ) / (p : ℝ)) at ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  have hpSel : p ∈ selectedPrimes H y := by simpa using hp
  change p ∈ (Finset.Icc (H + 1) (Nat.floor y)).filter Nat.Prime at hpSel
  have hHp : H < p := by
    have hh := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpSel).1).1
    omega
  have hp0n : 0 < p := by omega
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp0n
  have hH0 : 0 ≤ (H : ℝ) := Nat.cast_nonneg H
  have hHple : (H : ℝ) ≤ (p : ℝ) := by exact_mod_cast hHp.le
  have ht0 : 0 ≤ 1 - z := by linarith
  have ht1 : 1 - z ≤ 1 := by linarith
  constructor
  · exact div_nonneg (mul_nonneg ht0 hH0) hp0.le
  · apply (div_le_iff₀ hp0).mpr
    calc
      (1 - z) * (H : ℝ) ≤ 1 * (H : ℝ) :=
        mul_le_mul_of_nonneg_right ht1 hH0
      _ ≤ 1 * (p : ℝ) := by simpa using hHple

/-- First Bonferroni use, valid even at integer zeros of the polynomial.-/
theorem hitWeight_pointwise_upper (H : ℕ) (y z : ℝ) (n : ℤ)
    (hz0 : 0 < z) (hz1 : z < 1) (J : ℕ) (hJ : Even J) :
    z ^ hitCount H y n ≤ ∑ j ∈ Finset.range (J + 1),
      (-1 : ℝ) ^ j * elementary (hitWeights H y z n) j := by
  have h := (even_sum_bounds (hitWeights H y z n)
    (hitWeights_bounds H y z n hz0 hz1) J hJ).1
  simpa only [avoidProduct_hitWeights] using h

/-- The pointwise truncation summed over any translated interval, with the
finite sums transposed. No lower bound on A is imposed. This is NOT the moment
estimate: it retains the actual elementary coefficients on the right.-/
theorem hitWeight_interval_upper (A : ℤ) (X H : ℕ) (y z : ℝ)
    (hz0 : 0 < z) (hz1 : z < 1) (J : ℕ) (hJ : Even J) :
    (∑ n ∈ Finset.Icc (A + 1) (A + (X : ℤ)), z ^ hitCount H y n) ≤
      ∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j *
        (∑ n ∈ Finset.Icc (A + 1) (A + (X : ℤ)),
          elementary (hitWeights H y z n) j) := by
  classical
  calc
    (∑ n ∈ Finset.Icc (A + 1) (A + (X : ℤ)), z ^ hitCount H y n)
        ≤ ∑ n ∈ Finset.Icc (A + 1) (A + (X : ℤ)),
          ∑ j ∈ Finset.range (J + 1),
            (-1 : ℝ) ^ j * elementary (hitWeights H y z n) j := by
              apply Finset.sum_le_sum
              intro n _hn
              exact hitWeight_pointwise_upper H y z n hz0 hz1 J hJ
    _ = ∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j *
          (∑ n ∈ Finset.Icc (A + 1) (A + (X : ℤ)),
            elementary (hitWeights H y z n) j) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro j _hj
              exact (Finset.mul_sum _ _ _).symm

/-- Second Bonferroni use, with the precise mean mu from the protected claim.-/
theorem meanWeight_truncation_upper (H : ℕ) (y z : ℝ)
    (hz0 : 0 < z) (hz1 : z < 1) (J : ℕ) (hJ : Even J) :
    (∑ j ∈ Finset.range (J + 1),
      (-1 : ℝ) ^ j * elementary (meanWeights H y z) j) ≤
      Real.exp (-((1 - z) * primeMass H y)) +
        ((1 - z) * primeMass H y) ^ (J + 1) /
          (Nat.factorial (J + 1) : ℝ) := by
  have h := even_sum_le_exp_add_tail (meanWeights H y z)
    (meanWeights_bounds H y z hz0 hz1) J hJ
  simpa only [meanWeights_sum] using h

end Erdos647Sieve
end

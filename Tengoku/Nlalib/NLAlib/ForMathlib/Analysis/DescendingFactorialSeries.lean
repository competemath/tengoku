import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.FiniteProductBounds
import Tengoku.Seed.Algebra.BigOperators.Field
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Logic.Equiv.Fin.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Descending-factorial series

Finite telescoping bounds give absolute summability of bounded-variation
Chebyshev coefficient envelopes.
-/
noncomputable section
open Finset
namespace NLAlib

/-- An inverse descending factorial is the difference of two adjacent inverse
shorter descending factorials, divided by their order. Source: focused BV reroute,
exact tail telescope.-/
theorem inv_cast_descFactorial_eq_sub {ν k : ℕ} (hν : 0 < ν) (hk : ν < k) :
    (k.descFactorial (ν + 1) : ℝ)⁻¹ =
      (((k - 1).descFactorial ν : ℝ)⁻¹ - (k.descFactorial ν : ℝ)⁻¹) / ν := by
  have hν0 : (ν : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hν
  have hA : ((k - 1).descFactorial ν : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.descFactorial_pos.mpr (by omega))
  have hB : (k.descFactorial ν : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.descFactorial_pos.mpr (by omega))
  have hC : (k.descFactorial (ν + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.descFactorial_pos.mpr (by omega))
  have hleft : (k.descFactorial (ν + 1) : ℝ) = k * ((k - 1).descFactorial ν : ℝ) := by
    have h := Nat.succ_descFactorial_succ (k - 1) ν
    rw [show k - 1 + 1 = k by omega] at h
    exact_mod_cast h
  have hright : (k.descFactorial (ν + 1) : ℝ) = ((k : ℝ) - ν) * (k.descFactorial ν : ℝ) := by
    rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub (by omega)]
  field_simp [hA, hB, hC, hν0]
  linear_combination -(k.descFactorial ν : ℝ) * hleft + ((k - 1).descFactorial ν : ℝ) * hright

/-- A finite descending-factorial tail has an exact positive remainder.
Source: focused BV reroute, exact tail telescope.-/
theorem sum_inv_cast_descFactorial_tail {ν n : ℕ} (hν : 0 < ν) (hn : ν ≤ n) (m : ℕ) :
    (∑ j ∈ range m, ((n + 1 + j).descFactorial (ν + 1) : ℝ)⁻¹) =
      (((n.descFactorial ν : ℝ)⁻¹ - ((n + m).descFactorial ν : ℝ)⁻¹) / ν) := by
  have hterm (j : ℕ) : ((n + 1 + j).descFactorial (ν + 1) : ℝ)⁻¹ =
      (((n + j).descFactorial ν : ℝ)⁻¹ - ((n + (j + 1)).descFactorial ν : ℝ)⁻¹) / ν := by
    rw [inv_cast_descFactorial_eq_sub hν (by omega), show n + 1 + j - 1 = n + j by omega,
      show n + 1 + j = n + (j + 1) by omega]
  simp_rw [hterm]
  rw [← sum_div, sum_range_sub']
  simp

/-- The inverse descending-factorial tail is summable, with bound
`1/(ν n(n−1)⋯(n−ν+1))`. Source: focused BV reroute, exact tail telescope.-/
theorem summable_inv_cast_descFactorial_tail {ν n : ℕ} (hν : 0 < ν) (hn : ν ≤ n) :
    Summable (fun j => ((n + 1 + j).descFactorial (ν + 1) : ℝ)⁻¹) := by
  apply summable_of_sum_range_le (c := (n.descFactorial ν : ℝ)⁻¹ / ν)
    (fun j => by positivity)
  intro m
  rw [sum_inv_cast_descFactorial_tail hν hn]
  exact div_le_div_of_nonneg_right (sub_le_self _ (by positivity)) (Nat.cast_nonneg ν)

/-- The summed inverse descending-factorial tail has the same explicit bound as
its finite partial sums. Source: focused BV reroute, exact tail telescope.-/
theorem tsum_inv_cast_descFactorial_tail_le {ν n : ℕ} (hν : 0 < ν) (hn : ν ≤ n) :
    (∑' j, ((n + 1 + j).descFactorial (ν + 1) : ℝ)⁻¹) ≤ (n.descFactorial ν : ℝ)⁻¹ / ν := by
  apply (summable_inv_cast_descFactorial_tail hν hn).tsum_le_of_sum_range_le
  intro m
  rw [sum_inv_cast_descFactorial_tail hν hn]
  exact div_le_div_of_nonneg_right (sub_le_self _ (by positivity)) (Nat.cast_nonneg ν)

/-- Inverse descending factorials are discretely convex above all their poles.
Source: finite midpoint form of the focused BV quadrature tail estimate.-/
theorem two_mul_inv_cast_descFactorial_le_adjacent {ν k : ℕ} (hk : ν + 1 < k) :
    2 * (k.descFactorial (ν + 1) : ℝ)⁻¹ ≤
      ((k - 1).descFactorial (ν + 1) : ℝ)⁻¹ + ((k + 1).descFactorial (ν + 1) : ℝ)⁻¹ := by
  have hA0 : ((k - 1).descFactorial (ν + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.descFactorial_pos.mpr (by omega))
  have hB0 : (k.descFactorial (ν + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.descFactorial_pos.mpr (by omega))
  have hC0 : ((k + 1).descFactorial (ν + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.descFactorial_pos.mpr (by omega))
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkR : (ν : ℝ) + 1 < k := by exact_mod_cast hk
  have hkν : (0 : ℝ) < k - ν - 1 := by linarith
  have hknu : (0 : ℝ) < k - ν := by linarith
  have hkp : (0 : ℝ) < k + 1 := by positivity
  have hA : ((k - 1).descFactorial (ν + 1) : ℝ) =
      ((k : ℝ) - ν - 1) * ((k - 1).descFactorial ν : ℝ) := by
    rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub (by omega),
      Nat.cast_sub (by omega), Nat.cast_one]
    ring
  have hB : (k.descFactorial (ν + 1) : ℝ) = k * ((k - 1).descFactorial ν : ℝ) := by
    have h := Nat.succ_descFactorial_succ (k - 1) ν
    rw [show k - 1 + 1 = k by omega] at h
    exact_mod_cast h
  have hC : ((k + 1).descFactorial (ν + 1) : ℝ) =
      (k + 1 : ℝ) * (k.descFactorial ν : ℝ) := by exact_mod_cast Nat.succ_descFactorial_succ k ν
  have hB' : (k.descFactorial (ν + 1) : ℝ) = ((k : ℝ) - ν) * (k.descFactorial ν : ℝ) := by
    rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub (by omega)]
  have hleft : (k : ℝ) * ((k - 1).descFactorial (ν + 1) : ℝ) =
      ((k : ℝ) - ν - 1) * (k.descFactorial (ν + 1) : ℝ) := by rw [hA, hB]; ring
  have hright : ((k : ℝ) - ν) * ((k + 1).descFactorial (ν + 1) : ℝ) =
      (k + 1 : ℝ) * (k.descFactorial (ν + 1) : ℝ) := by rw [hC, hB']; ring
  have hAinv : ((k - 1).descFactorial (ν + 1) : ℝ)⁻¹ =
      (k : ℝ) / (k - ν - 1) * (k.descFactorial (ν + 1) : ℝ)⁻¹ := by
    field_simp [hA0, hB0, ne_of_gt hkν]
    linear_combination -hleft
  have hCinv : ((k + 1).descFactorial (ν + 1) : ℝ)⁻¹ =
      ((k : ℝ) - ν) / (k + 1) * (k.descFactorial (ν + 1) : ℝ)⁻¹ := by
    field_simp [hC0, hB0, ne_of_gt hkp]
    linear_combination -hright
  have hrat : (2 : ℝ) ≤ (k : ℝ) / (k - ν - 1) + ((k : ℝ) - ν) / (k + 1) := by
    have hid : (k : ℝ) / (k - ν - 1) + ((k : ℝ) - ν) / (k + 1) - 2 =
        ((ν : ℝ) + 1) * (ν + 2) / ((k - ν - 1) * (k + 1)) := by
      field_simp [ne_of_gt hkν, ne_of_gt hkp]
      ring
    have hnon : 0 ≤ ((ν : ℝ) + 1) * (ν + 2) / ((k - ν - 1) * (k + 1)) := by positivity
    rw [← hid] at hnon
    linarith
  rw [hAinv, hCinv, ← add_mul]
  exact mul_le_mul_of_nonneg_right hrat (by positivity)

/-- Inverse descending factorials of order at least two are summable; their finitely
many zero-denominator terms are totalized to zero. Source: exact tail telescope.-/
theorem summable_inv_cast_descFactorial {ν : ℕ} (hν : 0 < ν) :
    Summable (fun k : ℕ => (k.descFactorial (ν + 1) : ℝ)⁻¹) := by
  rw [← summable_nat_add_iff (ν + 1)]
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    summable_inv_cast_descFactorial_tail hν (le_refl ν)

end NLAlib

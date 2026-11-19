import Tengoku.Erdos278.Erdos278.RadixModel
import Tengoku.Erdos278.Erdos278.PartitionDP
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos278

open Finset

/-- Number of digit coordinates, including coordinates used by only one vertex.-/
def radixCoordinateCount {r : ℕ} {β : Type*} [Fintype β]
    (e : Fin r → β → ℕ) : ℕ := ∑ j, univ.sup (fun i => e i j)

theorem radix_coordinate_count_le_sum {r : ℕ} {β : Type*} [Fintype β]
    (e : Fin r → β → ℕ) : radixCoordinateCount e ≤ ∑ i, ∑ j, e i j := by
  calc
    _ ≤ ∑ j, ∑ i, e i j := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sup_le_iff.mpr (fun i hi =>
        Finset.single_le_sum (f := fun i => e i j) (fun _ _ => Nat.zero_le _) hi)
    _ = _ := Finset.sum_comm

theorem radix_exponent_sum_le_log {β : Type*} [Fintype β]
    (b e : β → ℕ) (hb : ∀ j, 2 ≤ b j)
    (hc : Pairwise (fun j k => (b j).Coprime (b k))) :
    (∑ j, e j) ≤ Nat.log 2 (radixModulus b e) := by
  apply Nat.le_log_of_pow_le (by decide)
  rw [radix_modulus_eq_product b e hc, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod' (fun j _ => Nat.pow_le_pow_left (hb j) _)

/-- The coordinate count is bounded by the total binary logarithmic input size.
This counts combinatorial objects; it is not a machine-time cost model.-/
theorem radix_coordinate_count_le_bit_bound {r : ℕ} {β : Type*} [Fintype β]
    (b : β → ℕ) (e : Fin r → β → ℕ) (hb : ∀ j, 2 ≤ b j)
    (hc : Pairwise (fun j k => (b j).Coprime (b k))) :
    radixCoordinateCount e ≤ ∑ i, Nat.clog 2 (radixModulus b (e i)) := by
  apply (radix_coordinate_count_le_sum e).trans
  exact Finset.sum_le_sum (fun i _ =>
    (radix_exponent_sum_le_log b (e i) hb hc).trans (Nat.log_le_clog _ _))

/-- Total candidate transitions before deduplication, for any finite schedule.-/
theorem separation_total_candidate_bound {r : ℕ} (d : ℕ)
    (V : ℕ → Finset (Fin r)) (b : ℕ → ℕ) :
    (∑ t ∈ range d,
      (separationDP (fun k => localSeparationMasks (V k) (b k)) t ×ˢ
        localSeparationMasks (V t) (b t)).card) ≤
      d * (2 ^ (r * (r-1) / 2) * r ^ r) := by
  calc
    _ ≤ ∑ _t ∈ range d, 2 ^ (r * (r-1) / 2) * r ^ r :=
      Finset.sum_le_sum (fun t _ => separation_step_candidate_bound _ _ _)
    _ = _ := by simp

theorem separation_transition_exponential_bound (r : ℕ) :
    2 ^ (r * (r-1) / 2) * r ^ r ≤ 2 ^ (2 * r * r) := by
  have hr : r ^ r ≤ 2 ^ (r * r) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n := r))) r
  have hq : r * (r-1) / 2 ≤ r * r :=
    (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left r (Nat.sub_le _ _))
  calc
    _ ≤ 2 ^ (r * (r-1) / 2) * 2 ^ (r * r) := Nat.mul_le_mul_left _ hr
    _ = 2 ^ (r * (r-1) / 2 + r * r) := (pow_add _ _ _).symm
    _ ≤ 2 ^ (2 * r * r) := Nat.pow_le_pow_right (by decide) (by nlinarith)

/-- A fully explicit exponential bound on transition count, with no time model.-/
theorem separation_total_exponential_bound {r : ℕ} (d : ℕ)
    (V : ℕ → Finset (Fin r)) (b : ℕ → ℕ) :
    (∑ t ∈ range d,
      (separationDP (fun k => localSeparationMasks (V k) (b k)) t ×ˢ
        localSeparationMasks (V t) (b t)).card) ≤ d * 2 ^ (2 * r * r) :=
  (separation_total_candidate_bound d V b).trans
    (Nat.mul_le_mul_left d (separation_transition_exponential_bound r))

end Erdos278

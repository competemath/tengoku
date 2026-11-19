import Tengoku.Erdos278.Erdos278.Model
import Tengoku.Seed.Algebra.BigOperators.Intervals

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos278

open Finset

def pairIndexEquiv (r : ℕ) : PairIndex r ≃ (Σ j : Fin r, Fin j.val) where
  toFun e := ⟨e.1.2, ⟨e.1.1.val, e.2⟩⟩
  invFun e := ⟨(⟨e.2.val, e.2.isLt.trans e.1.isLt⟩, e.1), e.2.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem twice_pair_count (r : ℕ) :
    2 * Fintype.card (PairIndex r) = r * (r - 1) := by
  rw [Fintype.card_congr (pairIndexEquiv r), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have hsum : (∑ j : Fin r, j.val) = ∑ j ∈ range r, j :=
    Fin.sum_univ_eq_sum_range (fun j : ℕ => j) r
  rw [hsum, Nat.mul_comm 2]
  exact Finset.sum_range_id_mul_two r

/-- The free x coordinates, one quotient and one binary coordinate per
unordered pair total exactly r²-1 for a nonempty family.-/
theorem integer_variable_count {r : ℕ} (i₀ : Fin r) :
    ((univ : Finset (Fin r)).erase i₀).card +
      Fintype.card (PairIndex r) + Fintype.card (PairIndex r) = r^2 - 1 := by
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le i₀.val) i₀.isLt
  have hp := twice_pair_count r
  simp only [Finset.card_erase_of_mem (mem_univ i₀), Finset.card_univ, Fintype.card_fin]
  have hm : r - 1 + 1 = r := by omega
  have hsq : 1 ≤ r^2 := by nlinarith
  have hsqeq : r^2 - 1 + 1 = r^2 := Nat.sub_add_cancel hsq
  nlinarith

/-- At most 2m vertices are incident to a set of m interacting pairs.-/
theorem interacting_vertices_bound {r : ℕ} (edges : Finset (PairIndex r)) :
    (edges.biUnion (fun e => {e.1.1, e.1.2})).card ≤ 2 * edges.card := by
  calc
    _ ≤ ∑ e ∈ edges, ({e.1.1, e.1.2} : Finset (Fin r)).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ edges, 2 := Finset.sum_le_sum (fun e _ => by
      have hne : e.1.1 ≠ e.1.2 := ne_of_lt e.2
      simp [hne])
    _ = 2 * edges.card := by simp [Nat.mul_comm]

theorem objective_coefficients_integral {r : ℕ} (n : Fin r → ℕ)
    (hn : ∀ i, 0 < n i) (S : CliqueIndex r) :
    ∃ k : ℤ, (((univ : Finset (Fin r)).lcm n : ℕ) : ℚ) *
      ((-1 : ℚ) ^ (S.1.card + 1) / (S.1.lcm n : ℕ)) = k := by
  have hdiv : S.1.lcm n ∣ (univ : Finset (Fin r)).lcm n :=
    Finset.lcm_mono (subset_univ _)
  obtain ⟨k, hk⟩ := hdiv
  have hnonzero : ((S.1.lcm n : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Finset.lcm_ne_zero_iff.mpr (fun i _ => (hn i).ne')
  refine ⟨(-1 : ℤ) ^ (S.1.card + 1) * k, ?_⟩
  rw [hk]
  push_cast
  field_simp

end Erdos278

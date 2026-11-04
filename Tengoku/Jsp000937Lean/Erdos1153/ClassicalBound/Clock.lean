import Tengoku.Jsp000937Lean.Erdos1153.ClassicalBound.Sharp
import Tengoku.Seed.Algebra.Order.BigOperators.Ring.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pair transport and defect bookkeeping for a classical clock argument

The sharp classical proof needs more than the weighted Bernstein estimate:
it must retain the slack in the actual nodal derivatives when the nodes are
badly distributed.  This file proves the pairwise identities that permit
that bookkeeping without introducing an unproved phase coordinate.
-/

namespace Erdos1153
namespace ClassicalBound

open Polynomial

noncomputable section

/-- Exact transport identity between two cardinal values at the same point.

All derivative and separation factors are retained.  Thus multiplying such
identities over paired indices can cancel reciprocal derivative ratios before
any estimates are made.
@isnad1 id=eq.2h5v.s7.e362692c7528 from=translated src=- shape=bd69cf11 vocab=39cfa38a
-/
lemma abs_lagrangeFundamental_mul_distance_eq_pair_transport {n : ℕ}
    (nodes : NodeFamily n) {j k : Fin n} (hjk : j ≠ k) {t : ℝ}
    (ht : ∀ i : Fin n, t ≠ nodes.point i) :
    |lagrangeFundamental nodes k t| * |t - nodes.point k| =
      |lagrangeFundamental nodes j t| *
        |(lagrangeBasis nodes k).derivative.eval (nodes.point j)| *
          |nodes.point j - nodes.point k| * |t - nodes.point j| := by
  rw [abs_lagrangeFundamental_eq_nodalPolynomial nodes k (ht k),
    abs_lagrangeFundamental_eq_nodalPolynomial nodes j (ht j),
    derivative_lagrangeBasis_eval_of_ne nodes hjk]
  simp only [abs_mul, abs_inv]
  have hjderiv :
      |(nodalPolynomial nodes).derivative.eval (nodes.point j)| ≠ 0 :=
    abs_ne_zero.mpr (derivative_nodalPolynomial_eval_node_ne_zero nodes j)
  have hkderiv :
      |(nodalPolynomial nodes).derivative.eval (nodes.point k)| ≠ 0 :=
    abs_ne_zero.mpr (derivative_nodalPolynomial_eval_node_ne_zero nodes k)
  have htj : |t - nodes.point j| ≠ 0 :=
    abs_ne_zero.mpr (sub_ne_zero.mpr (ht j))
  have htk : |t - nodes.point k| ≠ 0 :=
    abs_ne_zero.mpr (sub_ne_zero.mpr (ht k))
  have hjkabs : |nodes.point j - nodes.point k| ≠ 0 :=
    abs_ne_zero.mpr (sub_ne_zero.mpr (nodes.point_ne hjk))
  field_simp

/-- Left endpoint index of an adjacent pair, local to the clock module.-/
def clockLeftIndex {n : ℕ} (g : Fin (n - 1)) : Fin n :=
  ⟨g.val, by omega⟩

/-- Right endpoint index of an adjacent pair, local to the clock module.-/
def clockRightIndex {n : ℕ} (g : Fin (n - 1)) : Fin n :=
  ⟨g.val + 1, by omega⟩

/--
@isnad1 id=eq.0h2v.s5.085d06ffee43 from=translated src=- shape=ef12c50a vocab=d23d40c0
-/
@[simp]
lemma clockLeftIndex_val {n : ℕ} (g : Fin (n - 1)) :
    (clockLeftIndex g).val = g.val :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.65364cb000fd from=translated src=- shape=6cf84995 vocab=3d7667ec
-/
@[simp]
lemma clockRightIndex_val {n : ℕ} (g : Fin (n - 1)) :
    (clockRightIndex g).val = g.val + 1 :=
  rfl

/--
@isnad1 id=lt.0h2v.s4.609e1aa87287 from=translated src=- shape=da863e3e vocab=532756dd
-/
lemma clockLeftIndex_lt_rightIndex {n : ℕ} (g : Fin (n - 1)) :
    clockLeftIndex g < clockRightIndex g := by
  simp [Fin.lt_def]

/-- Length of an adjacent gap in an ordered node family.-/
def clockGap {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) : ℝ :=
  nodes.point (clockRightIndex g) - nodes.point (clockLeftIndex g)

/--
@isnad1 id=lt.0h3v.s5.b1159d586f20 from=translated src=- shape=d29793a2 vocab=60f56b86
-/
lemma clockGap_pos {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    0 < clockGap nodes g := by
  exact sub_pos.mpr (nodes.point_lt (clockLeftIndex_lt_rightIndex g))

/-- Adjacent clock gaps telescope exactly between the extreme nodes.
@isnad1 id=eq.1h2v.s6.a7ad62c65614 from=translated src=- shape=381540c9 vocab=48bdb8e9
-/
lemma sum_clockGap_eq_extreme_difference {n : ℕ} (nodes : OrderedNodes n)
    (hn : 2 ≤ n) :
    (∑ g : Fin (n - 1), clockGap nodes g) =
      nodes.point ⟨n - 1, by omega⟩ - nodes.point ⟨0, by omega⟩ := by
  let f : ℕ → ℝ := fun i ↦
    nodes.point ⟨min i (n - 1), by omega⟩
  rw [Finset.sum_fin_eq_sum_range]
  have htel := Finset.sum_range_sub f (n - 1)
  rw [show f (n - 1) = nodes.point ⟨n - 1, by omega⟩ by simp [f],
    show f 0 = nodes.point ⟨0, by omega⟩ by simp [f]] at htel
  rw [← htel]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < n - 1 := Finset.mem_range.mp hi
  rw [dite_eq_left hi']
  simp only [clockGap, clockRightIndex, clockLeftIndex, f]
  congr 2
  · apply Fin.ext
    exact (Nat.min_eq_left (by omega)).symm
  · apply Fin.ext
    exact (Nat.min_eq_left hi'.le).symm

/-- Since all nodes lie in `[-1,1]`, the total adjacent clock length is at
most two.
@isnad1 id=le.0h2v.s6.50e378ae43ff from=translated src=- shape=c397b48f vocab=1d0e6bc8
-/
lemma sum_clockGap_le_two {n : ℕ} (nodes : OrderedNodes n) :
    (∑ g : Fin (n - 1), clockGap nodes g) ≤ 2 := by
  by_cases hn : 2 ≤ n
  · rw [sum_clockGap_eq_extreme_difference nodes hn]
    calc
      nodes.point ⟨n - 1, by omega⟩ - nodes.point ⟨0, by omega⟩ ≤
          1 - (-1 : ℝ) :=
        sub_le_sub (nodes.le_one _) (nodes.neg_one_le _)
      _ = 2 := by norm_num
  · interval_cases n <;> simp

/-- Pure finite arithmetic behind the cluster side of the clock dichotomy:
positive gaps of total length at most two have reciprocal mass at least
`m² / 2`.
@isnad1 id=le.2h2v.s6.a1589c2c716c from=translated src=- shape=01d4a9d9 vocab=32cd1795
-/
lemma sq_card_div_two_le_sum_inv_of_sum_le_two {m : ℕ}
    (gap : Fin m → ℝ) (hgap : ∀ i, 0 < gap i)
    (hsum : (∑ i : Fin m, gap i) ≤ 2) :
    (m : ℝ) ^ 2 / 2 ≤ ∑ i : Fin m, (gap i)⁻¹ := by
  by_cases hm : m = 0
  · subst m
    simp
  have hsumpos : 0 < ∑ i : Fin m, gap i := by
    exact Finset.sum_pos' (fun i _ ↦ (hgap i).le)
      ⟨⟨0, Nat.pos_of_ne_zero hm⟩, Finset.mem_univ _, hgap _⟩
  have htitu := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset (Fin m))
    (fun _ ↦ (1 : ℝ)) (g := gap) (fun i _ ↦ hgap i)
  have hcard : (∑ _i : Fin m, (1 : ℝ)) = (m : ℝ) := by simp
  have hone : (∑ i : Fin m, (1 : ℝ) ^ 2 / gap i) =
      ∑ i : Fin m, (gap i)⁻¹ := by
    apply Finset.sum_congr rfl
    intro i _
    simp [div_eq_mul_inv]
  rw [hcard, hone] at htitu
  calc
    (m : ℝ) ^ 2 / 2 ≤
        (m : ℝ) ^ 2 / ∑ i : Fin m, gap i := by
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hsumpos).2
      exact mul_le_mul_of_nonneg_left hsum (sq_nonneg (m : ℝ))
    _ ≤ ∑ i : Fin m, (gap i)⁻¹ := htitu

end

end ClassicalBound
end Erdos1153

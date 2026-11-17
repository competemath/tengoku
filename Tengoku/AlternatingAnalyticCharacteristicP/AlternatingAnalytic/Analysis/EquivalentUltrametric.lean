import Tengoku.Seed.Analysis.Normed.Module.Seminorm.Basic
import Tengoku.Seed.Analysis.Normed.Module.Basic
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
import Tengoku.Seed.Algebra.Order.Archimedean.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A criterion excluding equivalent ultrametric norms

An equivalent ultrametric norm bounds all finite sums of vectors in the unit ball
uniformly, so unit vectors with unbounded partial sums rule it out. This is the last
step of the block-wedge argument of Proposition E.1.
-/

namespace AlternatingAnalytic

variable (K F : Type*) [NormedField K] [NormedAddCommGroup F] [NormedSpace K F]

/-- `F` has an ultrametric seminorm equivalent to its norm (hence a norm).-/
def HasEquivalentUltrametricNorm : Prop :=
  ∃ q : Seminorm K F,
    (∀ x y, q (x + y) ≤ max (q x) (q y)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ x, ‖x‖ ≤ C * q x) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ x, q x ≤ C * ‖x‖)

variable {K F}

/-- An equivalent ultrametric norm uniformly bounds finite sums in the unit ball.-/
theorem HasEquivalentUltrametricNorm.bounded_unit_sums
    (h : HasEquivalentUltrametricNorm K F) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (s : Finset ι) (v : ι → F),
      (∀ i ∈ s, ‖v i‖ ≤ 1) → ‖∑ i ∈ s, v i‖ ≤ C := by
  rcases h with ⟨q, hq, ⟨A, hA, hlower⟩, ⟨B, hB, hupper⟩⟩
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  intro ι s v hv
  have hsum : q (∑ i ∈ s, v i) ≤ B := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using hB.le
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      apply (hq _ _).trans
      refine max_le ?_ (ih (fun j hj => hv j (Finset.mem_insert_of_mem hj)))
      exact (hupper _).trans ((mul_le_mul_of_nonneg_left
        (hv i (Finset.mem_insert_self i s)) hB.le).trans_eq (mul_one B))
  exact (hlower _).trans (mul_le_mul_of_nonneg_left hsum hA.le)

/-- Unbounded partial sums of unit vectors exclude every equivalent ultrametric norm.-/
theorem not_hasEquivalentUltrametricNorm_of_unbounded_partial_sums
    (v : ℕ → F) (hv : ∀ n, ‖v n‖ ≤ 1)
    (hgrowth : ∀ B : ℝ, ∃ N : ℕ, B < ‖∑ i ∈ Finset.range N, v i‖) :
    ¬ HasEquivalentUltrametricNorm K F := by
  intro h
  obtain ⟨C, _, hC⟩ := h.bounded_unit_sums
  obtain ⟨N, hN⟩ := hgrowth C
  exact (not_lt_of_ge (hC (Finset.range N) v (fun i _ => hv i))) hN

/-- Partial sums of unit vectors growing at least linearly exclude an equivalent
ultrametric norm.-/
theorem not_hasEquivalentUltrametricNorm_of_linear_growth
    (v : ℕ → F) (hv : ∀ n, ‖v n‖ ≤ 1) {M : ℝ} (hM : 0 < M)
    (hgrowth : ∀ N : ℕ, (N : ℝ) / M ≤ ‖∑ i ∈ Finset.range N, v i‖) :
    ¬ HasEquivalentUltrametricNorm K F := by
  apply not_hasEquivalentUltrametricNorm_of_unbounded_partial_sums v hv
  intro B
  obtain ⟨N, hN⟩ := exists_nat_gt (B * M)
  exact ⟨N, ((lt_div_iff₀ hM).2 hN).trans_le (hgrowth N)⟩

end AlternatingAnalytic

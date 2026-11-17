import Tengoku.Seed.Data.Complex.Basic
import Tengoku.Seed.Data.Set.Countable
import Tengoku.Seed.Order.Bounds.Basic
import Tengoku.Seed.Data.Fintype.Lattice
import Tengoku.Seed.Data.Set.Finite.Lattice

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Complex_exists_forall_not_countable_setOf_re_gt_mem_of_finite.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Complex_exists_forall_not_countable_setOf_re_gt_mem_of_finite

theorem solution
    {ι : Type} [Finite ι] (S : ι → Set ℂ)
    (h : ∀ σ' : ℝ, ¬ Set.Countable {s : ℂ | σ' < s.re ∧ ∃ i, s ∈ S i}) :
    ∃ i, ∀ σ' : ℝ, ¬ Set.Countable {s : ℂ | σ' < s.re ∧ s ∈ S i} := by
  classical
  by_contra hcon
  push Not at hcon

  choose σ hσ using hcon

  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ i, σ i ≤ M := by
    obtain ⟨M, hM⟩ := (Set.range σ).toFinite.bddAbove
    exact ⟨M, fun i => hM (Set.mem_range_self i)⟩
  haveI : Countable ι := Finite.to_countable
  apply h M
  have hsub : {s : ℂ | M < s.re ∧ ∃ i, s ∈ S i} ⊆ ⋃ i, {s : ℂ | σ i < s.re ∧ s ∈ S i} := by
    rintro s ⟨hs, i, hi⟩
    exact Set.mem_iUnion.2 ⟨i, lt_of_le_of_lt (hM i) hs, hi⟩
  exact (Set.countable_iUnion fun i => hσ i).mono hsub

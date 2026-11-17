import Tengoku.Seed.Topology.ContinuousMap.Bounded.Normed
import Tengoku.Seed.Data.Int.ConditionallyCompleteOrder
import Tengoku.Seed.Algebra.Order.Archimedean.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Discrete sup norms are attained

A bounded function whose nonzero values have norms in `e ^ ℤ`, `e > 1`, attains its
supremum norm. Used for sequence spaces over a discretely valued field.
-/

open scoped BoundedContinuousFunction

namespace AlternatingAnalytic

variable {S Y : Type*} [TopologicalSpace S] [NormedAddCommGroup Y]

/-- A nonzero bounded function with nonzero norms in `e ^ ℤ`, `e > 1`, attains its
norm, with no compactness of the index space.
@isnad1 id=ex.3h4v.s7.62fd1ee803b9 from=translated src=- shape=461513bc vocab=0af0ef88
-/
theorem exists_norm_eq_of_discrete (e : ℝ) (he : 1 < e)
    (hdiscrete : ∀ y : Y, y ≠ 0 → ∃ n : ℤ, ‖y‖ = e ^ n)
    (f : S →ᵇ Y) (hf : f ≠ 0) : ∃ s : S, f s ≠ 0 ∧ ‖f‖ = ‖f s‖ := by
  classical
  have hnonzero : ∃ s, f s ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    ext s
    exact h s
  let exponents : Set ℤ := {n | ∃ s, f s ≠ 0 ∧ ‖f s‖ = e ^ n}
  have hne : exponents.Nonempty := by
    obtain ⟨s, hs⟩ := hnonzero
    obtain ⟨n, hn⟩ := hdiscrete (f s) hs
    exact ⟨n, s, hs, hn⟩
  obtain ⟨N, _, hN⟩ := exists_nat_pow_near (le_max_left 1 ‖f‖) he
  have hbound : ‖f‖ ≤ e ^ (N + 1) := (le_max_right 1 ‖f‖).trans hN.le
  have hbdd : BddAbove exponents := by
    refine ⟨(N + 1 : ℕ), ?_⟩
    rintro n ⟨s, hs, hn⟩
    apply (zpow_le_zpow_iff_right₀ he).1
    calc
      e ^ n = ‖f s‖ := hn.symm
      _ ≤ ‖f‖ := f.norm_coe_le_norm s
      _ ≤ e ^ ((N + 1 : ℕ) : ℤ) := by simpa only [zpow_natCast] using hbound
  obtain ⟨s, hs, hn⟩ := Int.csSup_mem hne hbdd
  refine ⟨s, hs, le_antisymm ?_ (f.norm_coe_le_norm s)⟩
  apply (BoundedContinuousFunction.norm_le (norm_nonneg (f s))).2
  intro t
  by_cases ht : f t = 0
  · simp [ht]
  · obtain ⟨m, hm⟩ := hdiscrete (f t) ht
    rw [hm, hn]
    exact (zpow_le_zpow_iff_right₀ he).2 (le_csSup hbdd ⟨t, ht, hm⟩)

end AlternatingAnalytic

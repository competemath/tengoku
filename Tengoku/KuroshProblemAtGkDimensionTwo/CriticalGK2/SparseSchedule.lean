import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sparse scheduling on actual integer scales

This module proves the existence of all scale choices, from divergence of the
given real envelope and arbitrary finite operation costs.
Stages are numbered from zero; stage `j` corresponds to manuscript stage `j+1`.
-/

namespace CriticalGK2

/-- The exact eventual lower-bound meaning of a real envelope tending to infinity.-/
def EnvelopeDiverges (Λ : ℕ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → M ≤ Λ n

/-- The support budget before the first operation is two.-/
def supportBudget (κ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 2
  | j + 1 => 2 ^ κ j * supportBudget κ j

/-- A convenient intentionally loose scale bound, proved without evaluating huge powers.
@isnad1 id=le.0h1v.s4.7a35469a2be0 from=translated src=- shape=e17d9afa vocab=74f5fafa
-/
theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hp : 0 < (2 : ℕ) ^ n := pow_pos (by norm_num) _
      rw [pow_succ]
      omega

/-- All three scale constraints can be paid at once.
@isnad1 id=ex.1h5v.s6.cf82a8aaaad0 from=translated src=- shape=f1e1ace1 vocab=78a590a1
-/
theorem exists_next_scale (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ)
    (C prev duration j : ℕ) :
    ∃ h : ℕ, prev + duration < h ∧
      C ^ (j + 1) ≤ 2 ^ h ∧ (C : ℝ) ^ 2 ≤ Λ (2 ^ h) := by
  obtain ⟨N, hN⟩ := hΛ ((C : ℝ) ^ 2)
  let h := prev + duration + C ^ (j + 1) + N + 1
  refine ⟨h, ?_, ?_, ?_⟩
  · dsimp [h]
    omega
  · have hC : C ^ (j + 1) ≤ h := by dsimp [h]; omega
    exact hC.trans (nat_le_two_pow h)
  · apply hN
    have hn : N ≤ h := by dsimp [h]; omega
    exact hn.trans (nat_le_two_pow h)

noncomputable def nextScale (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ)
    (C prev duration j : ℕ) : ℕ :=
  Classical.choose (exists_next_scale Λ hΛ C prev duration j)

/--
@isnad1 id=and.1h5v.s7.78d5c2fe14f2 from=translated src=- shape=eef36e03 vocab=141802d6
-/
theorem nextScale_spec (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ)
    (C prev duration j : ℕ) :
    prev + duration < nextScale Λ hΛ C prev duration j ∧
    C ^ (j + 1) ≤ 2 ^ nextScale Λ hΛ C prev duration j ∧
    (C : ℝ) ^ 2 ≤ Λ (2 ^ nextScale Λ hΛ C prev duration j) :=
  Classical.choose_spec (exists_next_scale Λ hΛ C prev duration j)

/-- Recursive heights use the previously completed layer as their next lower bound.-/
noncomputable def scaleHeight (κ duration : ℕ → ℕ)
    (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) : ℕ → ℕ
  | 0 => nextScale Λ hΛ (supportBudget κ 1) 0 0 0
  | j + 1 => nextScale Λ hΛ (supportBudget κ (j + 2))
      (scaleHeight κ duration Λ hΛ j) (duration j) (j + 1)

/--
@isnad1 id=lt.1h4v.s5.7e36a54c1db9 from=translated src=- shape=5a26bc47 vocab=b0101e6b
-/
theorem scaleHeight_separated (κ duration : ℕ → ℕ)
    (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) (j : ℕ) :
    scaleHeight κ duration Λ hΛ j + duration j <
      scaleHeight κ duration Λ hΛ (j + 1) := by
  exact (nextScale_spec Λ hΛ (supportBudget κ (j + 2))
    (scaleHeight κ duration Λ hΛ j) (duration j) (j + 1)).1

/--
@isnad1 id=le.1h4v.s6.59501af849b3 from=translated src=- shape=fe61b3cb vocab=2b212720
-/
theorem scaleHeight_budget_pow (κ duration : ℕ → ℕ)
    (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) (j : ℕ) :
    supportBudget κ (j + 1) ^ (j + 1) ≤
      2 ^ scaleHeight κ duration Λ hΛ j := by
  cases j with
  | zero => exact (nextScale_spec Λ hΛ (supportBudget κ 1) 0 0 0).2.1
  | succ j =>
      exact (nextScale_spec Λ hΛ (supportBudget κ (j + 2))
        (scaleHeight κ duration Λ hΛ j) (duration j) (j + 1)).2.1

/--
@isnad1 id=strictmo.1h3v.s4.81876a7e4fc3 from=translated src=- shape=d4214246 vocab=d477dc4f
-/
theorem scaleHeight_strictMono (κ duration : ℕ → ℕ)
    (Λ : ℕ → ℝ) (hΛ : EnvelopeDiverges Λ) :
    StrictMono (scaleHeight κ duration Λ hΛ) := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hs := scaleHeight_separated κ duration Λ hΛ j
  omega

end CriticalGK2

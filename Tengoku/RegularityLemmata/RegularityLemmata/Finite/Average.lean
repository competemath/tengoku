/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Finite.Density
import Tengoku.RegularityLemmata.RegularityLemmata.Finite.RectKernel
import Tengoku.Seed.Algebra.BigOperators.Field

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# One-variable finite averages

`averageOn S φ` is the average of `φ : α → ℝ` over a finset, guard-free with value `0` on the
empty set (via `x / 0 = 0`), mirroring `densityOn`'s convention. `densityOn` is its indicator
shadow (`averageOn_indicator`), and the two-variable `rectAverageCount` factors through it in
both orders (`rectAverageCount_eq_averageOn_left`/`_right`), so kernel averages, fiber
averages, and densities share one vocabulary.

The mass form `averageOn_mul_card` is the restriction primitive: statements about sums
restrict along subsets, and the average forms are recovered by dividing.
-/

namespace RegularityLemmata

variable {α X Y : Type*} {S : Finset α} {φ ψ : α → ℝ} {c : ℝ}

/-- The average of `φ` over `S`; `0` on the empty set via `x / 0 = 0`.-/
noncomputable def averageOn (S : Finset α) (φ : α → ℝ) : ℝ := (∑ x ∈ S, φ x) / S.card

/--
@isnad1 id=eq.0h2v.s4.84357cd8d3dc from=translated src=- shape=f33f5fe1 vocab=67339d4f
-/
@[simp] theorem averageOn_empty (φ : α → ℝ) : averageOn (∅ : Finset α) φ = 0 := by
  simp [averageOn]

/-- The mass form, guard-free: on the empty set both sides are `0`.
@isnad1 id=eq.0h3v.s5.7cb4f7124742 from=translated src=- shape=8c0ac2e4 vocab=42de67cf
-/
theorem averageOn_mul_card (S : Finset α) (φ : α → ℝ) :
    averageOn S φ * S.card = ∑ x ∈ S, φ x := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  · have h0 : (S.card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hS
    rw [averageOn, div_mul_cancel₀ _ h0]

/--
@isnad1 id=eq.1h3v.s4.adfa5fb58d67 from=translated src=- shape=d2f128d9 vocab=bb91fc99
-/
theorem averageOn_const (hS : S.Nonempty) (c : ℝ) : averageOn S (fun _ ↦ c) = c := by
  have h0 : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  rw [averageOn, Finset.sum_const, nsmul_eq_mul, mul_comm, mul_div_assoc, div_self h0,
    mul_one]

/--
@isnad1 id=eq.1h4v.s5.62b2cc6b8e83 from=translated src=- shape=7ff4b184 vocab=91a84ed5
-/
theorem averageOn_congr (h : ∀ x ∈ S, φ x = ψ x) : averageOn S φ = averageOn S ψ := by
  rw [averageOn, averageOn, Finset.sum_congr rfl h]

/--
@isnad1 id=le.1h3v.s5.1b26c8050120 from=translated src=- shape=822ee102 vocab=4b97cda0
-/
theorem averageOn_nonneg (h : ∀ x ∈ S, 0 ≤ φ x) : 0 ≤ averageOn S φ :=
  div_nonneg (Finset.sum_nonneg h) (Nat.cast_nonneg _)

/-- Upper bound from a pointwise bound; the nonnegativity of the bound absorbs the empty
set's junk value `0`.
@isnad1 id=le.2h4v.s5.7a116b45faf8 from=translated src=- shape=75615d9e vocab=4b97cda0
-/
theorem averageOn_le_of_le (h : ∀ x ∈ S, φ x ≤ c) (hc : 0 ≤ c) : averageOn S φ ≤ c := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simpa using hc
  · have h0 : (0 : ℝ) < (S.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hS
    rw [averageOn, div_le_iff₀ h0]
    calc ∑ x ∈ S, φ x ≤ ∑ _x ∈ S, c := Finset.sum_le_sum h
      _ = c * S.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- A `[0,1]`-valued function has a `[0,1]`-valued average, the empty set included.
@isnad1 id=mem.1h3v.s6.ce1482bc2348 from=translated src=- shape=3f152fe2 vocab=0e338345
-/
theorem averageOn_mem_Icc (h : ∀ x ∈ S, φ x ∈ Set.Icc (0 : ℝ) 1) :
    averageOn S φ ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨averageOn_nonneg fun x hx ↦ (h x hx).1, averageOn_le_of_le (fun x hx ↦ (h x hx).2) one_pos.le⟩

/-- **`densityOn` is the indicator shadow of `averageOn`.**
@isnad1 id=eq.0h3v.s5.5a6781724e26 from=translated src=- shape=c44b641f vocab=a66cdd03
-/
theorem averageOn_indicator (S : Finset α) (p : α → Prop) [DecidablePred p] :
    averageOn S (fun x ↦ if p x then 1 else 0) = densityOn S p := by
  rw [averageOn, densityOn, Finset.sum_boole]

/-! ### Rectangle-fiber bridges

The counting kernel average factors through `averageOn` in both orders, guard-free: an empty
side makes both sides `0`. -/

/-- Outer average over the left carrier of inner fiber averages.
@isnad1 id=eq.0h5v.s5.71803fe4212d from=translated src=- shape=a21ef4ee vocab=8425e7a0
-/
theorem rectAverageCount_eq_averageOn_left (f : RectKernel X Y) (A : Finset X)
    (B : Finset Y) :
    rectAverageCount f A B = averageOn A fun x ↦ averageOn B (f x) := by
  simp only [rectAverageCount, rectAverage, rectSum, finsetMass, one_mul, averageOn,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [← Finset.sum_div, div_div, mul_comm ((B.card : ℝ)) _]

/-- Outer average over the right carrier of inner fiber averages.
@isnad1 id=eq.0h5v.s5.1a96fa5e424b from=translated src=- shape=d703fa96 vocab=8425e7a0
-/
theorem rectAverageCount_eq_averageOn_right (f : RectKernel X Y) (A : Finset X)
    (B : Finset Y) :
    rectAverageCount f A B = averageOn B fun y ↦ averageOn A fun x ↦ f x y := by
  simp only [rectAverageCount, rectAverage, rectSum, finsetMass, one_mul, averageOn,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_comm, ← Finset.sum_div, div_div]

/-! ### Tests and adversarial examples -/

section Tests

-- The empty set: the junk value is `0`, consistent with `densityOn`.

end Tests

end RegularityLemmata

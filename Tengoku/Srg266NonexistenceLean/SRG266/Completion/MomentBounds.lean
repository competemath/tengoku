/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Data.Rat.Defs
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Cardinality bounds and the binary projection trace obstruction -/

open scoped BigOperators

namespace SRG266.MomentBounds

/--
@isnad1 id=le.3h5v.s7.2342b6adf9da from=translated src=- shape=616a8fd7 vocab=3321a561
-/
theorem card_le_four_mul_bound {ι : Type*} (s : Finset ι)
    (f : ι → ℚ) (d bound : ℚ) (hd : 0 < d)
    (hgap : ∀ i ∈ s, d / 4 ≤ f i ^ 2)
    (hupper : ∑ i ∈ s, f i ^ 2 ≤ bound * d) :
    (s.card : ℚ) ≤ 4 * bound := by
  have hsum := Finset.sum_le_sum hgap
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  apply (mul_le_mul_iff_left₀ hd).mp
  nlinarith

/--
@isnad1 id=false.4h4v.s7.2b146f251f73 from=translated src=- shape=bac435ac vocab=0f0ea7aa
-/
theorem no_gap_of_moment_upper {ι : Type*} (s : Finset ι) (hs : s.card = 220)
    (f : ι → ℚ) (d : ℚ) (hd : 0 < d)
    (hgap : ∀ i ∈ s, d / 4 ≤ f i ^ 2)
    (hupper : ∑ i ∈ s, f i ^ 2 ≤ 45 * d) : False := by
  have hcard := card_le_four_mul_bound s f d 45 hd hgap hupper
  rw [hs] at hcard
  norm_num at hcard

/--
@isnad1 id=and.2h2v.s6.0b96f6e9164a from=translated src=- shape=48cf879d vocab=ded7ec63
-/
theorem shell_type_balance (a b : ℚ) (htotal : a + b = 220)
    (hfirst : a / 4 - b / 12 = 0) : a = 55 ∧ b = 165 := by
  constructor <;> linarith

/--
@isnad1 id=false.5h3v.s7.f698d20c901d from=translated src=- shape=9965998f vocab=a9ac3fea
-/
theorem no_q15_projection_trace (x y z : ℤ)
    (hx : x = 0 ∨ x = 4 ∨ x = 6 ∨ x = 12)
    (hy : y = 0 ∨ y = 4 ∨ y = 6 ∨ y = 12)
    (hcs : z ^ 2 ≤ x * y)
    (hroots : x = 6 → y = 6 → 3 ∣ z)
    (htrace : 4 * x + 4 * y - 2 * z = 50) : False := by
  have hnot : ¬ (x = 6 ∧ y = 6) := by
    rintro ⟨rfl, rfl⟩
    obtain ⟨k, hk⟩ := hroots rfl rfl
    omega
  rcases hx with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl <;>
    first | exact hnot ⟨rfl, rfl⟩ | nlinarith

end SRG266.MomentBounds

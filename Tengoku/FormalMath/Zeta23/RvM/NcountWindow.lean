/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/NcountWindow.lean — window arithmetic for `Ncount`.

These lemmas (window splitting, additivity and monotonicity of the zero count) live here, in the
root `Zeta23` namespace, and are used by the Riemann–von Mangoldt files.
-/
import Tengoku.FormalMath.Zeta23.Statement.SeamClosed

noncomputable section

namespace Zeta23
/-! ## Window arithmetic for Ncount -/

/-- windows split: zerosIn a c = zerosIn a b ∪ zerosIn b c for a ≤ b ≤ c.
@isnad1 id=eq.2h3v.s5.8c3fc672b434 from=translated src=- shape=f5498cce vocab=58d8ab82
-/
theorem zerosIn_union {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    zerosIn a c = zerosIn a b ∪ zerosIn b c := by
  ext ρ
  simp only [zerosIn, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨hρ, ha, hb⟩
    rcases le_or_gt ρ.im b with hle | hgt
    · exact Or.inl ⟨hρ, ha, hle⟩
    · exact Or.inr ⟨hρ, hgt, hb⟩
  · rintro (⟨hρ, ha, hb⟩ | ⟨hρ, ha, hb⟩)
    · exact ⟨hρ, ha, le_trans hb h2⟩
    · exact ⟨hρ, lt_of_le_of_lt h1 ha, hb⟩

/-- window additivity: N(a,c] = N(a,b] + N(b,c].
@isnad1 id=eq.2h3v.s5.4f54f846a5e9 from=translated src=- shape=be2d3d3e vocab=919ea763
-/
theorem Ncount_add {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    Ncount a c = Ncount a b + Ncount b c := by
  unfold Ncount
  rw [zerosIn_union h1 h2]
  refine finsum_mem_union ?_ (zerosIn_finite a b) (zerosIn_finite b c)
  rw [Set.disjoint_left]
  rintro ρ ⟨_, _, hb⟩ ⟨_, ha, _⟩
  exact absurd hb (not_le.2 ha)

/-- window monotonicity: (a,b] ⊆ (c,d] ⇒ N(a,b] ≤ N(c,d].
@isnad1 id=le.2h4v.s4.74e115e71603 from=translated src=- shape=8268fbc7 vocab=7686c2a7
-/
theorem Ncount_mono {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) : Ncount a b ≤ Ncount c d := by
  unfold Ncount
  have hsub : zerosIn a b ⊆ zerosIn c d := by
    rintro ρ ⟨hρ, h1, h2⟩
    exact ⟨hρ, lt_of_le_of_lt hca h1, le_trans h2 hbd⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite a b),
    finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite c d)]
  apply Finset.sum_le_sum_of_subset
  intro ρ hρ
  rw [Set.Finite.mem_toFinset] at hρ ⊢
  exact hsub hρ

end Zeta23

end

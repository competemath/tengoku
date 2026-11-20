/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Partition.BlockEnergy
import Tengoku.Seed.Algebra.BigOperators.Field

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Mass-weighted partition energy and refinement monotonicity

The partition energy of a relation `R` with respect to `P : Finpartition s` is the
mass-weighted mean of squared block densities,
`energy R P = Σ_{A,B ∈ parts} (|A||B| / |s|²) · d(A,B)²`, **including diagonal blocks**
(see `energy_eq_sum_weighted`). It is monotone under refinement (`energy_mono`) — the
quantity driving iterated-refinement (energy-increment) arguments.

**Design fact.** The *uniform* block-mean of `d²` (dividing by `#parts²` instead of
weighting by mass) is NOT refinement-monotone. Worked example over `s = {0,1,2}` with
`R a b ↔ (a = 0 ∧ b = 0)`: for the partition `{{0}, {1,2}}` the four block densities
are `1,0,0,0`, uniform mean `1/4`; refining to singletons gives nine densities
`1,0,…,0`, uniform mean `1/9 < 1/4`. The mass-weighted energy instead moves from
`1/9 ≤ 1/9` (it is `1·1·1/9 = 1/9` in both cases, consistent with monotonicity).
That example uses the *diagonal-inclusive* uniform mean. Mathlib's `Finpartition.energy`
is the uniform, `ℚ`-valued, **off-diagonal** variant used for equipartitions, so it needs
its own witness — now proved, on a common instance, in
`RegularityLemmata.MathlibEnergyCounterexample` (`RegularityLemmata/Graph/Bridge.lean`, where both
sides speak `SimpleGraph`): on six vertices split `2 + 4` with the complete bipartite graph
between the coarse cells, refining into `2 + 2 + 2` **decreases** mathlib's energy from
`1/2` to `4/9` (`mathlibEnergy_fine_lt_coarse`) while the mass-weighted `energy` here is
unchanged at `4/9` (`weightedEnergy_eq`), as `energy_mono` requires. Mathlib's
normalization is not a defect there — it is calibrated for equipartitions inside the
increment loop — but it cannot serve as the potential function for refinement arguments
over arbitrary partitions, which is why this file forks.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}
variable (R : α → α → Prop) [DecidableRel R]

/-- Un-normalized partition energy: mass-weighted local energies over all ordered pairs
of parts, diagonal included.-/
noncomputable def energyNum (P : Finpartition s) : ℝ :=
  ∑ AB ∈ P.parts ×ˢ P.parts, blockEnergy R AB.1 AB.2

/-- Normalized partition energy, in `[0, 1]`; `0` on the empty ground set.-/
noncomputable def energy (P : Finpartition s) : ℝ :=
  energyNum R P / (s.card : ℝ) ^ 2

variable {P Q : Finpartition s}

/--
@isnad1 id=le.0h4v.s5.b77f6f4ffb89 from=translated src=- shape=db318047 vocab=6c9f36df
-/
theorem energyNum_nonneg : 0 ≤ energyNum R P :=
  Finset.sum_nonneg fun _ _ => blockEnergy_nonneg

/--
@isnad1 id=le.0h4v.s5.9b912a80197e from=translated src=- shape=843c5e42 vocab=067c0bff
-/
theorem energyNum_le_sq : energyNum R P ≤ (s.card : ℝ) ^ 2 := by
  have hprod : ∑ uv ∈ P.parts ×ˢ P.parts, ((uv.1.card : ℝ) * (uv.2.card : ℝ))
      = (∑ A ∈ P.parts, (A.card : ℝ)) * (∑ B ∈ P.parts, (B.card : ℝ)) := by
    rw [Finset.sum_mul_sum, Finset.sum_product]
  calc energyNum R P
      ≤ ∑ uv ∈ P.parts ×ˢ P.parts, ((uv.1.card : ℝ) * (uv.2.card : ℝ)) :=
        Finset.sum_le_sum fun uv _ => blockEnergy_le_mass
    _ = (∑ A ∈ P.parts, (A.card : ℝ)) * (∑ B ∈ P.parts, (B.card : ℝ)) := hprod
    _ = (s.card : ℝ) ^ 2 := by rw [sum_card_parts_cast, sq]

/--
@isnad1 id=le.0h4v.s5.550a10eb79c7 from=translated src=- shape=db318047 vocab=1e69887f
-/
theorem energy_nonneg : 0 ≤ energy R P :=
  div_nonneg (energyNum_nonneg R) (by positivity)

/-- **The all-host normalization identity**: the un-normalized energy is the normalized one
scaled by `|s|²`, with **no** nonemptiness hypothesis. On the empty ground set both sides
are `0` — the partition has no parts, so `energyNum` is an empty sum, and the guard-free
convention makes `energy = 0/0 = 0` — so the identity survives the degenerate case that the
naive `div_mul_cancel₀` route excludes.
@isnad1 id=eq.0h4v.s6.5c0c7367f31d from=translated src=- shape=6c818263 vocab=0fd8b295
-/
theorem energyNum_eq_energy_mul : energyNum R P = energy R P * (s.card : ℝ) ^ 2 := by
  rcases eq_or_ne ((s.card : ℝ)) 0 with h | h
  · have hsq : (s.card : ℝ) ^ 2 = 0 := by rw [h]; ring
    have hz : energyNum R P = 0 :=
      le_antisymm (hsq ▸ energyNum_le_sq R) (energyNum_nonneg R)
    rw [hz, hsq, mul_zero]
  · rw [energy, div_mul_cancel₀ _ (pow_ne_zero 2 h)]

/-- Holds for ALL `s`: on the empty ground set the energy is `0 / 0 = 0`.
@isnad1 id=le.0h4v.s5.316a7b25d262 from=translated src=- shape=2fda4ccf vocab=1e69887f
-/
theorem energy_le_one : energy R P ≤ 1 := by
  unfold energy
  rcases eq_or_ne ((s.card : ℝ)) 0 with h | h
  · rw [h]
    norm_num
  · have hpos : (0 : ℝ) < (s.card : ℝ) :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h)
    rw [div_le_one (by positivity)]
    exact energyNum_le_sq R

/-- Reindexing the refined energy along the `P`-parent fibers.
@isnad1 id=eq.1h5v.s7.4986c84aedd6 from=translated src=- shape=3bc7fb6a vocab=8d0439cb
-/
theorem energyNum_eq_sum_refined (hQ : Q ≤ P) :
    (∑ C ∈ P.parts, ∑ D ∈ P.parts, ∑ C' ∈ Q.parts.filter (· ⊆ C),
      ∑ D' ∈ Q.parts.filter (· ⊆ D), blockEnergy R C' D') = energyNum R Q := by
  rw [Finset.sum_congr rfl fun C _ => Finset.sum_comm]
  rw [sum_over_parents hQ (fun C' => ∑ D ∈ P.parts, ∑ D' ∈ Q.parts.filter (· ⊆ D),
    blockEnergy R C' D')]
  rw [Finset.sum_congr rfl fun C' _ => sum_over_parents hQ (fun D' => blockEnergy R C' D')]
  unfold energyNum
  rw [Finset.sum_product]

/-- Refinement never decreases the un-normalized energy.
@isnad1 id=le.1h5v.s6.7698538cf550 from=translated src=- shape=aaa1552c vocab=6c9f36df
-/
theorem energyNum_mono (hQ : Q ≤ P) : energyNum R P ≤ energyNum R Q := by
  have hstep : energyNum R P
      ≤ ∑ C ∈ P.parts, ∑ D ∈ P.parts, ∑ C' ∈ Q.parts.filter (· ⊆ C),
          ∑ D' ∈ Q.parts.filter (· ⊆ D), blockEnergy R C' D' := by
    unfold energyNum
    rw [Finset.sum_product]
    exact Finset.sum_le_sum fun C hC =>
      Finset.sum_le_sum fun D hD => blockEnergy_le_sum_refined hQ R hC hD
  rw [energyNum_eq_sum_refined R hQ] at hstep
  exact hstep

/-- **Energy monotonicity.** Refinement never decreases the partition energy.
@isnad1 id=le.1h5v.s6.9ea571ac3983 from=translated src=- shape=aaa1552c vocab=1e69887f
-/
theorem energy_mono (hQ : Q ≤ P) : energy R P ≤ energy R Q := by
  unfold energy
  gcongr
  exact energyNum_mono R hQ

/-- The energy as an explicitly mass-weighted mean of squared block densities
(diagonal blocks included).
@isnad1 id=eq.0h4v.s7.7cadc604e2ff from=translated src=- shape=d0c3e415 vocab=eb25413f
-/
theorem energy_eq_sum_weighted :
    energy R P = ∑ AB ∈ P.parts ×ˢ P.parts,
      ((AB.1.card : ℝ) * AB.2.card / (s.card : ℝ) ^ 2) * pairDensity R AB.1 AB.2 ^ 2 := by
  rw [energy, energyNum, Finset.sum_div]
  exact Finset.sum_congr rfl fun AB _ => by rw [blockEnergy]; ring

/-! ### Tests and adversarial examples -/

-- Exact identity for the indiscrete partition of a 3-element set with the strict order:
-- one block of density 3/9 = 1/3, so energy = (1/3)² · 3 · 3 / 3² = 1/9.

end RegularityLemmata

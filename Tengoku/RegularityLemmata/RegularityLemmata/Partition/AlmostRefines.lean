/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Partition.Equitable
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Almost-refinement of partitions

`AlmostRefinesAt Q P m` is the raw per-parent form of almost-refinement: inside every
part `t` of `P`, the elements not covered by `Q`-parts contained in `t` number at most
`m`. This is exactly the shape mathlib proves for `Finpartition.equitabilise`
(`Finpartition.card_parts_equitabilise_subset_le`), re-exported here as
`equitabilise_almostRefinesAt` — the quantitative bridge the graph regularity ladder
consumes: an equitabilisation with part sizes in `{m, m+1}` almost-refines `P` at
tolerance `ε` as soon as `m · #P.parts ≤ ε · |s|`
(`almostRefines_of_almostRefinesAt`).

`exceptionalMass Q P` is the total uncovered mass, and `AlmostRefines Q P ε` its
normalized form. Composition is additive at the mass level (`AlmostRefines.trans`), and
almost-refinement is stable under further refinement of `Q`
(`almostRefinesAt_anti_left`). These were proved in general — not just checked on small
hosts — before this API was frozen.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- The part of `t` not covered by parts of `Q` contained in `t`.-/
def uncoveredWithin (Q : Finpartition s) (t : Finset α) : Finset α :=
  t \ (Q.parts.filter (· ⊆ t)).biUnion id

/-- Raw per-parent almost-refinement: every part of `P` has uncovered remainder of size
at most `m` in `Q`.-/
def AlmostRefinesAt (Q P : Finpartition s) (m : ℕ) : Prop :=
  ∀ t ∈ P.parts, (uncoveredWithin Q t).card ≤ m

/-- Total uncovered mass of `Q` against the parts of `P`.-/
def exceptionalMass (Q P : Finpartition s) : ℕ :=
  ∑ t ∈ P.parts, (uncoveredWithin Q t).card

/-- Normalized almost-refinement: the exceptional mass is at most `ε · |s|`.-/
def AlmostRefines (Q P : Finpartition s) (ε : ℝ) : Prop :=
  (exceptionalMass Q P : ℝ) ≤ ε * s.card

variable {P Q Q' R : Finpartition s} {m : ℕ} {ε ε₁ ε₂ : ℝ}

/-! ### Exact refinement gives zero remainder -/

/-- An actual refinement almost-refines with zero remainder.
@isnad1 id=almostre.1h4v.s5.88befc84f703 from=translated src=- shape=c9f609b4 vocab=197d628d
-/
theorem almostRefinesAt_of_le (hQ : Q ≤ P) : AlmostRefinesAt Q P 0 := by
  intro t ht
  rw [uncoveredWithin, biUnion_filter_subset_eq hQ ht, Finset.sdiff_self,
    Finset.card_empty]

/--
@isnad1 id=almostre.0h3v.s4.798ce982e610 from=translated src=- shape=01b68af4 vocab=12e820bd
-/
theorem almostRefinesAt_refl : AlmostRefinesAt P P 0 :=
  almostRefinesAt_of_le le_rfl

/--
@isnad1 id=almostre.0h3v.s5.d70dde170a12 from=translated src=- shape=2b17b0fb vocab=8a7d2dc3
-/
theorem bot_almostRefinesAt : AlmostRefinesAt (⊥ : Finpartition s) P 0 :=
  almostRefinesAt_of_le bot_le

/-! ### Monotonicity -/

/--
@isnad1 id=almostre.2h6v.s5.0fd13e1f8272 from=translated src=- shape=8322f8c9 vocab=197d628d
-/
theorem AlmostRefinesAt.mono {m' : ℕ} (hm : m ≤ m') (h : AlmostRefinesAt Q P m) :
    AlmostRefinesAt Q P m' := fun t ht => (h t ht).trans hm

/--
@isnad1 id=almostre.2h6v.s5.5e7ecb25d90a from=translated src=- shape=8322f8c9 vocab=d4dc690e
-/
theorem AlmostRefines.mono (hε : ε₁ ≤ ε₂) (h : AlmostRefines Q P ε₁) :
    AlmostRefines Q P ε₂ :=
  h.trans (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _))

/-- Refining `Q` further can only shrink each uncovered remainder.
@isnad1 id=le.1h5v.s6.28df352cdce9 from=translated src=- shape=4708b62a vocab=55f16ed3
-/
theorem uncoveredWithin_anti (hQ' : Q' ≤ Q) (t : Finset α) :
    uncoveredWithin Q' t ⊆ uncoveredWithin Q t := by
  intro x hx
  rw [uncoveredWithin, Finset.mem_sdiff] at hx ⊢
  refine ⟨hx.1, fun hcov => hx.2 ?_⟩
  rw [Finset.mem_biUnion] at hcov
  obtain ⟨E, hEf, hxE⟩ := hcov
  rw [Finset.mem_filter] at hEf
  obtain ⟨E', hE'mem, hxE'⟩ := Q'.exists_mem (Q.le hEf.1 hxE)
  obtain ⟨E'', hE''mem, hE'sub⟩ := hQ' hE'mem
  have : E'' = E := Q.eq_of_mem_parts hE''mem hEf.1 (hE'sub hxE') hxE
  rw [Finset.mem_biUnion]
  exact ⟨E', Finset.mem_filter.mpr ⟨hE'mem, (this ▸ hE'sub).trans hEf.2⟩, hxE'⟩

/-- Almost-refinement is stable under further refinement of the finer partition.
@isnad1 id=almostre.2h6v.s6.1276ff836a6d from=translated src=- shape=0efc92c1 vocab=197d628d
-/
theorem almostRefinesAt_anti_left (hQ' : Q' ≤ Q) (h : AlmostRefinesAt Q P m) :
    AlmostRefinesAt Q' P m := fun t ht =>
  (Finset.card_le_card (uncoveredWithin_anti hQ' t)).trans (h t ht)

/--
@isnad1 id=le.1h5v.s6.a0a383f30bc7 from=translated src=- shape=b91d4be7 vocab=8096d115
-/
theorem exceptionalMass_anti_left (hQ' : Q' ≤ Q) :
    exceptionalMass Q' P ≤ exceptionalMass Q P :=
  Finset.sum_le_sum fun t _ => Finset.card_le_card (uncoveredWithin_anti hQ' t)

/--
@isnad1 id=almostre.2h6v.s6.2d1bc0b12b03 from=translated src=- shape=0efc92c1 vocab=d4dc690e
-/
theorem almostRefines_anti_left (hQ' : Q' ≤ Q) (h : AlmostRefines Q P ε) :
    AlmostRefines Q' P ε :=
  le_trans (by exact_mod_cast exceptionalMass_anti_left hQ') h

/-! ### Mass bounds and the normalized form -/

/--
@isnad1 id=le.1h5v.s6.f7dab5eb1ea9 from=translated src=- shape=91cb0c32 vocab=01533d54
-/
theorem exceptionalMass_le_of_almostRefinesAt (h : AlmostRefinesAt Q P m) :
    exceptionalMass Q P ≤ m * P.parts.card := by
  calc exceptionalMass Q P ≤ ∑ _t ∈ P.parts, m := Finset.sum_le_sum h
    _ = P.parts.card * m := by rw [Finset.sum_const, smul_eq_mul]
    _ = m * P.parts.card := Nat.mul_comm _ _

/-- **Quantitative bridge.** A per-parent remainder `m` gives normalized
almost-refinement at any `ε` with `m · #P.parts ≤ ε · |s|` — the exact arithmetic the
regular-equipartition theorems consume.
@isnad1 id=almostre.2h6v.s6.2bd2b91ede94 from=translated src=- shape=f9805b4a vocab=aa5ffa7d
-/
theorem almostRefines_of_almostRefinesAt (h : AlmostRefinesAt Q P m)
    (hm : (m * P.parts.card : ℝ) ≤ ε * s.card) : AlmostRefines Q P ε := by
  refine le_trans ?_ hm
  exact_mod_cast exceptionalMass_le_of_almostRefinesAt h

/--
@isnad1 id=almostre.2h5v.s6.e62152959ab8 from=translated src=- shape=dc8835c4 vocab=d4dc690e
-/
theorem almostRefines_of_le (hQ : Q ≤ P) (hε : 0 ≤ ε) : AlmostRefines Q P ε := by
  refine almostRefines_of_almostRefinesAt (almostRefinesAt_of_le hQ) ?_
  simp only [Nat.cast_zero, zero_mul]
  exact mul_nonneg hε (Nat.cast_nonneg _)

/--
@isnad1 id=almostre.0h3v.s4.7294d277db6a from=translated src=- shape=01b68af4 vocab=c11e88f3
-/
theorem almostRefines_refl : AlmostRefines P P 0 :=
  almostRefines_of_le le_rfl le_rfl

/-! ### The equitabilise bridge -/

/-- **Equitabilisation almost-refines.** Direct re-export of mathlib's per-parent
remainder bound for `Finpartition.equitabilise`.
@isnad1 id=almostre.1h6v.s6.1be02f7cb893 from=translated src=- shape=4de15aa9 vocab=28b753d7
-/
theorem equitabilise_almostRefinesAt {a b : ℕ} (P : Finpartition s)
    (h : a * m + b * (m + 1) = s.card) :
    AlmostRefinesAt (P.equitabilise h) P m := fun _ ht =>
  equitabilise_uncovered_card_le ht

/-- Equipartitions of any admissible part count almost-refine any partition: for
`0 < t ≤ |s|` there is an equipartition with exactly `t` parts whose per-parent
remainder against `P` is at most `⌊|s| / t⌋`.
@isnad1 id=ex.2h4v.s6.d8a9892760ac from=translated src=- shape=58e53906 vocab=69b85dc5
-/
theorem exists_equipartition_almostRefinesAt (P : Finpartition s) {t : ℕ}
    (ht : 0 < t) (hts : t ≤ s.card) :
    ∃ E : Finpartition s, E.IsEquipartition ∧ E.parts.card = t ∧
      AlmostRefinesAt E P (s.card / t) := by
  have hrt : s.card % t < t := Nat.mod_lt _ ht
  have hmpos : 0 < s.card / t := (Nat.one_le_div_iff ht).mpr hts
  have h : (t - s.card % t) * (s.card / t) + (s.card % t) * (s.card / t + 1) = s.card := by
    have hdm : t * (s.card / t) + s.card % t = s.card := Nat.div_add_mod s.card t
    have hsub : (t - s.card % t) * (s.card / t) = t * (s.card / t) - s.card % t * (s.card / t) :=
      Nat.sub_mul t (s.card % t) (s.card / t)
    have hrm : s.card % t * (s.card / t) ≤ t * (s.card / t) :=
      Nat.mul_le_mul_right _ hrt.le
    calc (t - s.card % t) * (s.card / t) + (s.card % t) * (s.card / t + 1)
        = (t * (s.card / t) - s.card % t * (s.card / t))
          + (s.card % t * (s.card / t) + s.card % t) := by rw [hsub, Nat.mul_add, Nat.mul_one]
      _ = t * (s.card / t) + s.card % t := by omega
      _ = s.card := hdm
  refine ⟨P.equitabilise h, Finpartition.equitabilise_isEquipartition, ?_,
    equitabilise_almostRefinesAt P h⟩
  rw [P.card_parts_equitabilise (h := h) hmpos.ne']
  omega

/-- The `ε`-form: an equipartition with `t` parts almost-refines `P` at tolerance `ε`
once `⌊|s|/t⌋ · #P.parts ≤ ε · |s|`.
@isnad1 id=ex.3h5v.s7.6092f91ad77b from=translated src=- shape=0e9c9387 vocab=65b3116a
-/
theorem exists_equipartition_almostRefines (P : Finpartition s) {t : ℕ}
    (ht : 0 < t) (hts : t ≤ s.card)
    (hbound : ((s.card / t : ℕ) : ℝ) * P.parts.card ≤ ε * s.card) :
    ∃ E : Finpartition s, E.IsEquipartition ∧ E.parts.card = t ∧ AlmostRefines E P ε := by
  obtain ⟨E, h1, h2, h3⟩ := exists_equipartition_almostRefinesAt P ht hts
  refine ⟨E, h1, h2, almostRefines_of_almostRefinesAt h3 ?_⟩
  exact_mod_cast hbound

/-! ### Composition -/

/-- Set-level composition bound: what `R` leaves uncovered in a `P`-part is covered by
what `Q` leaves uncovered there plus what `R` leaves uncovered inside each `Q`-part.
@isnad1 id=le.0h5v.s6.fc7a27041c15 from=translated src=- shape=85c3ae5e vocab=10b6731d
-/
theorem uncoveredWithin_subset_trans (t : Finset α) :
    uncoveredWithin R t ⊆
      uncoveredWithin Q t ∪
        (Q.parts.filter (· ⊆ t)).biUnion (fun u => uncoveredWithin R u) := by
  intro x hx
  rw [uncoveredWithin, Finset.mem_sdiff] at hx
  rw [Finset.mem_union]
  by_cases hq : x ∈ (Q.parts.filter (· ⊆ t)).biUnion id
  · right
    rw [Finset.mem_biUnion] at hq ⊢
    obtain ⟨u, huf, hxu⟩ := hq
    refine ⟨u, huf, ?_⟩
    rw [uncoveredWithin, Finset.mem_sdiff]
    refine ⟨hxu, fun hcov => hx.2 ?_⟩
    rw [Finset.mem_biUnion] at hcov ⊢
    obtain ⟨v, hvf, hxv⟩ := hcov
    rw [Finset.mem_filter] at hvf huf
    exact ⟨v, Finset.mem_filter.mpr ⟨hvf.1, hvf.2.trans huf.2⟩, hxv⟩
  · left
    rw [uncoveredWithin, Finset.mem_sdiff]
    exact ⟨hx.1, hq⟩

/-- **Composition, additive at the mass level.**
@isnad1 id=almostre.2h7v.s6.38b7c229d5ce from=translated src=- shape=46f3c62d vocab=ff8156de
-/
theorem AlmostRefines.trans (hRQ : AlmostRefines R Q ε₂) (hQP : AlmostRefines Q P ε₁) :
    AlmostRefines R P (ε₁ + ε₂) := by
  have hstep : ∀ t ∈ P.parts, (uncoveredWithin R t).card
      ≤ (uncoveredWithin Q t).card
        + ∑ u ∈ Q.parts.filter (· ⊆ t), (uncoveredWithin R u).card := by
    intro t ht
    calc (uncoveredWithin R t).card
        ≤ (uncoveredWithin Q t ∪
            (Q.parts.filter (· ⊆ t)).biUnion (fun u => uncoveredWithin R u)).card :=
          Finset.card_le_card (uncoveredWithin_subset_trans t)
      _ ≤ (uncoveredWithin Q t).card
            + ((Q.parts.filter (· ⊆ t)).biUnion (fun u => uncoveredWithin R u)).card :=
          Finset.card_union_le _ _
      _ ≤ (uncoveredWithin Q t).card
            + ∑ u ∈ Q.parts.filter (· ⊆ t), (uncoveredWithin R u).card :=
          Nat.add_le_add_left Finset.card_biUnion_le _
  -- Is Q ≤ P available? NO — composition must not assume it. Reindex the double sum
  -- over Q-parts-inside-t by bounding it by the full sum over Q.parts instead.
  have hmass : (exceptionalMass R P : ℝ)
      ≤ (exceptionalMass Q P : ℝ) + (exceptionalMass R Q : ℝ) := by
    have hnat : exceptionalMass R P
        ≤ exceptionalMass Q P
          + ∑ t ∈ P.parts, ∑ u ∈ Q.parts.filter (· ⊆ t), (uncoveredWithin R u).card := by
      rw [exceptionalMass, exceptionalMass, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum hstep
    have hinner : ∑ t ∈ P.parts, ∑ u ∈ Q.parts.filter (· ⊆ t), (uncoveredWithin R u).card
        ≤ exceptionalMass R Q := by
      rw [exceptionalMass]
      calc ∑ t ∈ P.parts, ∑ u ∈ Q.parts.filter (· ⊆ t), (uncoveredWithin R u).card
          = ∑ u ∈ P.parts.biUnion (fun t => Q.parts.filter (· ⊆ t)),
              (uncoveredWithin R u).card := by
            rw [Finset.sum_biUnion ?_]
            intro t₁ ht₁ t₂ ht₂ hne
            simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
            rintro u ⟨humem, hsub₁⟩ ⟨-, hsub₂⟩
            obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts humem
            exact hne (P.eq_of_mem_parts (Finset.mem_coe.mp ht₁) (Finset.mem_coe.mp ht₂)
              (hsub₁ hx) (hsub₂ hx))
        _ ≤ ∑ u ∈ Q.parts, (uncoveredWithin R u).card := by
            refine Finset.sum_le_sum_of_subset (fun u hu => ?_)
            rw [Finset.mem_biUnion] at hu
            obtain ⟨t, -, huf⟩ := hu
            exact (Finset.mem_filter.mp huf).1
    exact_mod_cast le_trans hnat (Nat.add_le_add_left hinner _)
  calc (exceptionalMass R P : ℝ)
      ≤ (exceptionalMass Q P : ℝ) + (exceptionalMass R Q : ℝ) := hmass
    _ ≤ ε₁ * s.card + ε₂ * s.card := add_le_add hQP hRQ
    _ = (ε₁ + ε₂) * s.card := by ring

/-! ### Tests and adversarial examples (the falsification-gate battery) -/

-- Reflexivity and exact refinement, computed: uncovered remainders are empty.

end RegularityLemmata

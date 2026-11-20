/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Graph.EquitableStep

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Equitable-supplier ladder, step 5: the finite-family regularity summit

`ARCHITECTURE.md` supplier route decision (2026-07-22), implementation sequence step 5.
Step 4 froze the constants and proved the one-step theorem: a non-family-regular
equipartition admits an equipartition refinement with exactly `familyStepBound #P.parts`
parts gaining `ε⁵/5` of family energy. This file iterates it.

* `familyFuel K ε = ⌈5K/ε⁵⌉₊` — the number of steps, now that the retained fraction is
  proved: the family energy is bounded by `K` (`familyEnergy_le_card`) and each step gains
  `familyRetainedFraction · ε⁵ = ε⁵/5`, so `K / (ε⁵/5) = 5K/ε⁵` steps exhaust the ceiling.
* `familyRegularityBound K ε l = familyRegularityBoundAux (familyFuel K ε)
  (familyInitialBound familyChunkThreshold ε l)` — the final part-count bound: the
  fuel-fold iterate of the single-relation step, started at the ε-dependent floor. It is
  **host-independent** and mentions only `K`, `ε`, and `l`.
* `familyRegularity_iterate` — the fuel-parametrized iteration, in the budget form of
  `regularity_iterate`: from family energy within `t · ε⁵/5` of the ceiling `K`, `t` steps
  reach a family-regular equipartition. Three invariants ride along, and each is preserved
  because the step's part count is EXACT: the equipartition property, the floor
  `familyInitialBound ⋯ ≤ #parts` (part counts only grow), and the host-size requirement.
* `exists_familyRegular_equipartition` — **the summit**: for every finite directed family,
  every tolerance `0 < ε ≤ 1`, and every requested `l`, a host with
  `familyRegularityBound K ε l ≤ #s` carries an equipartition that is `ε`-regular for
  EVERY relation of the family, with `l ≤ #parts ≤ familyRegularityBound K ε l`.

**The host-size requirement is exactly `familyRegularityBound K ε l ≤ #s`** — room for
the partition the iteration can actually produce, and nothing beyond it. In particular no
room is demanded for a further step: the terminal (fuel-zero) argument concludes
regularity by contradiction from the ENERGY gain alone, and
`familyEnergy_equitableIncrement_increment` carries no host hypothesis — even with
`chunkSize = 0` the equitabilised increment exists, refines `P`, is an equipartition, and
gains `ε⁵/5`, which is already impossible against the ceiling `K`. The exact new part
count, the only thing that needs host room, is used solely to transport the part-count
invariant through a step that really happens. This is the `N₀` the piece supplier will
have to meet (step 6); it is stated, not hidden, and a permanent test records that it
fails on small hosts.

**No tower-type claim.** `familyStepBound` is deliberately generous and the bound is a
`familyFuel`-fold iterate of it; only finiteness and host-independence are used or
claimed. The Conlon–Fox scope statement in `PROVENANCE.md` stands: this route follows the
weaker regularity-plus-independent-set argument, so no quantitative optimality is asserted.

The budget-form iteration is this library's own `regularity_iterate`
(`RegularityLemmata/Graph/Regularity.lean`) transposed from one relation with ceiling `1` to a
family with ceiling `K`; the bounded-iteration architecture it follows is mathlib's proof of
Szemerédi's regularity lemma, credited there and in `PROVENANCE.md`.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α} {ε : ℝ}
variable {K : ℕ} {Rk : Fin K → α → α → Prop} [∀ k, DecidableRel (Rk k)]

/-! ### The fuel and the final bound -/

/-- **The fuel**, now that the retained fraction is proved: the family energy is at most
`K` and each step gains `ε⁵/5`, so `⌈5K/ε⁵⌉₊` steps exhaust the ceiling.-/
noncomputable def familyFuel (K : ℕ) (ε : ℝ) : ℕ := ⌈5 * (K : ℝ) / ε ^ 5⌉₊

/-- **The final part-count bound**: the fuel-fold iterate of the single-relation step
bound, started at the ε-dependent initial floor. Host-independent — it mentions only `K`,
`ε`, and the requested `l`.-/
noncomputable def familyRegularityBound (K : ℕ) (ε : ℝ) (l : ℕ) : ℕ :=
  familyRegularityBoundAux (familyFuel K ε) (familyInitialBound familyChunkThreshold ε l)

/--
@isnad1 id=eq.0h1v.s4.d538c320dac2 from=translated src=- shape=004a7881 vocab=dd49d9c8
-/
theorem familyFuel_zero (ε : ℝ) : familyFuel 0 ε = 0 := by
  rw [familyFuel]
  norm_num

/--
@isnad1 id=le.0h3v.s4.b4a652779442 from=translated src=- shape=791015cc vocab=9617b01c
-/
theorem le_familyRegularityBound (K : ℕ) (ε : ℝ) (l : ℕ) :
    familyInitialBound familyChunkThreshold ε l ≤ familyRegularityBound K ε l :=
  le_familyRegularityBoundAux _ _

/-- The requested part count is met: `l` never exceeds the final bound.
@isnad1 id=le.0h3v.s3.430451c882c2 from=translated src=- shape=24aa6d92 vocab=31fa52ed
-/
theorem le_familyRegularityBound_of_le (K : ℕ) (ε : ℝ) (l : ℕ) :
    l ≤ familyRegularityBound K ε l :=
  le_trans (le_familyInitialBound _ _ _) (le_familyRegularityBound K ε l)

/-- **The fuel is enough**: `K` steps' worth of gain at `ε⁵/5` each exhausts the ceiling.
@isnad1 id=le.1h2v.s5.326bd8154d9f from=translated src=- shape=cb9d581f vocab=50e039d4
-/
theorem card_le_familyFuel_mul (hε : 0 < ε) (K : ℕ) :
    (K : ℝ) ≤ (familyFuel K ε : ℝ) * (familyRetainedFraction * ε ^ 5) := by
  have hε5 : (0 : ℝ) < ε ^ 5 := by positivity
  have hc : familyRetainedFraction * ε ^ 5 = ε ^ 5 / 5 := by
    rw [familyRetainedFraction]; ring
  rw [hc]
  have hceil : 5 * (K : ℝ) / ε ^ 5 ≤ (familyFuel K ε : ℝ) := Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_right hceil (le_of_lt (by positivity : (0 : ℝ) < ε ^ 5 / 5))
  calc (K : ℝ) = 5 * (K : ℝ) / ε ^ 5 * (ε ^ 5 / 5) := by field_simp
    _ ≤ (familyFuel K ε : ℝ) * (ε ^ 5 / 5) := hmul

/-! ### The bounded iteration -/

/-- **Fuel-parametrized iteration.** From family energy within `t · ε⁵/5` of the ceiling
`K`, `t` equitabilised steps reach a family-regular equipartition.

The host hypothesis is the part count the LAST of the `t` steps could reach — no more:
at fuel `t + 1` it unfolds to the fuel-`t` hypothesis for the stepped partition and
dominates the single step taken now, and at fuel `0` it is not used at all.
@isnad1 id=ex.6h8v.s8.cd3fca46f79c from=translated src=- shape=7d8a9963 vocab=e30be6be
-/
theorem familyRegularity_iterate (hε : 0 < ε) (hε1 : ε ≤ 1) {l : ℕ} :
    ∀ (t : ℕ) (P : Finpartition s), P.IsEquipartition →
      familyInitialBound familyChunkThreshold ε l ≤ P.parts.card →
      familyRegularityBoundAux t P.parts.card ≤ s.card →
      (K : ℝ) - (t : ℝ) * (familyRetainedFraction * ε ^ 5) ≤ familyEnergy Rk P →
      ∃ Q : Finpartition s, Q ≤ P ∧ Q.IsEquipartition ∧ IsFamilyRegular Rk ε Q ∧
        familyInitialBound familyChunkThreshold ε l ≤ Q.parts.card ∧
        Q.parts.card ≤ familyRegularityBoundAux t P.parts.card := by
  have hgain : (0 : ℝ) < familyRetainedFraction * ε ^ 5 := by
    rw [familyRetainedFraction]; positivity
  intro t
  induction t with
  | zero =>
    intro P hP hfloor _hs hbudget
    refine ⟨P, le_rfl, hP, ?_, hfloor, le_familyRegularityBoundAux 0 _⟩
    by_contra hreg
    -- The terminal contradiction needs only the ENERGY gain, not the exact new part
    -- count: `familyEnergy_equitableIncrement_increment` carries no host hypothesis, so
    -- fuel `0` requires no room for a further step.
    rw [IsFamilyRegular] at hreg
    push Not at hreg
    obtain ⟨k, hk⟩ := hreg
    have hgainQ := familyEnergy_equitableIncrement_increment (Rk := Rk) hP hε hε1 hfloor k
      (lt_of_not_ge hk)
    have hceil : familyEnergy Rk (equitableIncrement (Rk k) ε hP) ≤ (K : ℝ) :=
      familyEnergy_le_card
    simp only [Nat.cast_zero, zero_mul, sub_zero] at hbudget
    linarith
  | succ t IH =>
    intro P hP hfloor hs hbudget
    by_cases hreg : IsFamilyRegular Rk ε P
    · exact ⟨P, le_rfl, hP, hreg, hfloor, le_familyRegularityBoundAux _ _⟩
    · -- Unfold the host hypothesis once: it is the fuel-`t` hypothesis after the step.
      rw [familyRegularityBoundAux] at hs
      have hstep : familyStepBound P.parts.card ≤ s.card :=
        le_trans (le_familyRegularityBoundAux t (familyStepBound P.parts.card)) hs
      obtain ⟨P', hP'P, hP'eq, hP'card, hP'gain⟩ :=
        exists_familyEnergy_increment_equitable Rk hP hε hε1 hfloor hstep hreg
      have hfloor' : familyInitialBound familyChunkThreshold ε l ≤ P'.parts.card := by
        rw [hP'card]
        exact le_trans hfloor (le_familyStepBound _)
      have hs' : familyRegularityBoundAux t P'.parts.card ≤ s.card := by
        rw [hP'card]; exact hs
      have hbudget' : (K : ℝ) - (t : ℝ) * (familyRetainedFraction * ε ^ 5)
          ≤ familyEnergy Rk P' := by
        push_cast at hbudget
        linarith
      obtain ⟨Q, hQP', hQeq, hQreg, hQfloor, hQcard⟩ := IH P' hP'eq hfloor' hs' hbudget'
      refine ⟨Q, hQP'.trans hP'P, hQeq, hQreg, hQfloor, ?_⟩
      rw [familyRegularityBoundAux, ← hP'card]
      exact hQcard

/-! ### The summit -/

/-- **Equitable finite-family regularity.** For finitely many arbitrary DIRECTED relations
on a host with `familyRegularityBound K ε l ≤ #s`, and every tolerance `0 < ε ≤ 1` and
requested part count `l`, there is an EQUIPARTITION that is `ε`-regular for EVERY relation
of the family, with `l ≤ #parts ≤ familyRegularityBound K ε l`. The host requirement is
the produced part count itself — no room is asked for a step that never happens.

No symmetry is assumed anywhere. The bound is host-independent; the host hypothesis is a
lower bound on `#s`, not on the bound. Ordinary off-diagonal regularity only — equitable
STRONG regularity stays deferred (`ARCHITECTURE.md`), and no tower-type claim is made.
@isnad1 id=ex.3h6v.s7.18d7b1ea5223 from=translated src=- shape=cbcce8e6 vocab=9279144f
-/
theorem exists_familyRegular_equipartition (Rk : Fin K → α → α → Prop)
    [∀ k, DecidableRel (Rk k)] (hε : 0 < ε) (hε1 : ε ≤ 1) (l : ℕ)
    (hs : familyRegularityBound K ε l ≤ s.card) :
    ∃ Q : Finpartition s, Q.IsEquipartition ∧ IsFamilyRegular Rk ε Q ∧
      l ≤ Q.parts.card ∧ Q.parts.card ≤ familyRegularityBound K ε l := by
  set n := familyInitialBound familyChunkThreshold ε l with hn
  have hn0 : n ≠ 0 := by
    have := two_le_familyInitialBound familyChunkThreshold ε l
    omega
  have hns : n ≤ s.card := le_trans (le_familyRegularityBound K ε l) hs
  obtain ⟨P, hPeq, hPcard⟩ := Finpartition.exists_equipartition_card_eq s hn0 hns
  have hfloor : n ≤ P.parts.card := hPcard.ge
  have hs' : familyRegularityBoundAux (familyFuel K ε) P.parts.card ≤ s.card := by
    rw [hPcard]
    exact hs
  have hbudget : (K : ℝ) - (familyFuel K ε : ℝ) * (familyRetainedFraction * ε ^ 5)
      ≤ familyEnergy Rk P := by
    have h1 := card_le_familyFuel_mul (ε := ε) hε K
    have h2 : (0 : ℝ) ≤ familyEnergy Rk P := familyEnergy_nonneg
    linarith
  obtain ⟨Q, -, hQeq, hQreg, hQfloor, hQcard⟩ :=
    familyRegularity_iterate hε hε1 (l := l) (familyFuel K ε) P hPeq hfloor hs' hbudget
  refine ⟨Q, hQeq, hQreg, le_trans (le_familyInitialBound _ _ _) hQfloor, ?_⟩
  rw [hPcard] at hQcard
  rw [familyRegularityBound, ← hn]
  exact hQcard

/-! ### Endpoints -/

/-- **The `K = 0` endpoint.** The empty family needs no steps: the fuel is `0` and the
bound is the initial floor itself, so the summit returns an equipartition of the requested
size, family-regular for vacuous reasons — and its host requirement is just enough
vertices for that initial equipartition.
@isnad1 id=eq.0h2v.s4.d0a28f28d4d6 from=translated src=- shape=8ca0490d vocab=a53997de
-/
theorem familyRegularityBound_zero (ε : ℝ) (l : ℕ) :
    familyRegularityBound 0 ε l = familyInitialBound familyChunkThreshold ε l := by
  rw [familyRegularityBound, familyFuel_zero, familyRegularityBoundAux]

/-! ### Tests and adversarial examples -/

section Tests

-- The fuel at the `K = 0` endpoint is `0`, and the bound collapses to the floor: no step
-- is taken for the empty family.

end Tests

end RegularityLemmata

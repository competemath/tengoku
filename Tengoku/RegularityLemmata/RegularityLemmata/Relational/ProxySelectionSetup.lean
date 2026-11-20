/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Relational.ProxyAggregateMass
import Tengoku.RegularityLemmata.RegularityLemmata.Finite.WeightedChoiceBudget

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Route (b) ladder step 2: weighted choice on proxy cells, and the forbidden-event budgets

`ARCHITECTURE.md` route (b) ladder step 2, final unit, **steps 1 and 2 of five**: the index
and event types on which `RegularityLemmata/Finite/WeightedChoice.lean` is instantiated, and the
conversion of the aggregate nonuniform mass into that machine's forbidden-event hypothesis. The cost
budget, the constants and the summit are steps 3–5 and are NOT here.

The machine is already indexed by an abstract event type with two distinct coordinates,
which is exactly what this file supplies. It is split across two generic modules:
`RegularityLemmata/Finite/WeightedChoice.lean` for the selection and expectation machinery, and
`RegularityLemmata/Finite/WeightedChoiceBudget.lean` for the adapters that convert aggregate mass
estimates into its hypotheses. Neither mentions a partition, a relation or a palette.

## Step 1 — the instantiation

* `ProxyIndex Q` — the selection coordinates: one per PROXY cell, so a selection chooses one
  representative fine cell inside every proxy.
* `ProxyEvent Q` — the forbidden events: an ordered distinct proxy pair. **No palette
  component.** In `exists_piFinset_forall_not_mem_bad_cost_le` the event type occurs only in
  `hbad`; the cost hypothesis `hexp` mentions `cost` alone. Palettes are NOT event
  coordinates. They enter the forbidden channel through the UNION of the per-palette
  nonuniform sets, and the cost channel through aggregate deviation. Multiplying them into
  the event index would be a different and wasteful thing: it would carry the palette count
  into the event cardinality rather than into the forbidden set.
* `proxyEventFst`, `proxyEventSnd`, `proxyEvent_fst_ne_snd` — the two coordinates and the
  distinctness the machine demands. Sibling pairs are events like any other.
* `proxyCandidates` — the candidate family, `repCandidates` of the fine partition inside
  each proxy, reused unchanged: the rebuild changes the INDEX, not the candidate notion.
* `proxyTotalCandidateWeight_pos` — `hWpos`, from the half-mass theorem proxy by proxy.

## Step 2 — the forbidden-event budget

* `sum_event_mass_le_of_weight_floor` (`RegularityLemmata/Finite/WeightedChoiceBudget.lean`) — the
generic
  factorization: a uniform floor `w₀ ≤ W j` turns the whole `hbad` left-hand side into
  `(aggregate mass) / w₀ ^ 2 * ∏_j W j`. **The event count does not appear** — each event
  contributes its own mass, never a copy of the total.
* `sum_candidateMass_le_fiberMass` — the candidate rectangle inside the fine-part fibers,
  as a weighted-mass inequality. Both channels need it, and later sparse, deviant and edit
  charges will need it too.
* `sum_proxyEvent_nonuniform_mass_le` — that factorization instantiated on proxies for a
  SINGLE relation, with the aggregate supplied by `sum_proxyPair_nonuniform_le`. The
  resulting admissible `σ` is `badMassDiagNum R ε F / w₀ ^ 2`, in which no `9n²` event-count
  multiplier occurs.
* `sum_proxyEvent_paletteNonuniform_mass_le` — **the simultaneous budget**, which is what the
  selection actually needs. The forbidden set `paletteNonuniformFinePairs` is the union over
  palette colors of the per-palette nonuniform sets — charged with `sum_le_sum_of_exists_mem`,
  the union bound in `RegularityLemmata/Finite/WeightedChoiceBudget.lean` — and its budget is
  `K * B / w₀ ^ 2` times the total weight, where `K = Fintype.card (BinaryPairPalette L)` and
  `B` bounds each palette's bad mass. `K` is the union-bound factor obtained from the
  per-palette estimates; it is not an event-count factor, and no `9n²` multiplier occurs
  here either. Optimality of `K` is not claimed.
* `notMem_paletteNonuniformFinePairs_iff` — what the summit consumes: weighted choice returns
  `∉ Bad e`, and for a pair of fine cells that is equivalent to uniformity for EVERY color.

## Steps 3–5, not done here

The conditioned cost budget from `sum_proxyPair_deviant_le`; the candidate-weight and
proxy-size constants that discharge `σ < 1`; the summit. `ARCHITECTURE.md` waits for the
completed theorem and its actual constants.
-/

namespace RegularityLemmata

open FirstOrder

variable {V : Type*} [DecidableEq V] {s : Finset V}

/-! ### The coordinates and the events -/

/-- The selection coordinates: one per PROXY cell. A selection assigns each proxy a
representative fine cell.-/
abbrev ProxyIndex (Q : Finpartition s) : Type _ := {C : Finset V // C ∈ Q.parts}

/-- The forbidden events: an ordered DISTINCT proxy pair. Sibling pairs — two proxies of one
owner — are events like any other, and there is deliberately no palette component: palettes
are not event coordinates. They enter the forbidden channel through
`paletteNonuniformFinePairs`, and the cost channel through aggregate deviation.-/
abbrev ProxyEvent (Q : Finpartition s) : Type _ :=
  {pd : Finset V × Finset V // pd ∈ proxyPairEvents Q}

variable {Q : Finpartition s}

/-- The ordered proxy PAIR underlying an event, as a readable projection: `e.1` names a
pair of cells, not a cell.-/
def proxyEventPair (e : ProxyEvent Q) : Finset V × Finset V := e.1

/-- The first coordinate of an event — a proxy CELL.-/
def proxyEventFst (e : ProxyEvent Q) : ProxyIndex Q :=
  ⟨e.1.1, (mem_proxyPairEvents.mp e.2).1⟩

/-- The second coordinate of an event.-/
def proxyEventSnd (e : ProxyEvent Q) : ProxyIndex Q :=
  ⟨e.1.2, (mem_proxyPairEvents.mp e.2).2.1⟩

/--
@isnad1 id=eq.0h4v.s6.5417b3287bc2 from=translated src=- shape=23392a01 vocab=095774ac
-/
@[simp] theorem proxyEventPair_fst (e : ProxyEvent Q) :
    (proxyEventPair e).1 = (proxyEventFst e).1 := rfl

/--
@isnad1 id=eq.0h4v.s6.b7b91045e3af from=translated src=- shape=23392a01 vocab=4ceb30ad
-/
@[simp] theorem proxyEventPair_snd (e : ProxyEvent Q) :
    (proxyEventPair e).2 = (proxyEventSnd e).1 := rfl

/--
@isnad1 id=mem.0h4v.s6.ed36e228a888 from=translated src=- shape=822b7089 vocab=8e683550
-/
@[simp] theorem proxyEventPair_mem (e : ProxyEvent Q) :
    proxyEventPair e ∈ proxyPairEvents Q := e.2

/-- An event IS its proxy pair, so the projection is injective — structural API for the
event representation, used whenever events are summed as pairs.
@isnad1 id=injectiv.0h3v.s5.18d32c95279d from=translated src=- shape=f978feaa vocab=a8de8f80
-/
theorem proxyEventPair_injective : Function.Injective (proxyEventPair (Q := Q)) :=
  fun _ _ h => Subtype.ext h

/-- **The two coordinates are distinct** — the hypothesis `WeightedChoice` demands of an
event index, and the reason self-pairs are excluded from `proxyPairEvents`.
@isnad1 id=ne.0h4v.s5.67b17662b1b5 from=translated src=- shape=889e54f5 vocab=f44ffd7c
-/
theorem proxyEvent_fst_ne_snd (e : ProxyEvent Q) : proxyEventFst e ≠ proxyEventSnd e := by
  intro h
  exact (mem_proxyPairEvents.mp e.2).2.2 (Subtype.ext_iff.mp h)

/-! ### The candidate family and its total weight -/

/-- The candidate family: inside each proxy, the `repCandidates` of the fine partition.
Reused unchanged — the proxy rebuild changes the INDEX, not the candidates.-/
def proxyCandidates (F : Finpartition s) (q : ℕ) (C : ProxyIndex Q) : Finset (Finset V) :=
  repCandidates F q C.1

/--
@isnad1 id=le.0h6v.s7.4b7a27e7c5d3 from=translated src=- shape=411dd3c5 vocab=9adcb05f
-/
theorem proxyCandidates_subset_fiber (F : Finpartition s) (q : ℕ) (C : ProxyIndex Q) :
    proxyCandidates (Q := Q) F q C ⊆ F.parts.filter (· ⊆ C.1) :=
  Finset.filter_subset _ _

/-- **The candidate weight of one proxy**: the total size of its candidate fine cells.
Step 4 reasons almost entirely about this quantity and the product below.-/
noncomputable def proxyCandidateWeight (F : Finpartition s) (q : ℕ) (C : ProxyIndex Q) : ℝ :=
  ∑ A ∈ proxyCandidates (Q := Q) F q C, (A.card : ℝ)

/-- **The total selection weight**: the product of the per-proxy candidate weights.-/
noncomputable def proxyTotalCandidateWeight (F : Finpartition s) (q : ℕ)
    (Q : Finpartition s) : ℝ :=
  ∏ C : ProxyIndex Q, proxyCandidateWeight (Q := Q) F q C

/--
@isnad1 id=le.0h6v.s5.04600362ba5a from=translated src=- shape=74c4e35c vocab=22b7139e
-/
theorem proxyCandidateWeight_nonneg (F : Finpartition s) (q : ℕ) (C : ProxyIndex Q) :
    0 ≤ proxyCandidateWeight (Q := Q) F q C := by
  rw [proxyCandidateWeight]
  exact Finset.sum_nonneg fun A _ => by positivity

/--
@isnad1 id=le.0h5v.s5.4534420348a4 from=translated src=- shape=17bc0987 vocab=c0b8a3d8
-/
theorem proxyTotalCandidateWeight_nonneg (F : Finpartition s) (q : ℕ) :
    0 ≤ proxyTotalCandidateWeight F q Q := by
  rw [proxyTotalCandidateWeight]
  exact Finset.prod_nonneg fun C _ => proxyCandidateWeight_nonneg F q C

/-- **The candidate rectangle lies inside the fine-part fibers.** Stated as a weighted-mass
inequality, since that is the form both channels use — and the form later sparse, deviant
and edit charges will use.
@isnad1 id=le.0h8v.s8.8bf14b3c225f from=translated src=- shape=dabd659d vocab=c262951f
-/
theorem sum_candidateMass_le_fiberMass (F : Finpartition s) (q : ℕ)
    (pred : Finset V × Finset V → Prop) [DecidablePred pred] (C D : ProxyIndex Q) :
    ∑ p ∈ ((F.parts ×ˢ F.parts).filter pred) ∩
        (proxyCandidates (Q := Q) F q C ×ˢ proxyCandidates (Q := Q) F q D),
        ((p.1.card : ℝ) * p.2.card)
      ≤ ∑ p ∈ ((F.parts.filter (· ⊆ C.1)) ×ˢ (F.parts.filter (· ⊆ D.1))).filter pred,
          ((p.1.card : ℝ) * p.2.card) := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p _ _ => by positivity)
  rw [Finset.mem_inter, Finset.mem_product, Finset.mem_filter] at hp
  rw [Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨proxyCandidates_subset_fiber F q C hp.2.1,
    proxyCandidates_subset_fiber F q D hp.2.2⟩, hp.1.2⟩

/--
@isnad1 id=nonempty.3h6v.s7.5d62c57c0297 from=translated src=- shape=9b3d4c0d vocab=cb569c24
-/
theorem proxyCandidates_nonempty {F : Finpartition s} (hFQ : F ≤ Q) {q : ℕ}
    (hq : F.parts.card ≤ q) (C : ProxyIndex Q) (hCpos : 0 < C.1.card) :
    (proxyCandidates (Q := Q) F q C).Nonempty :=
  repCandidates_nonempty hFQ C.2 hq hCpos

/-- Each proxy's candidate weight is at least half its size, hence positive.
@isnad1 id=lt.2h6v.s6.4fec327e50a2 from=translated src=- shape=56635968 vocab=b30bb729
-/
theorem proxyCandidateWeight_pos {F : Finpartition s} (hFQ : F ≤ Q) {q : ℕ}
    (hq : F.parts.card ≤ q) (C : ProxyIndex Q) :
    0 < proxyCandidateWeight (Q := Q) F q C := by
  have hCpos : (0 : ℝ) < (C.1.card : ℝ) := by
    have := Finset.card_pos.mpr (Q.nonempty_of_mem_parts C.2)
    exact_mod_cast this
  have := half_le_sum_card_repCandidates hFQ C.2 hq
  rw [proxyCandidateWeight, proxyCandidates]
  linarith

/-- **The half-mass theorem is the weight floor.** Every proxy's candidate weight is at
least half the proxy's size, so a size floor on proxies gives the uniform `w₀` the
factorization needs.
@isnad1 id=le.2h6v.s7.5a488e09c7f4 from=translated src=- shape=c6c511be vocab=5dc81dd4
-/
theorem half_card_le_proxyCandidateWeight {F : Finpartition s} (hFQ : F ≤ Q) {q : ℕ}
    (hq : F.parts.card ≤ q) (C : ProxyIndex Q) :
    (C.1.card : ℝ) / 2 ≤ proxyCandidateWeight (Q := Q) F q C :=
  half_le_sum_card_repCandidates hFQ C.2 hq

/-- **The total selection weight is positive** — `hWpos` of the conditioned-cost form,
obtained proxy by proxy from the half-mass theorem.
@isnad1 id=lt.2h5v.s6.3256da8ca087 from=translated src=- shape=1f4e9de4 vocab=1b3f2867
-/
theorem proxyTotalCandidateWeight_pos {F : Finpartition s} (hFQ : F ≤ Q) {q : ℕ}
    (hq : F.parts.card ≤ q) :
    0 < proxyTotalCandidateWeight F q Q := by
  rw [proxyTotalCandidateWeight]
  exact Finset.prod_pos fun C _ => proxyCandidateWeight_pos hFQ hq C

/-! ### The forbidden events: nonuniform fine pairs -/

open Classical in
/-- The forbidden set, the same for every event: pairs of fine cells that are not
`ε`-uniform. Intersected with the event's own candidate rectangle by `WeightedChoice`.-/
noncomputable def nonuniformFinePairs (R : V → V → Prop) [DecidableRel R] (ε : ℝ)
    (F : Finpartition s) :
    Finset (Finset V × Finset V) :=
  (F.parts ×ˢ F.parts).filter fun p => ¬ IsUniformPair R p.1 p.2 ε

open Classical in
/-- **Step 2: the forbidden-event budget.** The `hbad` left-hand side of
`exists_piFinset_forall_not_mem_bad_cost_le`, instantiated on proxy cells and proxy-pair
events, is at most `badMassDiagNum R ε F / w₀ ^ 2` times the total selection weight. The
admissible `σ` is therefore that quotient: the aggregate mass, bounded ONCE by
`sum_proxyPair_nonuniform_le`, against the squared weight floor. No `9n²` event-count
multiplier appears — the factorization gives each event its own mass and nothing else.
@isnad1 id=le.2h8v.s8.c9ddd79ab183 from=translated src=- shape=2571311a vocab=eff53586
-/
theorem sum_proxyEvent_nonuniform_mass_le (R : V → V → Prop) [DecidableRel R] {ε : ℝ}
    (F : Finpartition s) (q : ℕ) {w₀ : ℝ} (hw₀ : 0 < w₀)
    (hW : ∀ C : ProxyIndex Q, w₀ ≤ proxyCandidateWeight (Q := Q) F q C) :
    ∑ e : ProxyEvent Q,
        ∑ p ∈ nonuniformFinePairs R ε F ∩ (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
            proxyCandidates (Q := Q) F q (proxyEventSnd e)),
          (p.1.card : ℝ) * p.2.card
          * ∏ j ∈ (Finset.univ.erase (proxyEventFst e)).erase (proxyEventSnd e),
              proxyCandidateWeight (Q := Q) F q j
      ≤ badMassDiagNum R ε F / w₀ ^ 2
        * proxyTotalCandidateWeight F q Q := by
  classical
  refine le_trans (sum_event_mass_le_of_weight_floor (proxyCandidates (Q := Q) F q)
    (fun A => (A.card : ℝ)) (fun A => by positivity) proxyEventFst proxyEventSnd
    proxyEvent_fst_ne_snd (fun _ => nonuniformFinePairs R ε F) hw₀ hW) ?_
  have hprod : (0 : ℝ) ≤ proxyTotalCandidateWeight F q Q :=
    proxyTotalCandidateWeight_nonneg F q
  refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ (by positivity)) hprod
  -- Each event's forbidden mass sits inside its own proxy pair's fine-fiber mass, so the
  -- sum over events is the aggregate — bounded once, with no event-count factor.
  have hsub : ∀ e : ProxyEvent Q,
      ∑ p ∈ nonuniformFinePairs R ε F ∩ (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
          proxyCandidates (Q := Q) F q (proxyEventSnd e)), ((p.1.card : ℝ) * p.2.card)
        ≤ ∑ p ∈ ((F.parts.filter (· ⊆ e.1.1)) ×ˢ (F.parts.filter (· ⊆ e.1.2))).filter
            (fun p => ¬ IsUniformPair R p.1 p.2 ε), ((p.1.card : ℝ) * p.2.card) := by
    intro e
    rw [nonuniformFinePairs]
    exact sum_candidateMass_le_fiberMass F q _ (proxyEventFst e) (proxyEventSnd e)
  calc ∑ e : ProxyEvent Q,
        ∑ p ∈ nonuniformFinePairs R ε F ∩ (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
          proxyCandidates (Q := Q) F q (proxyEventSnd e)), ((p.1.card : ℝ) * p.2.card)
      ≤ ∑ e : ProxyEvent Q,
          ∑ p ∈ ((F.parts.filter (· ⊆ e.1.1)) ×ˢ (F.parts.filter (· ⊆ e.1.2))).filter
            (fun p => ¬ IsUniformPair R p.1 p.2 ε), ((p.1.card : ℝ) * p.2.card) :=
        Finset.sum_le_sum fun e _ => hsub e
    _ = ∑ pd ∈ proxyPairEvents Q,
          ∑ p ∈ ((F.parts.filter (· ⊆ pd.1)) ×ˢ (F.parts.filter (· ⊆ pd.2))).filter
            (fun p => ¬ IsUniformPair R p.1 p.2 ε), ((p.1.card : ℝ) * p.2.card) :=
        Finset.sum_coe_sort (proxyPairEvents Q) (fun pd =>
          ∑ p ∈ ((F.parts.filter (· ⊆ pd.1)) ×ˢ (F.parts.filter (· ⊆ pd.2))).filter
            (fun p => ¬ IsUniformPair R p.1 p.2 ε), ((p.1.card : ℝ) * p.2.card))
    _ ≤ badMassDiagNum R ε F := sum_proxyPair_nonuniform_le R F Q

/-! ### The simultaneous forbidden budget over all palettes -/

section Palettes

variable {L : FirstOrder.Language} [FiniteRelational L]

open Classical in
/-- **The forbidden set for SIMULTANEOUS palette uniformity.** A fine pair is forbidden as
soon as it fails `ε`-uniformity for SOME palette color — the union of the per-color
forbidden sets. This is how palettes enter the forbidden channel: as a union inside `Bad`,
never as a coordinate of the event index.-/
noncomputable def paletteNonuniformFinePairs (M : FiniteRelModel L V) (ε : ℝ)
    (F : Finpartition s) : Finset (Finset V × Finset V) :=
  (F.parts ×ˢ F.parts).filter fun p =>
    ∃ c : BinaryPairPalette L, ¬ IsUniformPair (HasBinaryPairPalette M c) p.1 p.2 ε

open Classical in
/-- The union is covered color by color: every forbidden pair is forbidden for some
specific color.
@isnad1 id=ex.1h7v.s7.4d6ac0e225e0 from=translated src=- shape=016a8db5 vocab=a36ec7c2
-/
theorem exists_mem_nonuniformFinePairs {M : FiniteRelModel L V} {ε : ℝ} {F : Finpartition s}
    {p : Finset V × Finset V} (hp : p ∈ paletteNonuniformFinePairs M ε F) :
    ∃ c : BinaryPairPalette L, p ∈ nonuniformFinePairs (HasBinaryPairPalette M c) ε F := by
  rw [paletteNonuniformFinePairs, Finset.mem_filter] at hp
  obtain ⟨c, hc⟩ := hp.2
  exact ⟨c, Finset.mem_filter.mpr ⟨hp.1, hc⟩⟩

open Classical in
/-- Conversely each color's forbidden set sits inside the union. This is why simultaneous
uniformity cannot be represented by one chosen color's forbidden set; the theorem below
charges the union using the factor `K`. It says nothing about whether `K` is optimal.
@isnad1 id=le.0h7v.s6.e1431ba45dcf from=translated src=- shape=09a079c9 vocab=7eb72ba4
-/
theorem nonuniformFinePairs_subset_palette (M : FiniteRelModel L V) (ε : ℝ)
    (F : Finpartition s) (c : BinaryPairPalette L) :
    nonuniformFinePairs (HasBinaryPairPalette M c) ε F ⊆ paletteNonuniformFinePairs M ε F := by
  intro p hp
  rw [nonuniformFinePairs, Finset.mem_filter] at hp
  exact Finset.mem_filter.mpr ⟨hp.1, ⟨c, hp.2⟩⟩

open Classical in
/-- **What weighted choice actually returns.** The machine delivers `∉ Bad e`, so the
load-bearing direction is from NOT forbidden to uniformity for every color. For a pair of
fine cells the two are equivalent.
@isnad1 id=iff.1h7v.s7.2afd3419182d from=translated src=- shape=d18ebb83 vocab=25e78eb2
-/
theorem notMem_paletteNonuniformFinePairs_iff {M : FiniteRelModel L V} {ε : ℝ}
    {F : Finpartition s} {p : Finset V × Finset V} (hp : p ∈ F.parts ×ˢ F.parts) :
    p ∉ paletteNonuniformFinePairs M ε F ↔
      ∀ c : BinaryPairPalette L, IsUniformPair (HasBinaryPairPalette M c) p.1 p.2 ε := by
  rw [paletteNonuniformFinePairs, Finset.mem_filter, not_and_or]
  constructor
  · rintro (h | h) c
    · exact absurd hp h
    · exact not_not.mp (fun hc => h ⟨c, hc⟩)
  · exact fun h => Or.inr (fun ⟨c, hc⟩ => hc (h c))

open Classical in
/-- **The simultaneous forbidden-event budget.** With `Bad e` the union over palette colors
of the per-color nonuniform pairs, the `hbad` left-hand side is at most `K * B / w₀ ^ 2`
times the total selection weight, where `K = Fintype.card (BinaryPairPalette L)` and `B`
bounds each color's diagonal-inclusive bad mass. `K` is the UNION-BOUND factor obtained
from the per-palette estimates — `sum_proxyEvent_nonuniform_mass_le` applied once per
color — and not an event-count factor; no `9n²` multiplier appears. Optimality of `K` is
neither claimed nor proved.
@isnad1 id=le.3h10v.s9.b5a0dde4337c from=translated src=- shape=26462efb vocab=c01fed83
-/
theorem sum_proxyEvent_paletteNonuniform_mass_le (M : FiniteRelModel L V) {ε : ℝ}
    (F : Finpartition s) (q : ℕ) {w₀ : ℝ} (hw₀ : 0 < w₀)
    (hW : ∀ C : ProxyIndex Q, w₀ ≤ proxyCandidateWeight (Q := Q) F q C)
    {B : ℝ} (hB : ∀ c : BinaryPairPalette L,
      badMassDiagNum (HasBinaryPairPalette M c) ε F ≤ B) :
    ∑ e : ProxyEvent Q,
        ∑ p ∈ paletteNonuniformFinePairs M ε F ∩
            (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
              proxyCandidates (Q := Q) F q (proxyEventSnd e)),
          (p.1.card : ℝ) * p.2.card
          * ∏ j ∈ (Finset.univ.erase (proxyEventFst e)).erase (proxyEventSnd e),
              proxyCandidateWeight (Q := Q) F q j
      ≤ (Fintype.card (BinaryPairPalette L) : ℝ) * B / w₀ ^ 2
        * proxyTotalCandidateWeight F q Q := by
  classical
  have hprod : (0 : ℝ) ≤ proxyTotalCandidateWeight F q Q :=
    proxyTotalCandidateWeight_nonneg F q
  -- Color by color: the union's mass is at most the summed per-color masses.
  have hstep : ∀ e : ProxyEvent Q,
      ∑ p ∈ paletteNonuniformFinePairs M ε F ∩
          (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
            proxyCandidates (Q := Q) F q (proxyEventSnd e)),
        ((p.1.card : ℝ) * p.2.card
          * ∏ j ∈ (Finset.univ.erase (proxyEventFst e)).erase (proxyEventSnd e),
              proxyCandidateWeight (Q := Q) F q j)
      ≤ ∑ c : BinaryPairPalette L,
          ∑ p ∈ nonuniformFinePairs (HasBinaryPairPalette M c) ε F ∩
              (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
                proxyCandidates (Q := Q) F q (proxyEventSnd e)),
            ((p.1.card : ℝ) * p.2.card
              * ∏ j ∈ (Finset.univ.erase (proxyEventFst e)).erase (proxyEventSnd e),
                  proxyCandidateWeight (Q := Q) F q j) := by
    intro e
    refine sum_le_sum_of_exists_mem _
      (fun c => nonuniformFinePairs (HasBinaryPairPalette M c) ε F ∩
        (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
          proxyCandidates (Q := Q) F q (proxyEventSnd e))) _
      (fun p => mul_nonneg (by positivity)
        (Finset.prod_nonneg fun j _ => proxyCandidateWeight_nonneg F q j))
      (fun p hp => ?_)
    rw [Finset.mem_inter] at hp
    obtain ⟨c, hc⟩ := exists_mem_nonuniformFinePairs hp.1
    exact ⟨c, Finset.mem_inter.mpr ⟨hc, hp.2⟩⟩
  have hsum : ∑ _c : BinaryPairPalette L, B
      ≤ (Fintype.card (BinaryPairPalette L) : ℝ) * B := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  calc ∑ e : ProxyEvent Q, ∑ p ∈ paletteNonuniformFinePairs M ε F ∩ _, _
      ≤ ∑ e : ProxyEvent Q, ∑ c : BinaryPairPalette L,
          ∑ p ∈ nonuniformFinePairs (HasBinaryPairPalette M c) ε F ∩
              (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
                proxyCandidates (Q := Q) F q (proxyEventSnd e)),
            ((p.1.card : ℝ) * p.2.card
              * ∏ j ∈ (Finset.univ.erase (proxyEventFst e)).erase (proxyEventSnd e),
                  proxyCandidateWeight (Q := Q) F q j) :=
        Finset.sum_le_sum fun e _ => hstep e
    _ = ∑ c : BinaryPairPalette L, ∑ e : ProxyEvent Q,
          ∑ p ∈ nonuniformFinePairs (HasBinaryPairPalette M c) ε F ∩
              (proxyCandidates (Q := Q) F q (proxyEventFst e) ×ˢ
                proxyCandidates (Q := Q) F q (proxyEventSnd e)),
            ((p.1.card : ℝ) * p.2.card
              * ∏ j ∈ (Finset.univ.erase (proxyEventFst e)).erase (proxyEventSnd e),
                  proxyCandidateWeight (Q := Q) F q j) := Finset.sum_comm
    _ ≤ ∑ c : BinaryPairPalette L, badMassDiagNum (HasBinaryPairPalette M c) ε F / w₀ ^ 2
          * proxyTotalCandidateWeight F q Q :=
        Finset.sum_le_sum fun c _ =>
          sum_proxyEvent_nonuniform_mass_le (HasBinaryPairPalette M c) F q hw₀ hW
    _ ≤ ∑ _c : BinaryPairPalette L, B / w₀ ^ 2
          * proxyTotalCandidateWeight F q Q :=
        Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right (hB c) (by positivity)) hprod
    _ = (∑ _c : BinaryPairPalette L, B) / w₀ ^ 2
          * proxyTotalCandidateWeight F q Q := by
        rw [← Finset.sum_mul, ← Finset.sum_div]
    _ ≤ (Fintype.card (BinaryPairPalette L) : ℝ) * B / w₀ ^ 2
          * proxyTotalCandidateWeight F q Q :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hsum (by positivity)) hprod

end Palettes

/-! ### Tests -/

section Tests

-- The two event coordinates are always distinct, so `WeightedChoice`'s `hne` is available
-- for every event — including sibling events.

end Tests

end RegularityLemmata

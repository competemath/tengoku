/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Hypergraph.PolyadIncrement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Realized triads: mass identities and the block density/edit calculus

Phase 7 units 1–2 of the triadic development (design freeze in `ARCHITECTURE.md`):
a precursor built from the index and polyad test surfaces of V. Rödl, M. Schacht,
*Regular partitions of hypergraphs: Regularity lemmas*, Combin. Probab. Comput. 16
(2007) — not a formalization of their full regular-partition theorem.

The frozen conventions in action: the objects are unordered `UniformHypergraph 3 α`;
all counting surfaces are ordered injective triples; the observable
`triadObs H v = tupleRange v ∈ H.edges` is set-level, hence permutation-invariant.
The realization identity gives the total ordered mass `6 · #edges`
(`card_realizedTriples`), refined along a pair coloring `κ : RSet 2 α → Fin K` into
per-block realized counts summing back to the total (`sum_blockRealizedCount` — the
mass identity). Edits are unordered symmetric differences (`UniformHypergraph.symmDiff`);
the ordered edit mass is `6 · editCount`, proved, never assumed
(`card_editTriples`), and block densities of two hypergraphs differ by at most the
block density of their symmetric difference (`abs_blockDensity_sub_le`) — the
density/edit bridge consumed by the repair step.

The bad-key layer at the end of the file is the triadic **specialization** of the
arity-generic layer of `RegularityLemmata/Hypergraph/PolyadIncrement.lean`, at `j = 2` and
`obs = triadObs H`; the mass identities and the edit calculus above are the genuinely
triadic content, and they are not consumed by the increment.
-/

namespace RegularityLemmata

open UniformHypergraph

variable {α : Type*} [Fintype α] [DecidableEq α] {K : ℕ}

/-! ### The triadic observable and total mass -/

/-- The triadic observable: an ordered triple realizes an edge when its underlying
set is one. Set-level, hence invariant under permuting the triple.-/
def triadObs (H : UniformHypergraph 3 α) : (Fin 3 → α) → Prop :=
  fun v => tupleRange v ∈ H.edges

instance (H : UniformHypergraph 3 α) : DecidablePred (triadObs H) :=
  fun v => inferInstanceAs (Decidable (tupleRange v ∈ H.edges))

omit [Fintype α] in
/-- On injective triples the observable is the ordered realization relation.
@isnad1 id=iff.1h3v.s5.618d83469418 from=translated src=- shape=5158569a vocab=19206433
-/
theorem triadObs_iff_orderedRel {H : UniformHypergraph 3 α} {v : Fin 3 → α}
    (hv : Function.Injective v) : triadObs H v ↔ H.orderedRel v :=
  ⟨fun h => ⟨hv, h⟩, fun h => h.2⟩

omit [Fintype α] in
/-- Permutation invariance of the observable.
@isnad1 id=iff.0h4v.s6.9fd50ccff094 from=translated src=- shape=f9fc7972 vocab=ecafe167
-/
theorem triadObs_comp_perm (H : UniformHypergraph 3 α) (v : Fin 3 → α)
    (σ : Equiv.Perm (Fin 3)) : triadObs H (v ∘ σ) ↔ triadObs H v := by
  rw [triadObs, triadObs, tupleRange, tupleRange]
  rw [show Finset.univ.image (v ∘ σ) = Finset.univ.image v from by
    rw [← Finset.image_image, Finset.image_univ_of_surjective σ.surjective]]

/-- **Total realized mass**: the injective triples realizing `H` number exactly
`3! · #edges = 6 · #edges`.
@isnad1 id=eq.0h2v.s6.b720d11cb0d6 from=translated src=- shape=eed9f707 vocab=89ee9e73
-/
theorem card_realizedTriples (H : UniformHypergraph 3 α) :
    ((injectiveTuples α 3).filter (triadObs H)).card = 6 * H.edges.card := by
  have hfilter : (injectiveTuples α 3).filter (triadObs H)
      = (Fintype.piFinset fun _ : Fin 3 => (Finset.univ : Finset α)).filter
          H.orderedRel := by
    ext v
    rw [Finset.mem_filter, Finset.mem_filter, mem_injectiveTuples,
      Fintype.mem_piFinset]
    constructor
    · rintro ⟨hv, hobs⟩
      exact ⟨fun i => Finset.mem_univ _, hv, hobs⟩
    · rintro ⟨-, hv, hobs⟩
      exact ⟨hv, hobs⟩
  rw [hfilter, show ((Fintype.piFinset fun _ : Fin 3 =>
      (Finset.univ : Finset α)).filter H.orderedRel).card
      = tupleCount H.orderedRel (fun _ => Finset.univ) from rfl, orderedCount_eq]
  norm_num [Nat.factorial]

/-! ### Per-block realized counts and densities -/

/-- The realized count within one triadic block.-/
def blockRealizedCount (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (key : Fin 3 → Fin K) : ℕ :=
  ((polyadBlock κ key).filter (triadObs H)).card

/-- The density of `H` within one triadic block (guard-free: `0` on an unrealized
key).-/
noncomputable def blockDensity (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (key : Fin 3 → Fin K) : ℝ :=
  densityOn (polyadBlock κ key) (triadObs H)

/-- `0 ≤ blockDensity H κ key`: a block density is a count divided by a count. Holds on an
unrealized key too, where the density is totalized at zero. House lemma, no source;
inherited from `densityOn_nonneg`.
@isnad1 id=le.0h5v.s5.622db0de0e77 from=translated src=- shape=99ee3e75 vocab=b282cf1a
-/
theorem blockDensity_nonneg (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (key : Fin 3 → Fin K) : 0 ≤ blockDensity H κ key :=
  densityOn_nonneg

/-- `blockDensity H κ key ≤ 1`: the realized triples of a block are a subset of the block.
Holds on an unrealized key, where the density is totalized at zero. House lemma, no
source; inherited from `densityOn_le_one`.
@isnad1 id=le.0h5v.s5.f26afe6808c6 from=translated src=- shape=95d0ed59 vocab=b282cf1a
-/
theorem blockDensity_le_one (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (key : Fin 3 → Fin K) : blockDensity H κ key ≤ 1 :=
  densityOn_le_one

/-- Count/density conversion, valid for all keys (both sides `0` when the key is
unrealized).
@isnad1 id=eq.0h5v.s6.6a765cf98fc8 from=translated src=- shape=e69979d9 vocab=8a2f0354
-/
theorem cast_blockRealizedCount (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (key : Fin 3 → Fin K) :
    (blockRealizedCount H κ key : ℝ)
      = blockDensity H κ key * ((polyadBlock κ key).card : ℝ) := by
  rw [blockRealizedCount, blockDensity, densityOn]
  rcases Finset.eq_empty_or_nonempty (polyadBlock κ key) with hempty | hne
  · rw [hempty]
    simp
  · rw [div_mul_cancel₀]
    exact_mod_cast (Finset.card_pos.mpr hne).ne'

/-- **The mass identity**: block realized counts sum to the total ordered
realization mass `6 · #edges`.
@isnad1 id=eq.0h4v.s7.75c93b408003 from=translated src=- shape=f76250d6 vocab=df8c303d
-/
theorem sum_blockRealizedCount (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K) :
    ∑ key : Fin 3 → Fin K, blockRealizedCount H κ key = 6 * H.edges.card := by
  classical
  have hdisj : ∀ key ∈ (Finset.univ : Finset (Fin 3 → Fin K)),
      ∀ key' ∈ (Finset.univ : Finset (Fin 3 → Fin K)), key ≠ key' →
      Disjoint ((polyadBlock κ key).filter (triadObs H))
        ((polyadBlock κ key').filter (triadObs H)) := fun key _ key' _ h =>
    (polyadBlock_disjoint h).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  calc ∑ key : Fin 3 → Fin K, blockRealizedCount H κ key
      = (Finset.univ.biUnion fun key =>
          (polyadBlock κ key).filter (triadObs H)).card :=
        (Finset.card_biUnion hdisj).symm
    _ = ((Finset.univ.biUnion (polyadBlock κ)).filter (triadObs H)).card := by
        rw [Finset.filter_biUnion]
    _ = ((injectiveTuples α 3).filter (triadObs H)).card := by
        rw [biUnion_polyadBlock]
    _ = 6 * H.edges.card := card_realizedTriples H

/-! ### The edit calculus -/

/-- The unordered edit count between two 3-uniform hypergraphs.-/
def editCount (H G : UniformHypergraph 3 α) : ℕ :=
  (H.symmDiff G).edges.card

omit [Fintype α] in
/-- `editCount H G = editCount G H`: the symmetric difference is symmetric, so the unordered
edit count is. House lemma, no source.
@isnad1 id=eq.0h3v.s5.8eb93e3b00c1 from=translated src=- shape=f8b4d7c3 vocab=62966f0a
-/
theorem editCount_comm (H G : UniformHypergraph 3 α) :
    editCount H G = editCount G H := by
  rw [editCount, editCount]
  refine congrArg Finset.card ?_
  ext e
  rw [mem_symmDiff, mem_symmDiff]
  tauto

omit [Fintype α] in
/-- `editCount H H = 0`: a hypergraph is at edit distance zero from itself. House lemma,
no source.
@isnad1 id=eq.0h2v.s4.43a37cc03bab from=translated src=- shape=716995a1 vocab=62966f0a
-/
theorem editCount_self (H : UniformHypergraph 3 α) : editCount H H = 0 := by
  rw [editCount, Finset.card_eq_zero]
  ext e
  rw [mem_symmDiff]
  tauto

omit [Fintype α] in
/-- The disagreement observable is the observable of the symmetric difference.
@isnad1 id=iff.0h4v.s5.9721e4aecf3e from=translated src=- shape=ca7183c5 vocab=fe5101b7
-/
theorem triadObs_symmDiff (H G : UniformHypergraph 3 α) (v : Fin 3 → α) :
    triadObs (H.symmDiff G) v ↔ ¬(triadObs H v ↔ triadObs G v) := by
  rw [triadObs, triadObs, triadObs, mem_symmDiff]

/-- **The ordered edit mass and the factor 6**: injective triples witnessing a
disagreement number exactly `6 · editCount` — proved via the realization identity,
never assumed.
@isnad1 id=eq.0h3v.s7.85786a2a97b7 from=translated src=- shape=9783d990 vocab=b938d738
-/
theorem card_editTriples (H G : UniformHypergraph 3 α) :
    ((injectiveTuples α 3).filter
        fun v => ¬(triadObs H v ↔ triadObs G v)).card = 6 * editCount H G := by
  have hcongr : (injectiveTuples α 3).filter
        (fun v => ¬(triadObs H v ↔ triadObs G v))
      = (injectiveTuples α 3).filter (triadObs (H.symmDiff G)) :=
    Finset.filter_congr fun v _ => (triadObs_symmDiff H G v).symm
  rw [hcongr, card_realizedTriples, editCount]

/-- **The block density/edit bridge**: within any block, the densities of `H` and
`G` differ by at most the block density of their symmetric difference.
@isnad1 id=le.0h6v.s6.4b9218a55be9 from=translated src=- shape=be1aa937 vocab=fa3f435e
-/
theorem abs_blockDensity_sub_le (H G : UniformHypergraph 3 α)
    (κ : RSet 2 α → Fin K) (key : Fin 3 → Fin K) :
    |blockDensity H κ key - blockDensity G κ key|
      ≤ blockDensity (H.symmDiff G) κ key := by
  rw [blockDensity, blockDensity, blockDensity]
  refine le_trans abs_densityOn_sub_densityOn_le (le_of_eq ?_)
  rw [densityOn, densityOn]
  refine congrArg (· / _) ?_
  exact_mod_cast congrArg Finset.card
    (Finset.filter_congr fun v _ => (triadObs_symmDiff H G v).symm)

/-- Per-block edit mass sums to the ordered total (mass identity for edits).
@isnad1 id=eq.0h5v.s7.b8cf09230365 from=translated src=- shape=1b23e3e2 vocab=48790c0e
-/
theorem sum_blockRealizedCount_symmDiff (H G : UniformHypergraph 3 α)
    (κ : RSet 2 α → Fin K) :
    ∑ key : Fin 3 → Fin K, blockRealizedCount (H.symmDiff G) κ key
      = 6 * editCount H G :=
  sum_blockRealizedCount (H.symmDiff G) κ

/-! ### Bad keys and their mass

The triadic instance of the arity-generic bad-key layer of
`RegularityLemmata/Hypergraph/PolyadIncrement.lean`, at `j = 2` and `obs = triadObs H`. Each `_def`
lemma records the triadic normal form of a definition — `Fin 3`, `|V|³` — which is what the
rewriting downstream consumes. -/

/-- A **bad key**: `H` fails local disc regularity at the block's own density
(`IsLocalDiscRegular`, the canonical Phase 7 predicate).-/
def IsBadTriad (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K) (δ : ℝ)
    (key : Fin 3 → Fin K) : Prop :=
  IsBadPolyad κ (triadObs H) δ key

/-- Unfolding lemma: `IsBadTriad H κ δ key` is `¬ IsLocalDiscRegular κ (triadObs H) key δ`.
Consumed by rewriting in `TriadIncrement.lean`.
@isnad1 id=iff.0h6v.s6.379f81833bf1 from=translated src=- shape=b07f0203 vocab=d6b09f19
-/
theorem isBadTriad_def (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K) (δ : ℝ)
    (key : Fin 3 → Fin K) :
    IsBadTriad H κ δ key ↔ ¬ IsLocalDiscRegular κ (triadObs H) key δ :=
  Iff.rfl

/-- Unrealized keys are never bad (for `0 ≤ δ`).
@isnad1 id=not.2h6v.s7.52a4f28613a9 from=translated src=- shape=8ec4ce86 vocab=8a87d2f1
-/
theorem not_isBadTriad_of_empty_block {H : UniformHypergraph 3 α}
    {κ : RSet 2 α → Fin K} {δ : ℝ} {key : Fin 3 → Fin K}
    (h : polyadBlock κ key = ∅) (hδ : 0 ≤ δ) : ¬ IsBadTriad H κ δ key :=
  not_isBadPolyad_of_empty_block h hδ

/-- **Permutation closure of bad keys**: the observable is set-level, so all ordered
presentations of an unordered triad go bad together.
@isnad1 id=iff.0h7v.s7.dcbc784e5b0b from=translated src=- shape=383c2335 vocab=e52d66e8
-/
theorem isBadTriad_comp_perm_iff (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) (key : Fin 3 → Fin K) (σ : Equiv.Perm (Fin 3)) :
    IsBadTriad H κ δ (key ∘ ⇑σ⁻¹) ↔ IsBadTriad H κ δ key :=
  isBadPolyad_comp_perm_iff κ δ key σ fun w => triadObs_comp_perm H w σ

/-- The (ordered, diagonal-free) mass carried by the bad keys.-/
noncomputable def badTriadMassNum (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) : ℝ :=
  badPolyadMassNum κ (triadObs H) δ

open Classical in
/-- Unfolding lemma: `badTriadMassNum H κ δ` is the sum of `#(polyadBlock κ key)` over the
bad keys, in `Fin 3` normal form. Consumed by `badTriadMassNum_le_of_mass_le`.
@isnad1 id=eq.0h5v.s7.697fe3c9bc6e from=translated src=- shape=9737ebcb vocab=5531b57f
-/
theorem badTriadMassNum_def (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K) (δ : ℝ) :
    badTriadMassNum H κ δ
      = ∑ key ∈ Finset.univ.filter (fun key => IsBadTriad H κ δ key),
          ((polyadBlock κ key).card : ℝ) :=
  rfl

/-- Normalized bad mass, per the frozen `|V|³` convention (guard-free on `V = ∅`).-/
noncomputable def badTriadMass (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) : ℝ :=
  badPolyadMass κ (triadObs H) δ

/-- Unfolding lemma: `badTriadMass H κ δ = badTriadMassNum H κ δ / |V|^3` (division
totalized at zero). Consumed by `badTriadMassNum_le_of_mass_le`.
@isnad1 id=eq.0h5v.s6.65e7f637a854 from=translated src=- shape=545e308f vocab=59d782f9
-/
theorem badTriadMass_def (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K) (δ : ℝ) :
    badTriadMass H κ δ = badTriadMassNum H κ δ / (Fintype.card α : ℝ) ^ 3 :=
  rfl

/-- `0 ≤ badTriadMassNum H κ δ`: the raw bad mass is a sum of block cardinalities.
Holds for every `δ`, including negative `δ` and the empty carrier. House lemma, no
source; the `j = 2` instance of `badPolyadMassNum_nonneg`.
@isnad1 id=le.0h5v.s5.34ba320fd20c from=translated src=- shape=43c95633 vocab=17c10c00
-/
theorem badTriadMassNum_nonneg (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) : 0 ≤ badTriadMassNum H κ δ :=
  badPolyadMassNum_nonneg κ (triadObs H) δ

/-- `0 ≤ badTriadMass H κ δ`: the normalized bad mass is a nonnegative numerator over the
nonnegative `|V|^3`. Holds for every `δ` and on the empty carrier, where the quotient is
totalized at zero. House lemma, no source; the `j = 2` instance of `badPolyadMass_nonneg`.
@isnad1 id=le.0h5v.s5.42c8276fd5ce from=translated src=- shape=43c95633 vocab=14a92097
-/
theorem badTriadMass_nonneg (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) : 0 ≤ badTriadMass H κ δ :=
  badPolyadMass_nonneg κ (triadObs H) δ

/-- The bad mass is at most the total injective mass.
@isnad1 id=le.0h5v.s5.ea87ae79e53c from=translated src=- shape=73a56c11 vocab=93532386
-/
theorem badTriadMassNum_le_count (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) : badTriadMassNum H κ δ ≤ (injectiveTupleCount α 3 : ℝ) :=
  badPolyadMassNum_le_count κ (triadObs H) δ

/-- `badTriadMass H κ δ ≤ 1`: the bad mass is at most the injective triple count, which is
at most `|V|^3`. Coarse: the frozen `|V|^3` normalization exceeds the injective count
`|V|(|V|-1)(|V|-2)`, so equality never holds for `|V| ≥ 1`; on the empty carrier the
left side is totalized at zero. House lemma, no source; the `j = 2` instance of
`badPolyadMass_le_one`.
@isnad1 id=le.0h5v.s5.a3aa2ff8cfc8 from=translated src=- shape=c613e1b2 vocab=14a92097
-/
theorem badTriadMass_le_one (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) : badTriadMass H κ δ ≤ 1 :=
  badPolyadMass_le_one κ (triadObs H) δ

/-- The exceptional tuple set: all ordered triples living in a bad block.-/
noncomputable def badTriadTuples (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) : Finset (Fin 3 → α) :=
  badPolyadTuples κ (triadObs H) δ

open Classical in
/-- Unfolding lemma: `badTriadTuples H κ δ` is the union of `polyadBlock κ key` over the
bad keys. Consumed by `editTriples_subset_badTriadTuples`.
@isnad1 id=eq.0h5v.s8.0e49ee82a648 from=translated src=- shape=26643e30 vocab=893f7546
-/
theorem badTriadTuples_def (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K) (δ : ℝ) :
    badTriadTuples H κ δ
      = (Finset.univ.filter fun key => IsBadTriad H κ δ key).biUnion (polyadBlock κ) :=
  rfl

open Classical in
/-- `#(badTriadTuples H κ δ)` equals the sum of `#(polyadBlock κ key)` over the bad keys:
the blocks of distinct keys are disjoint, so the union counts without overlap. The count is
ordered and diagonal-free (blocks contain only injective triples). House lemma, no source;
the `j = 2` instance of `card_badPolyadTuples`.
@isnad1 id=eq.0h5v.s7.fead470125d4 from=translated src=- shape=994f9180 vocab=25d4b429
-/
theorem card_badTriadTuples (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) :
    (badTriadTuples H κ δ).card
      = ∑ key ∈ Finset.univ.filter (fun key => IsBadTriad H κ δ key),
          (polyadBlock κ key).card :=
  card_badPolyadTuples κ (triadObs H) δ

/-- The real cast of `#(badTriadTuples H κ δ)` is the raw bad mass `badTriadMassNum H κ δ`:
the tuple-set and key-sum views of the exceptional mass agree. Consumed by
`editCount_triadCleaned_le`. House lemma, no source; the `j = 2` instance of
`cast_card_badPolyadTuples`.
@isnad1 id=eq.0h5v.s5.c84e8a1b1ec8 from=translated src=- shape=32078164 vocab=947e4255
-/
theorem cast_card_badTriadTuples (H : UniformHypergraph 3 α) (κ : RSet 2 α → Fin K)
    (δ : ℝ) :
    ((badTriadTuples H κ δ).card : ℝ) = badTriadMassNum H κ δ :=
  cast_card_badPolyadTuples κ (triadObs H) δ

/-! ### Tests and adversarial examples -/

section Tests

-- The complete 3-graph on Fin 3 has one edge and 6 = 3! realized triples.

end Tests

end RegularityLemmata

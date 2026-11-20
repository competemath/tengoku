/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Hypergraph.Triad

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The global energy increment, triadically

Phase 7 unit 4/5 capstone (design freeze in `ARCHITECTURE.md`): when the bad keys of
a pair coloring carry more than a `δ` fraction of the triple mass, one simultaneous
cut round strictly gains more than `δ⁴` of normalized energy
(`polyadEnergy_cutRefine_gain`), and the bounded iteration reaches a weak regularization
summit (`exists_goodColoring_refining`, `exists_goodColoring`).

Every declaration here is the `j = 2`, `obs = triadObs H` instance of the arity-generic
development in `RegularityLemmata/Hypergraph/PolyadIncrement.lean`. Nothing in the increment is
specific to triples: the witness family (`badWitnessFamily`), the strict local gain
(`local_variance_gain`), the exact refinement-variance identity
(`polyadEnergyNum_comp_variance`), the cut budget `cutBound 2 K = K·2^(3K³)`, and the
normalization by `|V|³` are all instances of arity-generic statements. What remains
genuinely triadic lives in `RegularityLemmata/Hypergraph/Triad.lean` — the realization identity, the
mass identity, and the edit calculus — and none of it is consumed here.

The mathematics follows the index-increment strategy of V. Rödl, M. Schacht, *Regular
partitions of hypergraphs: Regularity lemmas*, Combin. Probab. Comput. 16 (2007); this is
a precursor built from their index and polyad test surfaces, not a formalization of their
regular-partition theorem.

The iteration is **refinement-preserving**: each round is a `cutRefine`, hence a
`ColoringRefines` step, and the projections compose along the induction, so the summit is
exported in seeded form (`exists_goodColoring_refining`) — from an arbitrary starting
coloring `κ₀`, an output that still refines it. That is what lets the summit be inserted
into a hierarchy, where `κ₀` already encodes a constructed lower level;
`exists_goodColoring` is the trivial-seed specialization.
-/

namespace RegularityLemmata

open UniformHypergraph

variable {α : Type*} [Fintype α] [DecidableEq α] {K : ℕ}

/-- The chosen simultaneous witness family: an actual witness on each bad key
(classical choice), the empty face family elsewhere.-/
noncomputable def badWitnessFamily (H : UniformHypergraph 3 α)
    (κ : RSet 2 α → Fin K) (δ : ℝ) :
    (Fin 3 → Fin K) → Fin 3 → Finset (RSet 2 α) :=
  badPolyadWitnessFamily κ (triadObs H) δ

/-- On a bad key, the chosen family is an actual witness's face system.
@isnad1 id=ex.1h6v.s7.9c19178409d6 from=translated src=- shape=0be4c49e vocab=ceaa890b
-/
theorem badWitnessFamily_spec {H : UniformHypergraph 3 α} {κ : RSet 2 α → Fin K}
    {δ : ℝ} {key : Fin 3 → Fin K} (h : IsBadTriad H κ δ key) :
    ∃ w : DiscWitness κ (triadObs H) key δ,
      badWitnessFamily H κ δ key = w.faces :=
  badPolyadWitnessFamily_spec h

/-- **The global increment**: if the bad keys carry more than a `δ` fraction of the
triple mass, one simultaneous cut round strictly gains more than `δ⁴` of normalized
energy.
@isnad1 id=lt.2h5v.s7.80a24b1b4f58 from=translated src=- shape=d6df7fa1 vocab=5faaa3d6
-/
theorem polyadEnergy_cutRefine_gain {H : UniformHypergraph 3 α}
    {κ : RSet 2 α → Fin K} {δ : ℝ} (hδ : 0 < δ)
    (hbad : δ < badTriadMass H κ δ) :
    δ ^ 4 < polyadEnergy (cutRefine κ (badWitnessFamily H κ δ)) (triadObs H)
        - polyadEnergy κ (triadObs H) :=
  polyadEnergy_cutRefine_gain_of_badPolyadMass hδ hbad

/-! ### Bounded iteration and the weak summit -/

/-- The color budget of `t` rounds of simultaneous cutting starting from `K`
colors: the exact frozen recurrence, iterating `cutBound 2`.-/
def triadRegularityBound (t K : ℕ) : ℕ := polyadRegularityBound 2 t K

/--
@isnad1 id=eq.0h1v.s3.6b1a242a7f88 from=translated src=- shape=a60e91e3 vocab=581b5414
-/
theorem triadRegularityBound_zero (K : ℕ) : triadRegularityBound 0 K = K := rfl

/--
@isnad1 id=eq.0h2v.s4.1600fe401d86 from=translated src=- shape=9122bce8 vocab=4152c99c
-/
theorem triadRegularityBound_succ (t K : ℕ) :
    triadRegularityBound (t + 1) K = triadRegularityBound t (cutBound 2 K) := rfl

/--
@isnad1 id=le.0h2v.s3.d4245d5d0116 from=translated src=- shape=86c6c8ca vocab=0849d521
-/
theorem le_triadRegularityBound (t K : ℕ) : K ≤ triadRegularityBound t K :=
  le_polyadRegularityBound 2 t K

/-- **The existential fuel theorem, refinement-preserving**: once the remaining energy
budget is below `t · δ⁴`, some coloring with at most `triadRegularityBound t K` colors
**refines the one it started from** and has bad mass at most `δ`.

Every round is a `cutRefine`, hence a refinement (`coloringRefines_cutRefine`); the
projections compose along the induction by `ColoringRefines.trans`. Preserving the
projection is what makes the summit usable when `κ` already encodes structure — a
prescribed vertex partition, a family of pair graphs, or a lower level of a complex.
@isnad1 id=ex.2h6v.s7.1a3a501e518d from=translated src=- shape=d617be86 vocab=1fa1da81
-/
theorem exists_goodColoring_of_fuel_refining {H : UniformHypergraph 3 α} {δ : ℝ}
    (hδ : 0 < δ) (t : ℕ) (K : ℕ) (κ : RSet 2 α → Fin K)
    (hbudget : 1 - polyadEnergy κ (triadObs H) ≤ (t : ℝ) * δ ^ 4) :
    ∃ (K' : ℕ) (κ' : RSet 2 α → Fin K'),
      K' ≤ triadRegularityBound t K ∧ ColoringRefines κ' κ ∧
        badTriadMass H κ' δ ≤ δ :=
  exists_goodPolyadColoring_of_fuel_refining hδ t K κ hbudget

/-- **The existential fuel theorem**: once the remaining energy budget is below
`t · δ⁴`, some coloring with at most `triadRegularityBound t K` colors has bad mass
at most `δ`. Each failing round strictly gains `δ⁴` of energy and multiplies the
colors by at most one `cutBound 2` step. The refinement-forgetting form of
`exists_goodColoring_of_fuel_refining`.
@isnad1 id=ex.2h6v.s7.0000b80c0fea from=translated src=- shape=2e28e935 vocab=6457a5b4
-/
theorem exists_goodColoring_of_fuel {H : UniformHypergraph 3 α} {δ : ℝ} (hδ : 0 < δ)
    (t : ℕ) (K : ℕ) (κ : RSet 2 α → Fin K)
    (hbudget : 1 - polyadEnergy κ (triadObs H) ≤ (t : ℝ) * δ ^ 4) :
    ∃ (K' : ℕ) (κ' : RSet 2 α → Fin K'),
      K' ≤ triadRegularityBound t K ∧ badTriadMass H κ' δ ≤ δ :=
  exists_goodPolyadColoring_of_fuel hδ t K κ hbudget

/-- The iteration fuel: `⌈1/δ⁴⌉₊` rounds suffice from any starting energy.-/
noncomputable def triadFuel (δ : ℝ) : ℕ := polyadFuel δ

/-- The host-independent color bound of the weak summit: `triadFuel δ` rounds of
`cutBound 2`, starting from the trivial `1`-coloring.-/
noncomputable def triadBound (δ : ℝ) : ℕ := polyadBound 2 δ

/-- The fuel budget is available from **any** seed coloring: the polyad energy is
nonnegative and `triadFuel δ` rounds already exhaust a budget of `1`.
@isnad1 id=le.1h5v.s6.8cc100f436df from=translated src=- shape=db0fe5e8 vocab=adc164c8
-/
theorem one_sub_polyadEnergy_le_triadFuel_mul (H : UniformHypergraph 3 α) {K₀ : ℕ}
    (κ₀ : RSet 2 α → Fin K₀) {δ : ℝ} (hδ : 0 < δ) :
    1 - polyadEnergy κ₀ (triadObs H) ≤ (triadFuel δ : ℝ) * δ ^ 4 :=
  one_sub_polyadEnergy_le_polyadFuel_mul κ₀ (triadObs H) hδ

/-- **The seeded weak triadic regularization summit**: from an arbitrary starting pair
coloring `κ₀`, a coloring that **refines** it, has at most
`triadRegularityBound (triadFuel δ) K₀` colors, and whose bad keys carry at most a `δ`
fraction of the ordered triple mass.

This is the form required to insert the summit into a hierarchy: `κ₀` may already
represent a constructed lower level, and `ColoringRefines` guarantees it survives.
`exists_goodColoring` is the trivial-seed specialization.
@isnad1 id=ex.1h5v.s6.b49202ea9429 from=translated src=- shape=9e55ae79 vocab=85093a3d
-/
theorem exists_goodColoring_refining (H : UniformHypergraph 3 α) {K₀ : ℕ}
    (κ₀ : RSet 2 α → Fin K₀) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (K' : ℕ) (κ' : RSet 2 α → Fin K'),
      K' ≤ triadRegularityBound (triadFuel δ) K₀ ∧ ColoringRefines κ' κ₀ ∧
        badTriadMass H κ' δ ≤ δ :=
  exists_goodPolyadColoring_refining κ₀ (triadObs H) hδ

/-- **The weak triadic regularization summit**: every 3-uniform hypergraph admits a
pair coloring with at most `triadBound δ` colors whose bad keys carry at most a `δ`
fraction of the ordered triple mass. A precursor to, not a formalization of, the
Rödl–Schacht regular-partition theorem (see the module docstring and the design
freeze). The trivial-seed specialization of `exists_goodColoring_refining`.
@isnad1 id=ex.1h3v.s6.37ba4d21d187 from=translated src=- shape=fc81c327 vocab=b941e227
-/
theorem exists_goodColoring (H : UniformHypergraph 3 α) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (K' : ℕ) (κ' : RSet 2 α → Fin K'),
      K' ≤ triadBound δ ∧ badTriadMass H κ' δ ≤ δ :=
  exists_goodPolyadColoring (triadObs H) hδ

/-! ### Tests and adversarial examples -/

section Tests

-- Statement-level instance of the global increment at concrete types.

end Tests

end RegularityLemmata

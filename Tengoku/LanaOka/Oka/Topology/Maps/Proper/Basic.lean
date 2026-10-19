/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Topology.Maps.Proper.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Base change of a proper map, at the set-level fibre product

Let `f : X → Z` be a proper map and `g : Y → Z` any continuous map. Then the second projection out
of `Function.Pullback f g`, Mathlib's set-level fibre product, is proper again. **No separation
axiom and no compactness is assumed of any of the three spaces.**

There is no analytic content here, so this file is a candidate for upstreaming; it lives in the
`Oka/Topology/` mirror of the Mathlib directory tree for that reason. Upstreaming to
`Mathlib/Topology/Maps/Proper/Basic.lean` costs that file **no** new imports — it is the only
module this file imports, so the cost is zero by inspection and `python3
scripts/import_cost.py Oka/Topology/Maps/Proper/Basic.lean` reports it against that target's
closure of **625** Mathlib modules.

## What Mathlib has, and the shape it does not have

`Mathlib/Topology/Maps/Proper/Basic.lean`, the one module this file imports and mirrors, has
**three** declarations that take properness of a map or of a family of maps and conclude about a
product of them: `IsProperMap.prodMap`, a binary product of proper maps; `IsProperMap.pi_map`, an
arbitrary indexed product of them, which that module's own `## Main statements` advertises; and
`IsProperMap.universally_closed`, which is `IsClosedMap (Prod.map f id)` at an arbitrary third
space. **The numeral is counted on that key and on no other**: it is two if only the declarations
*concluding* properness are counted, since `IsProperMap.universally_closed` concludes closedness,
and it is not a count of the declarations of that module mentioning a product, which would also take
in the four `isProperMap_fst_of_compactSpace`, `isProperMap_snd_of_compactSpace`,
`isClosedMap_fst_of_compactSpace` and `isClosedMap_snd_of_compactSpace`, none of which has a proper
map as a hypothesis. **None of the three is at a fibre product**, and the statement below is not an
instance of any of them: `Function.Pullback f g` is a subspace of `X × Y` and
`Function.Pullback.snd` is not `Prod.map` anything.

**And the route through a closed subspace of the product carries a separation axiom, which is why
it is not taken.** `Function.Pullback f g` is the preimage, under `Prod.map f id`, of the set
`{(z, y) | z = g y}`, which is in turn the preimage of the diagonal of `Z` under `Prod.map id g`.
That diagonal is closed when `Z` is Hausdorff — `isClosed_diagonal`, which takes `[T2Space Z]` —
and not in general, so the fibre product is not known to be a closed subspace of `X × Y` and
neither `IsProperMap.restrict` nor `IsProperMap.universally_closed` can be reached without
assuming a base separation axiom. **The characterisation used below assumes none.**

## The route: one ultrafilter, pushed forward along the first projection

`isProperMap_iff_ultrafilter` is the characterisation that makes the statement two lines of
content: `f` is proper when, for every ultrafilter on the source converging to a point `z` of the
target, some preimage of `z` is a limit of it. Given an ultrafilter `𝒰` on the fibre product with
`Function.Pullback.snd` tending to `y`, the defining equation of the fibre product —
`Function.pullback_comm_sq`, which says `f ∘ fst = g ∘ snd` — turns continuity of `g` into
`f ∘ fst` tending to `g y`, so properness of `f` supplies an `x` with `f x = g y` that
`fst 𝒰` converges to. **That `x` and `y` are a point of the fibre product precisely because
`f x = g y`**, and the convergence of `𝒰` to it is the two component convergences, since the
topology of a subspace of a product is induced by the two projections (`nhds_induced`,
`Filter.Tendsto.prodMk_nhds`).

**`Continuous g` is spent exactly once**, on `f ∘ fst` tending to `g y`, and it cannot be dropped:
with `f` the identity of `Bool`, which is proper, and `g` the identity out of the two-element
indiscrete space, which is not continuous, the projection is a continuous
bijection with finite fibres and is not a closed map.

## Main results

- `IsProperMap.pullback_snd`: **a proper map stays proper under base change along a continuous
  map.**

## What is not here

* **Nothing about the first projection.** `Function.Pullback.fst` is a base change of `g` and not
  of `f`, so reading it off the statement below means exchanging the two legs of the cospan; no
  such exchange is used or stated here, and a consumer that wants the other projection should
  state it with the cospan written the other way round.
* **No converse.** Nothing below says that a map whose every base change is proper is proper.
* **Nothing about the fibres.** Properness gives *compact* fibres and not finite ones, which is
  the distinction `Oka/AnalyticSpace/Finite.lean` is careful about; the finite-fibre half of a
  base change is `Function.Pullback.finite_fiber_snd` in `Oka/Topology/Covering/Basic.lean`, which
  assumes no topology at all. **This file imports neither of those two and neither imports it**,
  the only import here being the Mathlib module this file mirrors.
* **One consumer, and it is the one this statement was written for.** What this statement is for is
  the finiteness half of
  `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` for
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale`: `ComplexAnalytic.AnalyticSpace.IsFinite` is a
  closed base map with finite fibres, `ComplexAnalytic.AnalyticSpace.isProperMap_base_of_isFinite`
  turns that into a proper map with no separation hypothesis, and this statement is what carries it
  across the cospan. The consumer is
  `ComplexAnalytic.AnalyticSpace.isClosedMap_baseChangeSndBase`
  (`Oka/AnalyticSpace/FiniteEtaleBaseChange.lean`), and the class itself is
  `ComplexAnalytic.AnalyticSpace.isStableUnderBaseChange_isFiniteEtale`
  (`Oka/AnalyticSpace/FiniteEtaleStableUnderBaseChange.lean`). **Nothing below claims either**, and
  both are downstream of this file rather than in it.

  **This bullet was headed *No consumer in this repository yet* and closed *That base change is not
  in the tree and nothing below claims it*, until 2026-09-15.** It was exact when written and went
  false in two steps, neither of them here: `280bb67` wrote
  `ComplexAnalytic.AnalyticSpace.isClosedMap_baseChangeSndBase` from this statement, and the push
  that retires this wording added the class. **The first step was already landed when this wording
  was retired**, so what the heading denied had been false on `master` from `280bb67` onwards and
  before anything swept it — **and no census over the qualified name could have caught it**,
  because that consumer reaches this statement by projection notation on its receiver and never
  writes `IsProperMap.pullback_snd`.
-/

open Filter Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {f : X → Z} {g : Y → Z}

/-- **A proper map stays proper under base change along a continuous map.** -/
theorem IsProperMap.pullback_snd (hf : IsProperMap f) (hg : Continuous g) :
    IsProperMap (Function.Pullback.snd : f.Pullback g → Y) := by
  rw [isProperMap_iff_ultrafilter]
  refine ⟨continuous_snd.comp continuous_subtype_val, fun 𝒰 y hy ↦ ?_⟩
  have hsq : Tendsto (f ∘ (Function.Pullback.fst : f.Pullback g → X)) (𝒰 : Filter _)
      (𝓝 (g y)) := by
    rw [Function.pullback_comm_sq f g]
    exact (hg.tendsto y).comp hy
  have hsq' : Tendsto f (Ultrafilter.map Function.Pullback.fst 𝒰 : Filter X) (𝓝 (g y)) := by
    rw [Ultrafilter.coe_map, Filter.tendsto_map'_iff]
    exact hsq
  obtain ⟨x, hx, hle⟩ := (isProperMap_iff_ultrafilter.1 hf).2 hsq'
  refine ⟨⟨(x, y), hx⟩, rfl, ?_⟩
  have hval : Filter.map (Subtype.val : f.Pullback g → X × Y) (𝒰 : Filter _) ≤ 𝓝 ((x, y) : X × Y) :=
    Filter.Tendsto.prodMk_nhds (by rwa [Ultrafilter.coe_map] at hle) hy
  rw [nhds_induced]
  exact Filter.map_le_iff_le_comap.1 hval

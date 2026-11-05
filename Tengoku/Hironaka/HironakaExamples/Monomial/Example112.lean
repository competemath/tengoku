/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Hironaka.HironakaExamples.Monomial.Examples
public import Tengoku.Hironaka.Hironaka.Resolution.Algebraic.Monomial.Step3Phases
public import Tengoku.Hironaka.Hironaka.Resolution.Algebraic.Monomial.Restrict

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Kollár's Example 112 and the split example, computed

Finite computations on the concrete states of `HironakaExamples/Monomial/Examples.lean`, decided by
the kernel (`decide`, never `native_decide`):

* the maximal-multiplicity procedure `maxMultRun` is structural recursion and reduces directly;
* Kollár's Step 3 (`MonomialState.step3` of
  `Hironaka/Resolution/Algebraic/Monomial/Step3Phases.lean`) is defined by well-founded recursion on
  the measure `(m_r, n_r)` and does not reduce in the kernel, so every statement about it is read
  through the fuelled copy `step3Fuel` and the agreement theorem `step3_map_eq_of_step3Fuel`:
  `decide` evaluates `(step3Fuel 20 st).map f = some x` and the theorem transports the value to `f
  (step3 st)`; fuel `20` is ample, the longest run here having four centres;
* the measure pairs of intermediate states are read off explicit `blowUp` chains (the centres
  are those the `_centers` statements establish), and `Sub splitU splitX` is `rfl` on the six
  shared fields plus `decide` on the nerve inclusion.

What the numbers show. [Kol07, Example 112]: on a smooth surface with two curves `E¹, E²`
through a point `p` and `a₁ = a₂ = m + 1`, blowing up the point of highest multiplicity, then
`E² ∩ E³`, and so on, produces after `r - 2` steps the exponents `m + p_i`, `p_i` the `i`-th
Fibonacci number, so the multiplicities grow without bound. On the state, blowing up a face `P`
creates a component of exponent `a(P) − m`; under the maximal-multiplicity rule the chosen face
is always the newest double point `{i, i+1}`, whose sum `(m + p_i) + (m + p_{i+1})` gives the new
exponent `m + p_i + p_{i+1} = m + p_{i+2}` (`maxMult_one`, `maxMult_two`, `maxMult_three`; the
other tie-break in `maxMult_otherTieBreak_one`). Under Kollár's order, phase 1 first blows up the
curves themselves (the old component dies, the new one has exponent `a − m`), so before any
double point is touched every exponent is `< m` and the sum of the pair is `< 2m`; the bound
`(∗₁)` caps the exceptional exponent below the old ones (`total_newFace_lt` of
`Hironaka/Resolution/Algebraic/Monomial/Measure.lean`), and the run stops after at most four steps
(`step3_one`, …, `step3_ten`, with the measure traces `measure_trace_one`, `measure_trace_two`). The
three-phase instance shows the pairs `(m_s, n_s)` of the later phases never increasing while the
current one drops (`threePhase_measure`). In the split example the fine exponents `1, 0, 1, 0` give
the same two trivial blow-ups on `X` and on `U` (`split_fine_centers`, `split_restrictRun`), whereas
the coarse exponents `0, 0` on `X` leave Step 3 idle while on `U` it acts twice
(`split_coarse_runs`): the coarse procedure does not commute with the open immersion `U → X`,
which is the reason for the fine split recorded in
`Hironaka/Resolution/Algebraic/Monomial/State.lean`.

The theorems `splitX_centers`/`splitU_centers` of `HironakaExamples/MonomialRestrict.lean` are
the two halves of `split_fine_centers`, re-proved here because the root does not import the
example modules. Nothing here is used elsewhere.
-/

public section

namespace Hironaka.Monomial.Example112

open Hironaka.Monomial MonomialState Hironaka.Monomial.Examples

/-! ### The maximal-multiplicity procedure -/

/-- [Kol07, Example 112] with `m = 1`: centres and exponents of six maximal-multiplicity steps;
the exceptional exponents `3, 4, 6, 9, 14, 22` are `m + p_i` with `p_i` Fibonacci.
@isnad1 id=and.0h0v.s8.a700b7f82a8d from=translated src=- shape=3440afea vocab=7aa4f69b
-/
theorem maxMult_one :
    (maxMultRun 6 (example112 1 le_rfl)).2 =
        [{{0, 1}}, {{1, 2}}, {{2, 3}}, {{3, 4}}, {{4, 5}}, {{5, 6}}] ∧
      (List.range 8).map (maxMultRun 6 (example112 1 le_rfl)).1.a = [2, 2, 3, 4, 6, 9, 14, 22] := by
  decide

/-- [Kol07, Example 112] with `m = 2`.
@isnad1 id=and.0h0v.s8.5c269117fe63 from=translated src=- shape=96feb7de vocab=244388c4
-/
theorem maxMult_two :
    (maxMultRun 6 (example112 2 (by decide))).2 =
        [{{0, 1}}, {{1, 2}}, {{2, 3}}, {{3, 4}}, {{4, 5}}, {{5, 6}}] ∧
      (List.range 8).map (maxMultRun 6 (example112 2 (by decide))).1.a =
        [3, 3, 4, 5, 7, 10, 15, 23] := by
  decide

/-- [Kol07, Example 112] with `m = 3`.
@isnad1 id=and.0h0v.s8.a27dabfe4ed2 from=translated src=- shape=96feb7de vocab=7f037989
-/
theorem maxMult_three :
    (maxMultRun 6 (example112 3 (by decide))).2 =
        [{{0, 1}}, {{1, 2}}, {{2, 3}}, {{3, 4}}, {{4, 5}}, {{5, 6}}] ∧
      (List.range 8).map (maxMultRun 6 (example112 3 (by decide))).1.a =
        [4, 4, 5, 6, 8, 11, 16, 24] := by
  decide

/-- The other tie-break, `m = 1`: the maximal-multiplicity locus after the first step is
`{{0, 2}, {1, 2}}`, every centre of `example112OtherPath` lies in the locus of its state, and
the exponents agree.
@isnad1 id=and.0h0v.s8.6f156a29962a from=translated src=- shape=8644788a vocab=c4aa1974
-/
theorem maxMult_otherTieBreak_one :
    maxMultFaces ((example112 1 le_rfl).blowUp {{0, 1}}) = {{0, 2}, {1, 2}} ∧
      (∀ k, k < 6 → example112OtherPath.getD k ∅ ⊆
        maxMultFaces ((example112OtherPath.take k).foldl MonomialState.blowUp
          (example112 1 le_rfl))) ∧
      (List.range 8).map (example112OtherPath.foldl MonomialState.blowUp (example112 1 le_rfl)).a =
        [2, 2, 3, 4, 6, 9, 14, 22] := by
  decide

/-! ### Kollár's Step 3 on Example 112 -/

/-- Kollár's Step 3 on Example 112 with `m = 1`: four centres, the two curves and then their
exceptional components again; final maximal face sum `0`.
@isnad1 id=and.0h0v.s8.5f4c3c751a11 from=translated src=- shape=96de3166 vocab=65f6d294
-/
theorem step3_one :
    (step3 (example112 1 le_rfl)).2 = [{{0}}, {{1}}, {{2}}, {{3}}] ∧
      (List.range 6).map (step3 (example112 1 le_rfl)).1.a = [2, 2, 1, 1, 0, 0] ∧
      (step3 (example112 1 le_rfl)).1.nerve = {{4}, {5}, {4, 5}} ∧
      (step3 (example112 1 le_rfl)).1.nerve.sup (step3 (example112 1 le_rfl)).1.total = 0 :=
  ⟨step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide),
    step3_map_eq_of_step3Fuel (fuel := 20) (fun r => (List.range 6).map r.1.a) (by decide),
    step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.nerve) (by decide),
    step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.nerve.sup r.1.total) (by decide)⟩

/-- Kollár's Step 3 on Example 112 with `m = 2`: the two curves, then the remaining double
point; final maximal face sum `1`.
@isnad1 id=and.0h0v.s8.35467d6da0c9 from=translated src=- shape=5980e327 vocab=2d7e2217
-/
theorem step3_two :
    (step3 (example112 2 (by decide))).2 = [{{0}}, {{1}}, {{2, 3}}] ∧
      (List.range 5).map (step3 (example112 2 (by decide))).1.a = [3, 3, 1, 1, 0] ∧
      (step3 (example112 2 (by decide))).1.nerve = {{2}, {3}, {4}, {2, 4}, {3, 4}} ∧
      (step3 (example112 2 (by decide))).1.nerve.sup (step3 (example112 2 (by decide))).1.total =
        1 :=
  ⟨step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide),
    step3_map_eq_of_step3Fuel (fuel := 20) (fun r => (List.range 5).map r.1.a) (by decide),
    step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.nerve) (by decide),
    step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.nerve.sup r.1.total) (by decide)⟩

/-- Kollár's Step 3 on Example 112 with `m = 3`: the two curves only; final maximal face sum
`2`.
@isnad1 id=and.0h0v.s8.9934b088cd9f from=translated src=- shape=7f1ef861 vocab=a60bf4b1
-/
theorem step3_three :
    (step3 (example112 3 (by decide))).2 = [{{0}}, {{1}}] ∧
      (List.range 4).map (step3 (example112 3 (by decide))).1.a = [4, 4, 1, 1] ∧
      (step3 (example112 3 (by decide))).1.nerve = {{2}, {3}, {2, 3}} ∧
      (step3 (example112 3 (by decide))).1.nerve.sup (step3 (example112 3 (by decide))).1.total =
        2 :=
  ⟨step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide),
    step3_map_eq_of_step3Fuel (fuel := 20) (fun r => (List.range 4).map r.1.a) (by decide),
    step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.nerve) (by decide),
    step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.nerve.sup r.1.total) (by decide)⟩

/-- Kollár's Step 3 on Example 112 with `m = 5`.
@isnad1 id=and.0h0v.s8.628ff10a2736 from=translated src=- shape=7f1ef861 vocab=9cc584c0
-/
theorem step3_five :
    (step3 (example112 5 (by decide))).2 = [{{0}}, {{1}}] ∧
      (List.range 4).map (step3 (example112 5 (by decide))).1.a = [6, 6, 1, 1] ∧
      (step3 (example112 5 (by decide))).1.nerve = {{2}, {3}, {2, 3}} ∧
      (step3 (example112 5 (by decide))).1.nerve.sup (step3 (example112 5 (by decide))).1.total =
        2 :=
  ⟨step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide),
    step3_map_eq_of_step3Fuel (fuel := 20) (fun r => (List.range 4).map r.1.a) (by decide),
    step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.nerve) (by decide),
    step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.nerve.sup r.1.total) (by decide)⟩

/-- Kollár's Step 3 on Example 112 with `m = 10`.
@isnad1 id=and.0h0v.s8.03676b43fdaf from=translated src=- shape=7f1ef861 vocab=39df7d79
-/
theorem step3_ten :
    (step3 (example112 10 (by decide))).2 = [{{0}}, {{1}}] ∧
      (List.range 4).map (step3 (example112 10 (by decide))).1.a = [11, 11, 1, 1] ∧
      (step3 (example112 10 (by decide))).1.nerve = {{2}, {3}, {2, 3}} ∧
      (step3 (example112 10 (by decide))).1.nerve.sup (step3 (example112 10 (by decide))).1.total =
        2 :=
  ⟨step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide),
    step3_map_eq_of_step3Fuel (fuel := 20) (fun r => (List.range 4).map r.1.a) (by decide),
    step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.nerve) (by decide),
    step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.nerve.sup r.1.total) (by decide)⟩

/-- `m = 1`: the measure pairs `((m_1, n_1), (m_2, n_2))` along the run.
@isnad1 id=eq.0h0v.s9.d09be03b9fe0 from=translated src=- shape=c081bbae vocab=a63086bf
-/
theorem measure_trace_one :
    [example112 1 le_rfl, (example112 1 le_rfl).blowUp {{0}},
        ((example112 1 le_rfl).blowUp {{0}}).blowUp {{1}},
        (((example112 1 le_rfl).blowUp {{0}}).blowUp {{1}}).blowUp {{2}},
        ((((example112 1 le_rfl).blowUp {{0}}).blowUp {{1}}).blowUp {{2}}).blowUp {{3}}].map
        (fun st => [1, 2].map fun s => ofLex (st.measure s)) =
      [[(2, 2), (4, 1)], [(2, 1), (3, 1)], [(1, 2), (2, 1)], [(1, 1), (1, 1)],
        [(0, 2), (0, 1)]] := by
  decide

/-- `m = 2`: the measure pairs `((m_1, n_1), (m_2, n_2))` along the run.
@isnad1 id=eq.0h0v.s8.a3bce2a7264a from=translated src=- shape=09b57a00 vocab=37aada76
-/
theorem measure_trace_two :
    [example112 2 (by decide), (example112 2 (by decide)).blowUp {{0}},
        ((example112 2 (by decide)).blowUp {{0}}).blowUp {{1}},
        (((example112 2 (by decide)).blowUp {{0}}).blowUp {{1}}).blowUp {{2, 3}}].map
        (fun st => [1, 2].map fun s => ofLex (st.measure s)) =
      [[(3, 2), (6, 1)], [(3, 1), (4, 1)], [(1, 2), (2, 1)], [(1, 2), (1, 2)]] := by
  decide

/-! ### The three-phase instance -/

/-- The three centres, one per phase.
@isnad1 id=eq.0h0v.s6.f5c287d9da08 from=translated src=- shape=1087a97d vocab=4e1ac850
-/
theorem threePhase_centers : (step3 threePhase).2 = [{{1}}, {{2, 3}}, {{3, 4, 5}}] :=
  step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide)

/-- The exponents after the run.
@isnad1 id=eq.0h0v.s6.efe2feccb583 from=translated src=- shape=acbd73f4 vocab=4c48fc48
-/
theorem threePhase_a : (List.range 7).map (step3 threePhase).1.a = [4, 9, 3, 6, 1, 1, 0] :=
  step3_map_eq_of_step3Fuel (fuel := 20) (fun r => (List.range 7).map r.1.a) (by decide)

/-- The final maximal face sum, `7 < m = 8`.
@isnad1 id=eq.0h0v.s5.671ab8af73a9 from=translated src=- shape=a2296acd vocab=c6eb32bf
-/
theorem threePhase_maxOrd : (step3 threePhase).1.nerve.sup (step3 threePhase).1.total = 7 :=
  step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.nerve.sup r.1.total) (by decide)

/-- The four measure vectors `((m_s, n_s))_{s = 1, 2, 3}` along the run: the current pair drops
and no later pair increases.
@isnad1 id=and.0h0v.s9.f438343ecce1 from=translated src=- shape=014f8600 vocab=d3d38d23
-/
theorem threePhase_measure :
    [1, 2, 3].map (fun s => ofLex (threePhase.measure s)) = [(9, 1), (15, 1), (18, 1)] ∧
      [1, 2, 3].map (fun s => ofLex ((threePhase.blowUp {{1}}).measure s)) =
        [(6, 1), (9, 1), (10, 1)] ∧
      [1, 2, 3].map (fun s => ofLex (((threePhase.blowUp {{1}}).blowUp {{2, 3}}).measure s)) =
        [(6, 1), (7, 2), (8, 1)] ∧
      [1, 2, 3].map (fun s =>
          ofLex ((((threePhase.blowUp {{1}}).blowUp {{2, 3}}).blowUp {{3, 4, 5}}).measure s)) =
        [(6, 1), (7, 2), (7, 2)] := by
  decide

/-! ### The split example -/

/-- The fine runs on `X` and on `U` blow up `V(x)` and then `V(y)` alike.
@isnad1 id=and.0h0v.s7.30680ab94c65 from=translated src=- shape=b2246810 vocab=400c6c7e
-/
theorem split_fine_centers :
    (step3 splitX).2 = [{{0}}, {{2}}] ∧ (step3 splitU).2 = [{{0}}, {{2}}] :=
  ⟨step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide),
    step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide)⟩

/-- Both fine runs end with maximal face sum `0`.
@isnad1 id=and.0h0v.s6.418385bae80d from=translated src=- shape=5da9fae5 vocab=149c9277
-/
theorem split_fine_maxOrd :
    (step3 splitX).1.nerve.sup (step3 splitX).1.total = 0 ∧
      (step3 splitU).1.nerve.sup (step3 splitU).1.total = 0 :=
  ⟨step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.nerve.sup r.1.total) (by decide),
    step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.nerve.sup r.1.total) (by decide)⟩

/-- `U` is the restriction of `X` in the sense of
`Hironaka/Resolution/Algebraic/Monomial/Restrict.lean`.
@isnad1 id=sub.0h0v.s1.b6c9a62bd6f9 from=translated src=- shape=25b03439 vocab=136627f9
-/
theorem split_sub : Sub splitU splitX := ⟨rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- The run on `X` pulled back to `U` is the direct run on `U`.
@isnad1 id=eq.0h0v.s4.1821dd3cdaf3 from=translated src=- shape=9bb6e27f vocab=4bdf784a
-/
theorem split_restrictRun : restrictRun splitU (step3 splitX).2 = (step3 splitU).2 := by
  rw [split_fine_centers.1, split_fine_centers.2]
  decide

/-- The coarse runs differ: idle on `X`, two blow-ups on `U`.
@isnad1 id=and.0h0v.s6.bbb53cb17f24 from=translated src=- shape=61f45391 vocab=cc1923b2
-/
theorem split_coarse_runs : (step3 coarseX).2 = [] ∧ (step3 coarseU).2 = [{{0}}, {{1}}] :=
  ⟨step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide),
    step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide)⟩

end Hironaka.Monomial.Example112

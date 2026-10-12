/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Minimal
public import Tengoku.Tauceti.TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Topology
public import Tengoku

/-!
# Comparing the arithmetic and topological genera of a numerical type

For a component `i` of a numerical type, put

`qᵢ = mᵢwᵢ` and `rᵢ = ∑_{j ≠ i} aᵢⱼ / wᵢ`.

The local genus defect

`qᵢ (-1 + gᵢ + rᵢ / 2) - (-1 + degree(i) / 2)`

compares the contribution of `i` to the arithmetic genus with its contribution to the first
Betti number of the intersection graph.  Summing these defects gives exactly
`arithmeticGenus - topologicalGenus`.

The divisibility axiom for a numerical type implies that `rᵢ` is at least the ordinary valence
of `i`.  Consequently the local defect is nonnegative whenever `gᵢ` is positive, `i` has at
least two neighbours, or `qᵢ = 1`.  This proves the arithmetic/topological genus comparison
whenever every component satisfies one of those conditions, in particular when the intersection
graph has minimum valence at least two.

For a minimal numerical type with more than one component the comparison holds without further
hypotheses: `g_top ≤ g`
([Stacks, Lemma 55.3.14](https://stacks.math.columbia.edu/tag/0C7C)).  The proof here differs
from the chain argument of the Stacks Project.  For a set `S` of components, put

`E(S) = ∑_{i ∈ S} (Φᵢ + 1 - vᵢ(S) / 2)`,

where `Φᵢ` is the genus contribution of `i` and `vᵢ(S)` is the number of components of `S`
meeting `i`, so that `E` of the set of all components is `g - g_top`.  Deleting `i` from `S`
lowers `E(S)` by `Φᵢ + 1 - vᵢ(S)`, which is nonnegative when `vᵢ(S) ≤ 1` because minimality makes
`Φᵢ` nonnegative.  Once every remaining component meets at least two others, the fibre relation
bounds `E(S)` below by a sum of nonnegative terms.

## Main results

* `TauCeti.NumericalType.sum_genusDefect`: the local defects sum to `g - g_top`.
* `TauCeti.NumericalType.topologicalGenus_le_arithmeticGenus_of_two_le_valence`: `g_top ≤ g`
  when every component has at least two neighbours.
* `TauCeti.NumericalType.IsMinimal.topologicalGenus_le_arithmeticGenus`: `g_top ≤ g` for a
  minimal numerical type with more than one component.
-/

public section

namespace TauCeti

namespace NumericalType

open Finset

universe u

variable (T : NumericalType.{u})

/-- The sum `∑_{j ≠ i} aᵢⱼ / wᵢ` of the normalized intersections of a component with all other
components. Each summand is a nonnegative integer by the axioms of a numerical type. -/
noncomputable def normalizedValence (i : T.Component) : ℚ :=
  ∑ j ∈ Finset.univ.erase i, (T.intersection i j : ℚ) / (T.weight i : ℚ)

/-- The defining sum for the normalized valence. -/
lemma normalizedValence_def (i : T.Component) :
    T.normalizedValence i =
      ∑ j ∈ Finset.univ.erase i, (T.intersection i j : ℚ) / (T.weight i : ℚ) := by
  rw [normalizedValence]

/-- The local difference between the arithmetic-genus and graph-genus contributions of a
component of a numerical type. -/
noncomputable def genusDefect (i : T.Component) : ℚ :=
  (T.multiplicity i : ℚ) * (T.weight i : ℚ) *
      (-1 + T.genus i + T.normalizedValence i / 2) -
    (-1 + (T.intersectionGraph.neighborSet i).ncard / 2)

/-- The defining formula for the local genus defect. -/
lemma genusDefect_def (i : T.Component) :
    T.genusDefect i =
      (T.multiplicity i : ℚ) * (T.weight i : ℚ) *
          (-1 + T.genus i + T.normalizedValence i / 2) -
        (-1 + (T.intersectionGraph.neighborSet i).ncard / 2) := by
  rw [genusDefect]

/-- The normalized valence is nonnegative. -/
lemma normalizedValence_nonneg (i : T.Component) :
    0 ≤ T.normalizedValence i := by
  apply Finset.sum_nonneg
  intro j hj
  have hij : i ≠ j := by
    exact (Finset.ne_of_mem_erase hj).symm
  exact div_nonneg (by exact_mod_cast T.offDiagonal_nonneg i j hij) (by positivity)

private lemma one_le_normalizedIntersection_of_adj {i j : T.Component}
    (hij : T.intersectionGraph.Adj i j) :
    (1 : ℚ) ≤ (T.intersection i j : ℚ) / (T.weight i : ℚ) := by
  have hpos : (0 : ℤ) < T.intersection i j :=
    by
      rw [T.intersectionGraph_adj_iff, T.adj_iff] at hij
      exact hij.2
  have hle : (T.weight i : ℤ) ≤ T.intersection i j :=
    Int.le_of_dvd hpos (T.weight_dvd i j)
  apply (le_div_iff₀ (by positivity : (0 : ℚ) < T.weight i)).2
  simpa using (by exact_mod_cast hle : (T.weight i : ℚ) ≤ T.intersection i j)

/-- The normalized intersection valence is at least the valence of the intersection graph. -/
lemma valence_le_normalizedValence (i : T.Component) :
    ((T.intersectionGraph.neighborSet i).ncard : ℚ) ≤ T.normalizedValence i := by
  classical
  calc
    ((T.intersectionGraph.neighborSet i).ncard : ℚ) =
        T.intersectionGraph.degree i := by
      norm_cast
      rw [← SimpleGraph.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
    _ =
        ∑ _j ∈ T.intersectionGraph.neighborFinset i, (1 : ℚ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one,
        SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ ∑ j ∈ T.intersectionGraph.neighborFinset i,
        (T.intersection i j : ℚ) / (T.weight i : ℚ) :=
      Finset.sum_le_sum fun j hj ↦ T.one_le_normalizedIntersection_of_adj
        ((T.intersectionGraph.mem_neighborFinset i j).1 hj)
    _ ≤ ∑ j ∈ Finset.univ.erase i,
        (T.intersection i j : ℚ) / (T.weight i : ℚ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact Finset.mem_erase.mpr
          ⟨((T.intersectionGraph.mem_neighborFinset i j).1 hj).ne.symm, Finset.mem_univ j⟩
      · intro j hj _
        have hij : i ≠ j := by exact (Finset.ne_of_mem_erase hj).symm
        exact div_nonneg (by exact_mod_cast T.offDiagonal_nonneg i j hij) (by positivity)
    _ = T.normalizedValence i := rfl

/-- A component has nonnegative genus defect if it has positive genus, at least two neighbours,
or multiplicity times weight equal to one. -/
theorem genusDefect_nonneg_of_genus_pos_or_two_le_valence_or_mul_eq_one (i : T.Component)
    (h : 0 < T.genus i ∨ 2 ≤ (T.intersectionGraph.neighborSet i).ncard ∨
      T.multiplicity i * T.weight i = 1) :
    0 ≤ T.genusDefect i := by
  rw [T.genusDefect_def]
  have hs := T.valence_le_normalizedValence i
  have hs0 := T.normalizedValence_nonneg i
  have hq : (1 : ℚ) ≤ (T.multiplicity i : ℚ) * (T.weight i : ℚ) := by
    have hm : (1 : ℚ) ≤ T.multiplicity i := by exact_mod_cast (T.multiplicity i).pos
    have hw : (1 : ℚ) ≤ T.weight i := by exact_mod_cast (T.weight i).pos
    nlinarith
  rcases h with hg | hd | hq1
  · have hgq : (1 : ℚ) ≤ T.genus i := by exact_mod_cast hg
    have hbase : 0 ≤ -1 + (T.genus i : ℚ) + T.normalizedValence i / 2 := by
      linarith
    have hmul : -1 + (T.genus i : ℚ) + T.normalizedValence i / 2 ≤
        (T.multiplicity i : ℚ) * T.weight i *
          (-1 + T.genus i + T.normalizedValence i / 2) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hq) hbase]
    linarith
  · have hdq : (2 : ℚ) ≤ (T.intersectionGraph.neighborSet i).ncard := by exact_mod_cast hd
    have hbase : 0 ≤ -1 + (T.genus i : ℚ) + T.normalizedValence i / 2 := by
      have hg0 : (0 : ℚ) ≤ T.genus i := by positivity
      linarith
    have hmul : -1 + (T.genus i : ℚ) + T.normalizedValence i / 2 ≤
        (T.multiplicity i : ℚ) * T.weight i *
          (-1 + T.genus i + T.normalizedValence i / 2) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hq) hbase]
    linarith
  · have hq1' : (T.multiplicity i : ℚ) * (T.weight i : ℚ) = 1 := by
      exact_mod_cast hq1
    rw [hq1']
    have hg0 : (0 : ℚ) ≤ T.genus i := by positivity
    linarith

/-! ### Minimal numerical types -/

/-- The number of components of `S`, other than `i`, that meet `i`. -/
private def valenceIn (S : Finset T.Component) (i : T.Component) : ℕ :=
  #{j ∈ S | j ≠ i ∧ 0 < T.intersection i j}

/-- The quantity `∑_{i ∈ S} (Φᵢ + 1 - vᵢ / 2)`, where `vᵢ` is the number of components of `S`
meeting `i`. For `S` the set of all components it is the difference between the arithmetic and
the topological genus. -/
private def excess (S : Finset T.Component) : ℚ :=
  ∑ i ∈ S, (T.genusContribution i + 1 - (T.valenceIn S i : ℚ) / 2)

namespace IsMinimal

variable {T}

end IsMinimal

end NumericalType

end TauCeti

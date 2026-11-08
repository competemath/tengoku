module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerDefs
public import Tengoku.Seed.Data.Fin.Embedding
public import Tengoku.Seed.Data.Fintype.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Derived Steiner systems

The weight-8 words of the (extended) Golay code yield the Witt design `S(5,8,24)`. Fixing two
coordinates (e.g. `0` and `1`) and puncturing yields the derived design `S(3,6,22)`.

This file provides the basic combinatorial plumbing relating blocks in `Fin 24` containing
`{0,1}` to `6`-subsets of `Fin 22` via `Fin.addNatEmb 2`.

## Main definitions
* `drop2`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

/--
Drop the first two coordinates `0` and `1` of a block `B : Finset (Fin 24)`, reindexing the
remaining points as `Fin 22` via `Fin.addNatEmb 2`.-/
@[expose] public def drop2 (B : Finset (Fin 24)) : Finset (Fin 22) :=
  Finset.univ.filter fun i : Fin 22 => (Fin.addNatEmb 2 i) ∈ B

/-- Membership in `drop2 B` is membership in `B` after embedding into `Fin 24`.-/
@[simp] public lemma mem_drop2 (B : Finset (Fin 24)) (i : Fin 22) :
    i ∈ drop2 B ↔ (Fin.addNatEmb 2 i) ∈ B := by
  simp [drop2]

private lemma two_le_val_of_ne_zero_one (j : Fin 24) (hj0 : j ≠ 0) (hj1 : j ≠ 1) :
    2 ≤ (j : ℕ) := by
  by_contra h
  have hjle : (j : ℕ) ≤ 1 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge h)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hjle with h0 | h1
  · exact hj0 (Fin.ext (by simp [h0]))
  · exact hj1 (Fin.ext (by simp [h1]))

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

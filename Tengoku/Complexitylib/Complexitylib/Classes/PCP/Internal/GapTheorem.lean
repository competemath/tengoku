/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.Dinur
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.ExpanderExists
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.FamilyFin
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.GapReduction

/-!
# Dinur's gap theorem for 3-SAT

The mathematical conclusion of the development. Every 3CNF formula is turned
into a constraint graph over a fixed constant-size alphabet, of size polynomial
in the formula, which is satisfiable when the formula is and whose
unsatisfiability value is at least a universal constant when it is not.

Three ingredients meet: the reduction of `ThreeSATCSP` carried across alphabets
by `GapReduction`, the explicit expander family `algFamily` of `FamilyFin` (a
numbered tower over a constant-size base picked once by
`Classical.choose exists_finBase`), and the amplifier of `Dinur`, whose
`dichotomy` supplies the gap after logarithmically many rounds.

This module states the gap theorem as a reduction in the mathematical sense:
`gapGraph` is a `noncomputable` definition and no running time is claimed here.
The polynomial-time implementation is elsewhere: `exists_pcp_of_mem_NP` in
`Complexitylib.Classes.PCP.Internal.AlgPCP` runs the same amplifier over the
same tower (`Dinur.amplifier (algF.toFamily algHd)`, with `algF = algBase`) and
packages it as a `PCPVerifier` with an `FP` query function and a `P` verdict.

## Main definitions

- `Complexity.dinurAmp` — Dinur's amplifier, with the expander supplied
- `Complexity.gapGraph` — the gap graph of a formula

## Main results

- `Complexity.satisfiable_gapGraph` — completeness
- `Complexity.gap_le_unsatVal_gapGraph` — soundness, with a universal gap
- `Complexity.numEdges_gapGraph_le` — the size bound
-/

@[expose] public section

namespace Complexity

open ThreeSATCSP SAT

/-- How many rounds of amplification a formula needs: enough that the doubling
of the unsatisfiability value reaches the threshold, which is the bit length of
the edge count. -/
def gapRounds (φ : CNF) : ℕ := Nat.log 2 (3 * φ.length) + 1

theorem numEdges_baseCSP_le_pow_rounds (φ : CNF) :
    (baseCSP φ).numEdges ≤ 2 ^ gapRounds φ := by
  rw [numEdges_baseCSP, gapRounds]
  exact Nat.le_of_lt (Nat.lt_pow_succ_log_self (by omega) _)

/-- A bit length costs at most a doubling. -/
theorem two_pow_log_succ_le (n : ℕ) : 2 ^ (Nat.log 2 n + 1) ≤ 2 * n + 2 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · have hlow : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
    omega

end Complexity

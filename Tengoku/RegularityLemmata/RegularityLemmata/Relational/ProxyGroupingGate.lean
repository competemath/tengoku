/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Graph.BadMass
import Tengoku.RegularityLemmata.RegularityLemmata.Graph.FamilyRegularity
import Tengoku.RegularityLemmata.RegularityLemmata.Partition.Equitable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Route (b) ladder step 2: the proxy partition must GROUP, not SPLIT

`ARCHITECTURE.md` route (b) ladder step 2 (2026-07-28). The clone/proxy checkpoint was
scoped as "construct the three-way proxy partition" by SPLITTING each coarse cell. This
file records why that direction hits the checkpoint's own hard stop, and why the opposite
direction does not.

## The obstruction

Representative selection over ordered distinct PROXY pairs must cover **sibling** pairs —
two proxies of the same coarse owner. If the proxies are obtained by splitting a cell `C`
of an already-regular partition, the sibling pair `(C⁽⁰⁾, C⁽¹⁾)` is a pair of subsets of one
cell, and **off-diagonal regularity of the original partition says nothing about it**.
Splitting does not inherit: gate **G-P1** below exhibits a partition that is off-diagonally
regular while a split of one of its cells produces a sibling pair that is not
`1/4`-uniform.

Nor can the gap be filled by diagonal-inclusive regularity in general: for the strict order
on any linearly ordered set, `(W, W)` fails `1/4`-uniformity whenever `|W| ≥ 2` (gate
G-U5, `RegularityLemmata/Graph/UniformUnion.lean`), so a diagonal-inclusive regular partition at
tolerance below `1/4` must be almost all singletons — no bounded part count survives. That is
exactly the "unavailable self-regularity" the checkpoint's hard stop names.

## The resolution: group instead of split

Sibling-pair regularity is available if the proxies are **cells of the regular partition
itself**, grouped into owners, rather than pieces carved out of its cells:

* run the supplier to obtain an equipartition `Q` that is family-regular **off-diagonally**;
* define coarse owners by grouping the cells of `Q` in threes — a coarse cell is the union
  of its three proxies;
* then a sibling pair is a pair of DISTINCT cells of `Q`, hence an ordinary off-diagonal
  event, already controlled (gate **G-P2**: distinct cells of a partition are exactly the
  pairs off-diagonal regularity speaks about).

This is the same equal-size, off-diagonal discipline the supplier was built for, and it
needs no diagonal control anywhere. G-U5 does not apply: it refutes `(W, W)`, not a pair of
two disjoint cells.

## The consequence for the tolerance

Grouping changes the event count, and the envelope must be derived before any tolerance is
chosen. With `3n` proxies instead of `n` owners, the ordered distinct pairs are `3n(3n−1)`,
which sits under a **`9n²` envelope** (`card_ordered_pairs_grouped_le`). That is an
envelope, NOT a ninefold factor over the coarse count `n(n−1)`: the ratio to `n(n−1)`
exceeds `9` for small `n` — at `n = 3` it is `72/6 = 12` — and only approaches `9` as `n`
grows. A selection tolerance is chosen against `9n²`, and — as before — must not depend on
the produced complexity.

## Two prerequisites the grouping inherits

* **Owner sizes.** Three cells of size `m` or `m+1` give `3m ≤ |owner| ≤ 3m + 3`, and the
  intermediate values `3m+1`, `3m+2` do occur — mixed triples are the normal case, not an
  edge case. The size floor must be stated in multiplication form against that range, never
  as an exact `3m` or `3m+3`.
* **Divisibility.** Grouping the cells of `Q` in threes needs `3 ∣ #Q.parts`, which the
  family-regularity summit does NOT currently guarantee: it delivers `l ≤ #parts ≤ bound`,
  and the reachable counts are the iterates of `familyStepBound` from the initial floor.
  The likely acyclic fix is to seed the iteration at a multiple of three — since
  `familyStepBound n = n · familyChunksPerPart n`, every step then preserves divisibility
  (`three_dvd_familyStepBound`), so all reachable part counts stay divisible by `3`. This
  is recorded as a prerequisite, not discharged here.

**Nothing is constructed here.** No partition, no representatives, no rounding, no
cleaning. The checkpoint's commit 1 should be re-specified as a grouping before it is
attempted.
-/

namespace RegularityLemmata

/-! ### G-P1 — splitting does not inherit sibling-pair regularity -/

section GateP1

/-- A relation on `Fin 4` that is irregular inside `{0,1,2,3}`: `0 → 2` and `1 → 3` only.-/
private abbrev splitRel : Fin 4 → Fin 4 → Prop :=
  fun a b => (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 3)

-- The one-cell partition of the host is off-diagonally regular for FREE: `IsBadPair`
-- demands two DISTINCT cells, and there is only one, so the bad mass is zero.

end GateP1

/-! ### G-P2 — grouping keeps sibling pairs off-diagonal -/

section GateP2

variable {α : Type*} [DecidableEq α] {s : Finset α}

omit [DecidableEq α] in
/-- **The grouping design, stated.** Two DISTINCT cells of a partition are exactly the
configuration off-diagonal regularity speaks about: `IsBadPair` is defined on distinct
cells, so a clean such pair is uniform for the relation. Grouping cells of an
already-regular partition into owners therefore leaves sibling pairs inside the existing
event index — sibling proxies are distinct cells — with no diagonal control required.
@isnad1 id=isunifor.2h5v.s5.0f46f4455a7e from=translated src=- shape=d64e9fd0 vocab=c9b927a5
-/
theorem isUniformPair_of_not_isBadPair {R : α → α → Prop} [DecidableRel R] {ε : ℝ}
    {A B : Finset α} (hAB : A ≠ B) (h : ¬ IsBadPair R ε A B) : IsUniformPair R A B ε := by
  by_contra hcon
  exact h ⟨hAB, hcon⟩

end GateP2

/-! ### The event-count factor of grouping -/

/-- **The grouping envelope.** Three proxies per owner turn `n` owners into `3n` proxies,
whose ordered distinct pairs number `3n(3n−1)` — under a `9n²` envelope. This is an
envelope on the proxy count itself, NOT a ninefold factor over the coarse count `n(n−1)`:
that ratio exceeds `9` for small `n`. The selection tolerance is chosen against `9n²`, and
only after this is known.
@isnad1 id=le.0h1v.s6.969e49d2dce8 from=translated src=- shape=019ebfc3 vocab=3027adc6
-/
theorem card_ordered_pairs_grouped_le (n : ℕ) :
    3 * n * (3 * n - 1) ≤ 9 * (n * n) := by
  cases n with
  | zero => simp
  | succ m =>
    have h : 3 * (m + 1) - 1 = 3 * m + 2 := by omega
    rw [h]
    nlinarith

/-- The proxy pair count dominates the coarse one, so the envelope is an increase and not
a re-description of the same events. No factor is claimed here.
@isnad1 id=le.0h1v.s6.4e637628541e from=translated src=- shape=9044f7cb vocab=3027adc6
-/
theorem card_ordered_pairs_coarse_le (n : ℕ) : n * (n - 1) ≤ 3 * n * (3 * n - 1) := by
  cases n with
  | zero => simp
  | succ m =>
    have h : 3 * (m + 1) - 1 = 3 * m + 2 := by omega
    have h2 : m + 1 - 1 = m := by omega
    rw [h, h2]
    exact Nat.mul_le_mul (by omega) (by omega)

/-! ### Tests -/

section Tests

-- At 3 owners: 9 proxies, 72 ordered distinct proxy pairs against 6 coarse ones — a ratio
-- of 12, which is why the bound is stated as a `9n²` ENVELOPE and not as a ninefold factor
-- over the coarse count.

end Tests

end RegularityLemmata

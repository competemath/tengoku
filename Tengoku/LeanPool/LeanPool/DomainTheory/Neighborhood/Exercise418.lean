/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.Example43
public import Tengoku

/-!
# Exercise 4.18 (Scott 1981, PRG-19, Lecture IV)

*In Example 4.3 there are many unproved assertions about `N` and `F`. These should
be checked.*

`Example43.lean` builds the natural-number domain `N`, the total elements `n̂ =
natElem n`, and the
structure maps `succ`, `pred`, `zero` with their value equations. This file
discharges the remaining
*structural* assertions Scott leaves implicit:

* **Element classification** (`element_classification`): `|N|` consists of exactly
`⊥` and the total
  elements `n̂` — `N` is genuinely the *flat* domain over `ℕ`. (This is the
  assertion that makes `N`
  "THE domain of integers".)
* **Peano's axioms for the total elements** `⟨{n̂}, 0̂, succ⟩`:
  - `natElem_injective` / `succMap_injective`: distinct numerals are distinct
  elements, and `succ` is
    one-one;
  - `natElem_zero_ne_succ` / `zero_ne_succMap`: `0̂` is not a successor;
  - `predMap_succMap_natElem` (already in `Example43`): `pred ∘ succ = id` on
  numerals.

The classification is classical (it decides whether `x` contains a singleton,
exactly as Example 4.3's
`zeroMap` is classical); the injectivity / zero-is-not-a-successor facts are
**choice-free**.
-/

@[expose] public section

namespace Domain.Neighborhood.Exercise418

open Domain.Neighborhood NeighborhoodSystem ApproximableMap Example43

/-- `∅` is not a neighbourhood of `N`.
@isnad1 id=not.0h0v.s3.eee0358030dd from=translated src=- shape=7fa2a4d3 vocab=6960ed49
-/
theorem not_N_mem_empty : ¬ N.mem (∅ : Set ℕ) := by
  rw [N_mem]
  rintro (h | ⟨n, h⟩)
  · exact Set.empty_ne_univ h
  · exact (Set.singleton_ne_empty n) h.symm

/-- Distinct singletons are disjoint. -/
private theorem singleton_inter_eq_empty {n m : ℕ} (hmn : m ≠ n) :
    ({n} : Set ℕ) ∩ {m} = ∅ := by
  simp_all

/-- **Exercise 4.18 (Scott 1981, PRG-19).** Element classification: every element
of `|N|` is either
the bottom `⊥` or a total element `n̂`. So `N` is the flat domain over `ℕ`.
@isnad1 id=or.0h1v.s4.0b21bee057e2 from=translated src=- shape=8b86e3ec vocab=fc3dd80b
-/
theorem element_classification (x : N.Element) :
    x = N.bot ∨ ∃ n, x = natElem n := by
  by_cases h : ∃ n, x.mem {n}
  · obtain ⟨n, hn⟩ := h
    refine Or.inr ⟨n, ?_⟩
    apply Element.ext
    intro Y
    rw [mem_natElem_iff]
    constructor
    · intro hY
      rcases N_mem.mp (x.sub hY) with rfl | ⟨m, rfl⟩
      · exact Or.inl rfl
      · by_cases hmn : m = n
        · subst hmn; exact Or.inr rfl
        · exfalso
          have hmem := x.inter_mem hn hY
          rw [singleton_inter_eq_empty hmn] at hmem
          exact not_N_mem_empty (x.sub hmem)
    · rintro (rfl | rfl)
      · exact x.master_mem
      · exact hn
  · refine Or.inl ?_
    apply Element.ext
    intro Y
    rw [N_bot_mem]
    constructor
    · intro hY
      rcases N_mem.mp (x.sub hY) with rfl | ⟨m, rfl⟩
      · rfl
      · exact absurd hY (fun hm => h ⟨m, hm⟩)
    · rintro rfl
      exact x.master_mem

/-- **Exercise 4.18 (Scott 1981, PRG-19).** The numerals are distinct: `n̂ = m̂ ⟹
n = m`.
@isnad1 id=eq.1h2v.s4.a670680f837b from=translated src=- shape=648d2cea vocab=ed6dbc0d
-/
theorem natElem_injective {n m : ℕ} (h : natElem n = natElem m) : n = m := by
  have hmem : (natElem m).mem {n} := h ▸ (mem_natElem_iff.mpr (Or.inr rfl))
  rw [mem_natElem_iff] at hmem
  simp_all

/-- **Exercise 4.18 (Scott 1981, PRG-19).** `succ` is injective on the total
elements.
@isnad1 id=eq.1h2v.s4.f4a4809df066 from=translated src=- shape=cdbba4c2 vocab=c1f25620
-/
theorem succMap_injective {n m : ℕ}
    (h : succMap.toElementMap (natElem n) = succMap.toElementMap (natElem m)) : n = m := by
  rw [succMap_natElem, succMap_natElem] at h
  have := natElem_injective h
  omega

/-- **Exercise 4.18 (Scott 1981, PRG-19).** `0̂` is not a numeral successor.
@isnad1 id=ne.0h1v.s4.5d800c13977b from=translated src=- shape=b3a55546 vocab=2559e14c
-/
theorem natElem_zero_ne_succ (k : ℕ) : natElem 0 ≠ natElem (k + 1) := fun h =>
  Nat.succ_ne_zero k (natElem_injective h).symm

/-- **Exercise 4.18 (Scott 1981, PRG-19).** `0̂` is not in the image of `succ` —
Peano's
"zero is not a successor".
@isnad1 id=ne.0h1v.s4.039103892267 from=translated src=- shape=051a529c vocab=c1f25620
-/
theorem zero_ne_succMap (n : ℕ) : natElem 0 ≠ succMap.toElementMap (natElem n) := by
  rw [succMap_natElem]
  exact natElem_zero_ne_succ n

end Domain.Neighborhood.Exercise418

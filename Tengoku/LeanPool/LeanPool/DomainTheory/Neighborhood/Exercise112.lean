/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.Basic
public import Tengoku

/-!
# Exercise 1.12 (Scott 1981, PRG-19, §1) — the final-segment system on `ℕ`

Let `Δ = ℕ` and take as neighbourhoods the **final segments** (tails)

`tail n = {m ∈ ℕ ∣ n ≤ m}`,

so `tail 0 = ℕ = Δ` and `tail 0 ⊇ tail 1 ⊇ tail 2 ⊇ ⋯` is a descending chain
(Scott's `{m ∣ m > n}`
is `tail (n+1)`). This generalizes Example 1.3 (a *chain*) to the countably
infinite case.

Deliverables:

* `neighborhoodSystem : NeighborhoodSystem ℕ` (the tails are pairwise nested, so
Factoid 1.4a
  applies) — verifies it is a neighbourhood system.
* **Finite elements.** `fin n = ↑(tail n)`, the principal filters; they form an
ascending `ω`-chain
  `fin 0 ⊏ fin 1 ⊏ ⋯` (`fin_le_iff`, `fin_strictMono`).
* **The limit / total element.** `top = 𝒟` itself (all tails) is the greatest
element (`le_top`),
  is the *unique* total (maximal) element (`top_isTotal`, `isTotal_iff_top`).
* **Classification** (the "only one limit element" hint): every element is either
a finite `fin n`
  or the limit `top` (`element_eq`). This single result is *classical* (it decides
  whether the set
  of indices in `x` is bounded — `Nat.find` over a `¬`-predicate); everything else
  is constructive.
-/

@[expose] public section

namespace Domain.Neighborhood.Exercise112

open Domain.Neighborhood NeighborhoodSystem

/-- The final segment (tail) `tail n = {m ∣ n ≤ m}`; the neighbourhood "all
integers `≥ n`". -/
def tail (n : ℕ) : Set ℕ := {m | n ≤ m}

/--
@isnad1 id=iff.0h2v.s4.b7687ef71abd from=translated src=- shape=27d62ace vocab=f9a3cdf8
-/
@[simp] theorem mem_tail {n m : ℕ} : m ∈ tail n ↔ n ≤ m := Iff.rfl

/-- A longer tail is a *smaller* set: `tail n ⊆ tail m ↔ m ≤ n`.
@isnad1 id=iff.0h2v.s4.1a3df3f9b671 from=translated src=- shape=020421fc vocab=eea5626e
-/
theorem tail_subset_iff {n m : ℕ} : tail n ⊆ tail m ↔ m ≤ n := by
  constructor
  · intro h
    exact h (show n ∈ tail n from le_refl n)
  · intro hmn k hk
    exact le_trans hmn hk

/-- `tail n ∩ tail m = tail (max n m)` (the intersection of two tails is the
shorter one).
@isnad1 id=eq.0h2v.s4.1cf05adbd960 from=translated src=- shape=82141211 vocab=4e538357
-/
theorem tail_inter (n m : ℕ) : tail n ∩ tail m = tail (max n m) := by
  ext k
  simp_all

/-- Membership in the final-segment system: `X` is a neighbourhood iff `X = tail
n` for some `n`. -/
def mem (X : Set ℕ) : Prop := ∃ n, X = tail n

/--
@isnad1 id=nestedor.0h0v.s1.ad6077204078 from=translated src=- shape=25b03439 vocab=93c2bf39
-/
theorem nestedOrDisjoint : NestedOrDisjoint mem := by
  rintro X Y ⟨n, rfl⟩ ⟨m, rfl⟩
  rcases le_total n m with h | h
  · exact Or.inr (Or.inl (tail_subset_iff.mpr h))
  · exact Or.inl (tail_subset_iff.mpr h)

/-- **Exercise 1.12.** The final-segment neighbourhood system on `ℕ` (master `Δ =
tail 0 = ℕ`). -/
def neighborhoodSystem : NeighborhoodSystem ℕ :=
  ofNestedOrDisjoint mem (tail 0) ⟨0, rfl⟩ nestedOrDisjoint
    (fun {X} hX => by obtain ⟨n, rfl⟩ := hX; exact tail_subset_iff.mpr (Nat.zero_le n))

/--
@isnad1 id=iff.0h1v.s4.b17a3c66c9bb from=translated src=- shape=0b4dbce5 vocab=5ac700de
-/
@[simp] theorem ns_mem {X : Set ℕ} : neighborhoodSystem.mem X ↔ ∃ n, X = tail n := Iff.rfl

/--
@isnad1 id=mem.0h1v.s2.5b96bfcab940 from=translated src=- shape=9bb0b988 vocab=d78b600d
-/
theorem mem_tail_nbhd (n : ℕ) : neighborhoodSystem.mem (tail n) := ⟨n, rfl⟩

/-! ### Finite elements: the principal filters `fin n = ↑(tail n)`. -/

/-- The finite element `fin n = ↑(tail n)` (principal filter of the tail). -/
def fin (n : ℕ) : neighborhoodSystem.Element := neighborhoodSystem.principal (mem_tail_nbhd n)

/-- The finite elements form an ascending chain: `fin n ⊑ fin m ↔ n ≤ m`.
@isnad1 id=iff.0h2v.s4.8dd1297987d3 from=translated src=- shape=9a35d825 vocab=a8ce6c5f
-/
theorem fin_le_iff (n m : ℕ) : fin n ≤ fin m ↔ n ≤ m := by
  rw [fin, fin, neighborhoodSystem.principal_le_iff, tail_subset_iff]

/-- The chain `fin 0 ⊏ fin 1 ⊏ ⋯` is strictly increasing.
@isnad1 id=strictmo.0h0v.s3.b35920813a6d from=translated src=- shape=28fc0566 vocab=f58bd897
-/
theorem fin_strictMono : StrictMono fin := by
  intro n m hnm
  refine lt_of_le_of_ne ((fin_le_iff n m).mpr hnm.le) ?_
  intro heq
  have : m ≤ n := (fin_le_iff m n).mp (le_of_eq heq.symm)
  exact absurd (le_antisymm hnm.le this) (Nat.ne_of_lt hnm)

/-! ### The limit element: the whole system `𝒟`, the greatest / unique total
element. -/

/-- The **limit element** `top`: the filter of *all* tails (Scott's single limit
node). -/
def top : neighborhoodSystem.Element where
  mem X := neighborhoodSystem.mem X
  sub h := h
  master_mem := neighborhoodSystem.master_mem
  inter_mem := by
    rintro X Y ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨max n m, tail_inter n m⟩
  up_mem _ hY _ := hY

/--
@isnad1 id=iff.0h1v.s3.812530681809 from=translated src=- shape=466d895d vocab=5ab009ab
-/
@[simp] theorem mem_top {X : Set ℕ} : top.mem X ↔ neighborhoodSystem.mem X := Iff.rfl

/-- `top` is the greatest element of `|𝒟|`: every element approximates it.
@isnad1 id=le.0h1v.s4.70aaa778aa94 from=translated src=- shape=7656ba26 vocab=13d94e6f
-/
theorem le_top (x : neighborhoodSystem.Element) : x ≤ top :=
  fun _ hX => x.sub hX

/-- `top` is a total (maximal) element.
@isnad1 id=istotal.0h0v.s2.456c5af0453b from=translated src=- shape=54c8eceb vocab=dde5a5a4
-/
theorem top_isTotal : neighborhoodSystem.IsTotal top :=
  fun y _ => le_top y

/-- `top` is the **unique** total element: an element is total iff it equals
`top`.
@isnad1 id=iff.0h1v.s3.3ebf1843b23f from=translated src=- shape=7cf5c502 vocab=d86af970
-/
theorem isTotal_iff_top (x : neighborhoodSystem.Element) :
    neighborhoodSystem.IsTotal x ↔ x = top := by
  constructor
  · intro h
    exact le_antisymm (le_top x) (h top (le_top x))
  · rintro rfl; exact top_isTotal

/-! ### Classification: finite `fin n`, or the limit `top` (classical). -/

/-- **Exercise 1.12 (classification).** Every element is either a finite element
`fin n` or the
single limit element `top`. *Classical*: it decides whether the indices present in
`x` are bounded.
(Hint realized: "there is only one limit element.")
@isnad1 id=or.0h1v.s4.79a2786c754a from=translated src=- shape=1c0cc578 vocab=f97d9a73
-/
theorem element_eq (x : neighborhoodSystem.Element) :
    (∃ n, x = fin n) ∨ x = top := by
  classical
  by_cases h : ∀ n, x.mem (tail n)
  · refine Or.inr ?_
    apply Element.ext
    intro X
    constructor
    · intro hx; exact x.sub hx
    · rintro ⟨n, rfl⟩; exact h n
  · refine Or.inl ?_
    have h' : ∃ n, ¬ x.mem (tail n) := not_forall.mp h
    have hpos : ∀ n, ¬ x.mem (tail n) → 0 < n := by
      intro n hn
      rcases Nat.eq_zero_or_pos n with rfl | hp
      · exact absurd x.master_mem hn
      · exact hp
    have hspec : ¬ x.mem (tail (Nat.find h')) := Nat.find_spec h'
    have hmin : ∀ j, j < Nat.find h' → x.mem (tail j) := by
      simp_all
    have hn₀ : 0 < Nat.find h' := hpos _ hspec
    refine ⟨Nat.find h' - 1, ?_⟩
    apply Element.ext
    intro X
    have key : ∀ j, x.mem (tail j) ↔ j ≤ Nat.find h' - 1 := by
      intro j
      constructor
      · intro hj
        by_contra hc
        have hle : Nat.find h' ≤ j := by omega
        exact hspec (x.up_mem hj (mem_tail_nbhd (Nat.find h')) (tail_subset_iff.mpr hle))
      · intro hj
        exact hmin j (by omega)
    constructor
    · intro hx
      obtain ⟨j, rfl⟩ := x.sub hx
      exact ⟨mem_tail_nbhd j, tail_subset_iff.mpr ((key j).mp hx)⟩
    · rintro ⟨hX, hsub⟩
      obtain ⟨j, rfl⟩ := hX
      exact (key j).mpr (tail_subset_iff.mp hsub)

end Domain.Neighborhood.Exercise112

/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.Basic

/-!
# Theorem 1.11 (Scott 1981, PRG-19, §1) — closure of `|𝒟|` under sequential `⋂`
and ascending `⋃`

If `𝒟` is a neighbourhood system and `xₙ ∈ |𝒟|` for `n = 0, 1, 2, …`, then

* (i)  `⋂ₙ xₙ ∈ |𝒟|`;
* (ii) `⋃ₙ xₙ ∈ |𝒟|`, **provided** `x₀ ⊆ x₁ ⊆ x₂ ⊆ ⋯` (an ascending chain).

We realize each as a concrete `Element`:

* `iInter x` has membership `X ∈ ⋂ₙ xₙ iff ∀ n, X ∈ xₙ`. All four filter laws are
pointwise. It is
  the **greatest lower bound** (`iInter_le`, `le_iInter`): Scott's "best element
  that approximates
  all of the `xₙ`; exactly what is common to all".
* `iUnion x hmono` (with `hmono : Monotone x`) has `X ∈ ⋃ₙ xₙ iff ∃ n, X ∈ xₙ`. Only
filter law (ii)
  (closure under `∩`) needs the proviso: from `X ∈ xₙ`, `Y ∈ xₘ` take `k = max n
  m`, where
  monotonicity puts both `X, Y ∈ x_k`, so `X ∩ Y ∈ x_k`. It is the **least upper
  bound**
  (`le_iUnion`, `iUnion_le`): "just what the increasing sequence approximates".

Everything is constructive (`[propext, Quot.sound]`).
-/

@[expose] public section

namespace Domain.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-! ### (i) Countable intersection. -/

/-- **Theorem 1.11 (i).** The intersection `⋂ₙ xₙ = {X ∣ ∀ n, X ∈ xₙ}` of a
sequence of elements is
again an element of `|𝒟|`. (No proviso: all of 1.6(i)–(iii) are pointwise.) -/
def iInter (x : ℕ → V.Element) : V.Element where
  mem X := ∀ n, (x n).mem X
  sub h := (x 0).sub (h 0)
  master_mem n := (x n).master_mem
  inter_mem h1 h2 n := (x n).inter_mem (h1 n) (h2 n)
  up_mem h hY hXY n := (x n).up_mem (h n) hY hXY

/--
@isnad1 id=iff.0h4v.s5.ac7f55c1557d from=translated src=- shape=177103d1 vocab=86128043
-/
@[simp] theorem mem_iInter (x : ℕ → V.Element) {X : Set α} :
    (V.iInter x).mem X ↔ ∀ n, (x n).mem X := Iff.rfl

/-- `⋂ₙ xₙ ⊑ xₙ`: the intersection approximates every member of the sequence.
@isnad1 id=le.0h4v.s5.db916815dd20 from=translated src=- shape=948037d8 vocab=d6cfbade
-/
theorem iInter_le (x : ℕ → V.Element) (n : ℕ) : V.iInter x ≤ x n :=
  fun _ h => h n

/-- `⋂ₙ xₙ` is the **greatest** lower bound: anything approximating all `xₙ`
approximates `⋂ₙ
xₙ`.
@isnad1 id=le.1h4v.s5.297e5836802b from=translated src=- shape=5c8cb551 vocab=d6cfbade
-/
theorem le_iInter (x : ℕ → V.Element) (y : V.Element) (h : ∀ n, y ≤ x n) :
    y ≤ V.iInter x :=
  fun X hX n => h n X hX

/-! ### (ii) Ascending countable union. -/

/-- **Theorem 1.11 (ii).** For an **ascending** sequence `x₀ ⊑ x₁ ⊑ ⋯`, the union
`⋃ₙ xₙ = {X ∣ ∃ n, X ∈ xₙ}` is again an element of `|𝒟|`. The proviso (`Monotone
x`) is used only in
the intersection law: `X ∈ xₙ`, `Y ∈ xₘ` ⟹ both in `x_{max n m}`. -/
def iUnion (x : ℕ → V.Element) (hmono : Monotone x) : V.Element where
  mem X := ∃ n, (x n).mem X
  sub := by rintro X ⟨n, hn⟩; exact (x n).sub hn
  master_mem := ⟨0, (x 0).master_mem⟩
  inter_mem := by
    rintro X Y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨max n m, (x (max n m)).inter_mem ?_ ?_⟩
    · exact hmono (le_max_left n m) X hn
    · exact hmono (le_max_right n m) Y hm
  up_mem := by
    rintro X Y ⟨n, hn⟩ hY hXY
    exact ⟨n, (x n).up_mem hn hY hXY⟩

/--
@isnad1 id=iff.1h4v.s5.5bd36775e69e from=translated src=- shape=1a023ef8 vocab=57faecb3
-/
@[simp] theorem mem_iUnion (x : ℕ → V.Element) (hmono : Monotone x) {X : Set α} :
    (V.iUnion x hmono).mem X ↔ ∃ n, (x n).mem X := Iff.rfl

/-- `xₙ ⊑ ⋃ₙ xₙ`: every member of the sequence approximates the union.
@isnad1 id=le.1h4v.s5.177addffd14d from=translated src=- shape=e288cf68 vocab=7e19b727
-/
theorem le_iUnion (x : ℕ → V.Element) (hmono : Monotone x) (n : ℕ) :
    x n ≤ V.iUnion x hmono :=
  fun _ hX => ⟨n, hX⟩

/-- `⋃ₙ xₙ` is the **least** upper bound: anything approximated by all `xₙ`
approximates the
union from above.
@isnad1 id=le.2h4v.s6.df8086031b0e from=translated src=- shape=460b2817 vocab=7e19b727
-/
theorem iUnion_le (x : ℕ → V.Element) (hmono : Monotone x) (y : V.Element)
    (h : ∀ n, x n ≤ y) : V.iUnion x hmono ≤ y := by
  rintro X ⟨n, hn⟩
  exact h n X hn

end NeighborhoodSystem

end Domain.Neighborhood

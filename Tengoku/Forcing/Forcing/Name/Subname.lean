/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Tengoku.Seed.Data.Set.Defs
import Tengoku.Forcing.Forcing.Name.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The subname relation, well-founded

The structural descent of names: `Subname σ τ` when `σ` is an immediate subname of `τ`. Its
well-foundedness is the recursion principle the atomic forcing kernel runs on — **not** a
numerical or ordinal rank: the actual problem downstream is well-founded recursion on a pair
of names where either coordinate may descend, and the structural relation feeds
`Sym2.GameAdd` directly. A `PName.rank` would be introduced only if the structural approach
genuinely failed; it has not. `SubnameClosed` is the family-level form — the preorder-free
structural notion that keeps mutual name inductions inside a family. The module is
order-free throughout.

## Main definitions

* `Forcing.PName.Subname`: the immediate-subname relation.

## Main results

* `Forcing.PName.subname_wellFounded`: the relation is well-founded.
-/

universe u

namespace Forcing.PName

variable {P : Type u}

/-- `σ` is an immediate subname of `τ`.-/
def Subname (σ τ : PName P) : Prop :=
  ∃ i : τ.Idx, τ.elems i = σ

/--
@isnad1 id=subname.0h3v.s4.e80bc76a4192 from=translated src=- shape=e8dbe213 vocab=b3e986f7
-/
theorem subname_elems (τ : PName P) (i : τ.Idx) : Subname (τ.elems i) τ :=
  ⟨i, rfl⟩

/-- A family of names closed under immediate subnames — the preorder-free structural notion
that keeps mutual name inductions inside a family.-/
def SubnameClosed (𝒩 : Set (PName P)) : Prop :=
  ∀ τ ∈ 𝒩, ∀ i : τ.Idx, τ.elems i ∈ 𝒩

/-- The subname relation is well-founded: names are well-founded trees.
@isnad1 id=wellfoun.0h1v.s2.90b18af379a3 from=translated src=- shape=27e09c58 vocab=fc434fdb
-/
theorem subname_wellFounded : WellFounded (Subname (P := P)) := by
  refine ⟨fun τ ↦ ?_⟩
  induction τ with
  | mk ι e c ih =>
    exact Acc.intro _ fun σ ⟨i, hi⟩ ↦ hi ▸ ih i

end Forcing.PName

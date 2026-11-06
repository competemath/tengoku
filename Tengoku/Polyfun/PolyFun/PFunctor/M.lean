/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Tengoku.Seed.Data.PFunctor.Univariate.M

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Auxiliary lemmas for `PFunctor.M`

Small extensions to `Mathlib.Data.PFunctor.Univariate.M` used by the
`PolyFun.ITree` port of the Coq `InteractionTrees` library.

The Mathlib file already supplies `M.mk`, `M.dest`, `M.corec`, `M.dest_mk`,
`M.mk_dest`, `M.dest_corec`, `M.corec_unique`, and the bisimulation principle
`M.bisim`. We add a few rewriting helpers that come up repeatedly when
defining and reasoning about ITrees:

* `M.dest_inj` / `M.eq_of_dest_eq` — `M.dest` is injective on `M P` (since
  it has a left inverse `M.mk`).
* `M.dest_corec_apply` — destructured form of `M.dest_corec` whose RHS unpacks
  the `Sigma` so that nested pattern matches reduce by `rfl`.
* `M.dest_corec_eq` — reformulation of `M.dest_corec` that lets `simp` see the
  result as an explicit `Sigma`.
* `M.corec_eq_corec` — bisimulation principle for two `corec`s, the workhorse
  for `bind`/`iter` rewriting.
* `M.corec_dest` — `M.corec dest = id`. The corecursive identity.
-/

@[expose] public section

universe u uA uB v w

namespace PFunctor

namespace M

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-! ### Injectivity of `dest` -/

/-! ### Corec helpers -/

/-- `M.dest_corec` with the result `Sigma` unpacked. The shape of `M.dest`'s
output is `(g x).1`; the children component, after applying the `PFunctor.map`
on the RHS of `M.dest_corec`, is `M.corec g ∘ (g x).2`.-/
theorem dest_corec_apply (g : α → P α) (x : α) :
    M.dest (M.corec g x) = ⟨(g x).1, fun b => M.corec g ((g x).2 b)⟩ := by
  rw [M.dest_corec]
  rcases h : g x with ⟨a, f⟩
  rfl

end M

end PFunctor

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Tengoku.T3ModelCompanion.T3.GroupTheory.Free.Burnside
public import Tengoku.T3ModelCompanion.T3.ModelTheory.ExponentThree
public import Tengoku.T3ModelCompanion.T3.ModelTheory.LocallyFinite.Universes

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Burnside formulation of local finiteness

The usual group theory with the exponent law is locally finite exactly when its free
Burnside groups of all positive finite ranks are finite. This is the established equivalence
used to interpret Conjecture 1.1 in the v9 introduction. Its detailed source remains the
archived v7 Section 6, which is removed from v9. Neither implication between local finiteness
and the existence of a model companion is asserted here for a general exponent.

Paper-ID: questions.burnside_local_finiteness
TeX: archives/T3_modelcompanion_v7.tex, Section 6, lines 1520–1525.
-/

@[expose] public section

open scoped FirstOrder

namespace T3

open FirstOrder FirstOrder.Language

/-- Finiteness of finite-rank Burnside groups makes every finitely generated subgroup of any
group of that exponent finite.

Paper-ID: questions.burnside_local_finiteness
TeX: archives/T3_modelcompanion_v7.tex, Section 6, lines 1522–1525.-/
theorem finite_closure_of_finite_burnside {n : ℕ}
    (hfree : ∀ r : ℕ, 0 < r → Finite (Burnside n (Fin r)))
    {G : Type*} [Group G] (hG : ∀ x : G, x ^ n = 1)
    {s : Set G} (hs : s.Finite) : Finite (Subgroup.closure s) := by
  let : Group.FG (Subgroup.closure s) :=
    (Group.fg_iff_subgroup_fg _).mpr ((Subgroup.fg_iff _).mpr ⟨s, rfl, hs⟩)
  exact Burnside.finite_of_fg hfree fun x => Subtype.ext (hG x)

end T3

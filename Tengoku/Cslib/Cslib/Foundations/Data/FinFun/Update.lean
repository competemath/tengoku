/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Tengoku.Cslib.Cslib.Foundations.Data.FinFun.Basic
public import Tengoku.Cslib.Cslib.Foundations.Data.DecidableEqZero
public import Tengoku.Seed.Data.Finset.SDiff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/leanprover/cslib@e806c8e639ed, `Cslib/Foundations/Data/FinFun/Update.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! # Update for finite functions

This module defines the update operation for finite functions, that is, the equivalent of
`Function.update` for `FinFun`.
-/

@[expose] public section

namespace Cslib.FinFun

variable [Zero β] [DecidableEq α] [DecidableEqZero β]

/-- `FinFun` equivalent of `Function.update`.-/
def update (f : α →₀ β) (a : α) (b : β) : α →₀ β where
  fn := Function.update f.fn a b
  support := if b = 0 then f.support \ {a} else f.support ∪ {a}
  mem_support_fn := by
    by_cases b = 0
    · grind only [= Finset.mem_sdiff, = Finset.mem_singleton, = Function.update, = mem_support_fn]
    · grind

/-- `FinFun.update` is consistent with `Function.update`.
@isnad1 id=eq.0h5v.s6.878b0392ebfd from=translated src=- shape=72b67d2d vocab=8337658d
-/
@[scoped grind =, simp]
theorem update_coe (f : α →₀ β) : (f.update a b : α → β) = Function.update f a b := by
  grind [update]

/-- Conditional characterisation of the functional interface of `FinFun.update`.
@isnad1 id=eq.0h6v.s6.b1b41dfce7dd from=translated src=- shape=b9771325 vocab=e4050aae
-/
@[scoped grind =]
theorem update_apply (f : α →₀ β) : ((f.update a' b) a) = if a = a' then b else f a := by
  simp [Function.update_apply]

/-- Conditional characterisation of the support of an updated `FinFun`.
@isnad1 id=eq.0h5v.s6.8dd39c473df3 from=translated src=- shape=312beb32 vocab=7297ec4f
-/
@[scoped grind =]
theorem update_support (f : α →₀ β) :
    (f.update a b).support = if b = 0 then f.support \ {a} else f.support ∪ {a} := by simp [update]

/-- Updating a finite function on the same key is the same as doing the last update.
@isnad1 id=eq.0h6v.s5.938796902872 from=translated src=- shape=3576c812 vocab=99097a75
-/
@[scoped grind =, simp]
theorem update_idem (f : α →₀ β) : (f.update a b).update a b' = f.update a b' := by grind

/-- Updates on different keys commute.
@isnad1 id=eq.1h7v.s6.7e4e6244a09d from=translated src=- shape=a19adeb3 vocab=99097a75
-/
@[scoped grind =]
theorem update_comm (f : α →₀ β) (h : a ≠ a') :
    (f.update a b).update a' b' = (f.update a' b').update a b := by
  grind only [←= ext, = update_apply]

/-- Updates that do not change mappings are redundant.
@isnad1 id=eq.0h4v.s5.d07006eee5a5 from=translated src=- shape=4345f08c vocab=62f6999f
-/
@[scoped grind =]
theorem update_self (f : α →₀ β) : (f.update a (f a)) = f := by grind

/-- Updating a function never grows its support more than adding the key.
@isnad1 id=le.0h5v.s6.fbb1123d1826 from=translated src=- shape=73eba097 vocab=f6078d9f
-/
@[scoped grind .]
theorem update_support_subseteq (f : α →₀ β) : (f.update a b).support ⊆ f.support ∪ {a} := by grind

end Cslib.FinFun

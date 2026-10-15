/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
module

public import Tengoku

/-!
# LeanPool.RlTheoryInLean.Order.Filter.Basic
-/

@[expose] public section

open Finset Filter
open scoped BigOperators

namespace Filter

/--
@isnad1 id=eventual.1h7v.s6.2fb99a12f093 from=translated src=- shape=46d0b439 vocab=f4c6ea94
-/
lemma EventuallyEq.finset_sum {α ι β : Type*} [AddCommGroup β] {l : Filter α}
  {s : Finset ι} {f g : ι → α → β} (hfg : ∀ i ∈ s, f i =ᶠ[l] g i) :
  ∑ i ∈ s, f i =ᶠ[l] ∑ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hfg a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hfg i (Finset.mem_insert_of_mem hi)))

end Filter

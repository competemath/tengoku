/-
Copyright (c) 2024 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module

public import Tengoku

/-!
# Auxiliary `Finset` lemmas

Small helper lemmas about `Finset` that are not specific to Boolean functions.
-/

@[expose] public section

namespace Finset

variable {α : Type*}

section ToDataFintypeBasic

variable [Fintype α] [DecidableEq α]

/--
@isnad1 id=eq.0h2v.s6.e980886f4c30 from=translated src=- shape=0bd01353 vocab=46f35ce0
-/
@[simp]
lemma filter_univ_not_mem (s : Finset α) : univ.filter (· ∉ s) = sᶜ := by
  ext; simp only [mem_filter, mem_univ, true_and, mem_compl]

end ToDataFintypeBasic

end Finset

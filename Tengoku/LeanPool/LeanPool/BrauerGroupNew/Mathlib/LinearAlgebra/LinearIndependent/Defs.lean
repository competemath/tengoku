/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
module

public import Tengoku

/-!
# LeanPool.BrauerGroupNew.Mathlib.LinearAlgebra.LinearIndependent.Defs

Imported Lean Pool material for
`LeanPool.BrauerGroupNew.Mathlib.LinearAlgebra.LinearIndependent.Defs`.
-/

@[expose] public section

variable {ι R M : Type*} {v : ι → M} [Semiring R] [AddCommMonoid M] [Module R M]

-- TODO: Replace `linearIndependent_iff_finset_linearIndependent`
/--
@isnad1 id=iff.0h4v.s5.5485345dd7e6 from=translated src=- shape=30ff4554 vocab=662fc1d5
-/
lemma linearIndependent_iff_linearIndepOn_finset :
    LinearIndependent R v ↔ ∀ s : Finset ι, LinearIndepOn R v s :=
  linearIndependent_iff_finset_linearIndependent

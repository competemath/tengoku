/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Tengoku

/-!
# LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Chain.Const

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Chain.Const`.
-/

@[expose] public section

namespace OmegaCompletePartialOrder.Chain

variable {A : Type*} [Preorder A]

/-- The chain that always returns the same value. -/
def const (x : A) : Chain A where
  toOrderHom := OrderHom.const ℕ x

/--
@isnad1 id=eq.0h3v.s4.15053f625e67 from=translated src=- shape=c3fcef69 vocab=039c48b6
-/
@[simp]
lemma const_apply (x : A) (n : ℕ) : const x n = x := by
  rfl

end OmegaCompletePartialOrder.Chain

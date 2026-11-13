/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open DirectSum

namespace RepresentationTheory.Algebra.Module.Simple

variable {R : Type*} [Ring R]

/-- A simple module is finitely generated.-/
theorem IsSimpleModule.finite {M : Type*} [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] : Module.Finite R M := by
  haveI := IsSimpleModule.nontrivial R M
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have hmem : x ∈ Submodule.span R {x} := Submodule.mem_span_singleton_self x
  have hspan : Submodule.span R {x} = ⊤ := by
    rcases eq_bot_or_eq_top (Submodule.span R {x}) with h | h
    · rw [h, Submodule.mem_bot] at hmem; exact absurd hmem hx
    · exact h
  rw [Module.finite_def, ← hspan]
  exact Submodule.fg_span (Set.finite_singleton x)

end RepresentationTheory.Algebra.Module.Simple

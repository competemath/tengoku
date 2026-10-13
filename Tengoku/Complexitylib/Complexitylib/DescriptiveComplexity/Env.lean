/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

/-!
  Variable environments for first-order logic.

  Since `Fin.cons` is absent from Lean 4 core, we define our own
  environment machinery for mapping de Bruijn variables to universe elements.
-/

@[expose] public section

namespace Complexity

namespace DescriptiveComplexity

/-- An environment maps `n` de Bruijn variables to elements of `Fin card`. -/
abbrev Env (card n : Nat) := Fin n → Fin card

/-- Extend an environment with a new element at index 0. -/
def envCons (a : Fin card) (σ : Env card n) : Env card (n + 1) :=
  fun i => if h : i.val = 0 then a else σ ⟨i.val - 1, by omega⟩

/-- The empty environment (no free variables). -/
def emptyEnv (card : Nat) : Env card 0 := Fin.elim0

/--
@isnad1 id=eq.0h4v.s5.179dbf883acf from=translated src=- shape=933b5b1f vocab=4e1ef55c
-/
theorem envCons_zero (a : Fin card) (σ : Env card n) :
    envCons a σ ⟨0, by omega⟩ = a := by
  simp [envCons]

/--
@isnad1 id=eq.0h5v.s5.98f1465e6eef from=translated src=- shape=fe8c1ceb vocab=8fcea366
-/
theorem envCons_succ (a : Fin card) (σ : Env card n) (i : Fin n) :
    envCons a σ ⟨i.val + 1, by omega⟩ = σ i := by
  simp [envCons]

/--
@isnad1 id=eq.0h6v.s6.a4beaca8e68d from=translated src=- shape=173c675a vocab=2be5e4e2
-/
theorem envCons_comp (f : Fin m → Fin k) (a : Fin m) (σ : Env m n) :
    f ∘ envCons a σ = envCons (f a) (f ∘ σ) := by
  funext i
  simp [Function.comp, envCons]
  split
  · rfl
  · rfl

/--
@isnad1 id=eq.0h3v.s5.2cb826266403 from=translated src=- shape=9c62f863 vocab=e6bdf30b
-/
theorem emptyEnv_comp (f : Fin m → Fin k) :
    f ∘ emptyEnv m = emptyEnv k := by
  funext i
  exact Fin.elim0 i

end DescriptiveComplexity

end Complexity

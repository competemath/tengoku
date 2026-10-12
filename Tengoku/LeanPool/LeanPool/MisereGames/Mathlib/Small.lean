/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Tengoku

/-!
Misere combinatorial games.
-/

namespace MisereGames

open Set

universe u

variable {α : Type*} (r : α → α → Prop) [H : ∀ x, Small.{u} {y // r x y}]

private def level (x : α) : ℕ → Set α
  | 0 => {x}
  | n + 1 => ⋃₀ ((fun x ↦ {y | r x y}) '' level x n)

public section

end

end MisereGames

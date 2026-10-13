/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Sum
public import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Hom
public import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Pi
import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Basic

/-!
# LeanPool.QuasiBorelSpaces.SeparatesPoints

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.SeparatesPoints`.
-/

@[expose] public section

variable
  {A : Type*} [QuasiBorelSpace A]
  {B : Type*} [QuasiBorelSpace B]
  {I : Type*} [Countable I]
  {P : I → Type*} [∀ i, QuasiBorelSpace (P i)]

namespace QuasiBorelSpace

/--
A `QuasiBorelSpace` _separates points_ if any two elements are equal iff all
morphism predicates agree on the elements.

This class is the `QuasiBorelSpace` analogue of `MeasurableSingletonClass`.
-/
class SeparatesPoints (A : Type*) [QuasiBorelSpace A] where
  /-- Two elements are equal iff they agree for all morphism predicates. -/
  separates (x y : A) : (∀ (p : A → Prop), IsHom p → p x → p y) → x = y

lemma separatesPoints_def
    [SeparatesPoints A] {x y : A}
    (h : ∀ (p : A → Prop), IsHom p → p x → p y)
    : x = y :=
  ‹SeparatesPoints A›.separates x y h

end QuasiBorelSpace

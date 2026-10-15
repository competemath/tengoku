/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Sum
import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Basic
import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Prop

/-!
# LeanPool.QuasiBorelSpaces.IsHomDiagonal

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.IsHomDiagonal`.
-/

@[expose] public section

namespace QuasiBorelSpace

variable
  {A : Type*} [QuasiBorelSpace A]
  {B : Type*} [QuasiBorelSpace B]

/-- The class of `QuasiBorelSpace`s where equality is a morphism. -/
class IsHomDiagonal (A : Type*) [QuasiBorelSpace A] where
  /-- Equality is a morphism. -/
  isHom_eq : IsHom (fun x : A × A ↦ x.1 = x.2)

export IsHomDiagonal (isHom_eq)
attribute [simp, fun_prop] isHom_eq

/--
@isnad1 id=ishom.2h4v.s5.08540874eea9 from=translated src=- shape=8a465181 vocab=0e3f80ca
-/
lemma isHom_eq'
    [IsHomDiagonal B] {f g : A → B} (hf : IsHom f) (hg : IsHom g)
    : IsHom fun x ↦ f x = g x := by
  fun_prop

instance
    [Countable A] [MeasurableSpace A]
    [DiscreteQuasiBorelSpace A]
    : IsHomDiagonal A where
  isHom_eq := by simp only [isHom_of_discrete_countable]

end QuasiBorelSpace

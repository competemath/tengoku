-- Tengoku.EquationalTheories.Generated.FiniteImplicationSearch.theorems.InversesManual: verified translations of equational_theories/Generated/FiniteImplicationSearch/theorems/InversesManual.lean (1 theorem)
import Tengoku.EquationalTheories.Deps.Superposition
import Tengoku.Data.Set.Finite.Basic
import Tengoku.Tactic.TypeStar
import Tengoku.Tactic.ByContra
import Tengoku.EquationalTheories.Deps

set_option linter.all false

namespace EquationalTheories

import Mathlib


class Magma (α : Type _) where
  /-- `a ◇ b` denotes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infix:65 " ◇ " => Magma.op

scoped instance MagmaToMul.inst {α : Type _} [Magma α] : Mul α where
  mul := Magma.op

scoped instance MagmaToAdd.inst {α : Type _} [Magma α] : Add α where
  add := Magma.op

scoped instance MulToMagma.inst {α : Type _} [Mul α] : Magma α where
  op := (· * ·)

scoped instance AddToMagma.inst {α : Type _} [Add α] : Magma α where
  op := (· + ·)

universe uEq

abbrev Equation1443 (G : Type uEq) [Magma G] : Prop := ∀ x y z : G, x = (x ◇ y) ◇ (x ◇ (x ◇ z))
abbrev Equation1630 (G : Type uEq) [Magma G] : Prop := ∀ x y : G, x = (x ◇ x) ◇ ((x ◇ x) ◇ y)

set_option linter.unusedVariables false

theorem _root_.Finite.Equation1443_implies_Equation1630 (G : Type*) [Magma G] [Finite G] (h : Equation1443 G) : Equation1630 G
:= by
  have eq1443_implies_eq21374 : ∀ X Y : G, X = ((X ◇ (X ◇ Y)) ◇ (X ◇ (X ◇ Y))) :=
    fun X Y => h X (X ◇ Y) Y
  have eq21374_implies_eq1630 (X Y : G) : ((X ◇ X) ◇ ((X ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ s)) (fun s => (s ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  intro x y
  simp only [eq1443_implies_eq21374, eq21374_implies_eq1630]

end EquationalTheories

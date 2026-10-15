/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/
module

public import Tengoku.LeanPool.LeanPool.Polylean.Complexes.Structures.Category

/-!
# LeanPool.Polylean.Complexes.Structures.Groupoid

Imported Lean Pool material for `LeanPool.Polylean.Complexes.Structures.Groupoid`.
-/

@[expose] public section

namespace LeanPool.Polylean

/-- A `Groupoid` is defined as a `Category` in which every morphism has an inverse satisfying certain conditions. -/
class Groupoid (S : Sort _) extends Category S where
  /-- The inverse of a morphism. -/
  inv : {X Y : S} → (X ⟶ Y) → (Y ⟶ X)
  inv_comp_id : {X Y : S} → (g : X ⟶ Y) → (inv g) ≫ g = 𝟙 Y
  comp_inv_id : {X Y : S} → (g : X ⟶ Y) → g ≫ (inv g) = 𝟙 X

namespace Groupoid

open Category

attribute [simp] inv_comp_id
attribute [simp] comp_inv_id

variable {S : Sort _} [G : Groupoid S] {X Y Z : S} (g g' : X ⟶ Y) (h h' : Y ⟶ Z)

/-- Groupoid inverse notation. -/
postfix:max " ⁻¹ " => Groupoid.inv -- type as `\inv`

/--
@isnad1 id=eq.0h6v.s6.84121c56fb19 from=translated src=- shape=b939518d vocab=aad9930e
-/
@[simp] theorem left_inv_cancel : g⁻¹ ≫ (g ≫ h) = h := by
  rw [← comp_assoc]; simp

/--
@isnad1 id=eq.0h2v.s5.58cc001434e5 from=translated src=- shape=b2122be4 vocab=c0f46adb
-/
@[simp] theorem id_inv : (𝟙 X)⁻¹ = 𝟙 X := by
  have := left_inv_cancel (𝟙 X) (𝟙 X)
  rw [comp_id, comp_id] at this; assumption

/--
@isnad1 id=eq.0h4v.s5.8ae195c102a4 from=translated src=- shape=41720921 vocab=d7d00a27
-/
@[simp] theorem inv_inv : (g⁻¹)⁻¹ = g := by
  have := left_inv_cancel (g⁻¹) g
  rw [inv_comp_id, comp_id] at this; assumption

/--
@isnad1 id=eq.0h6v.s6.9fb35472e116 from=translated src=- shape=7f6b7561 vocab=aad9930e
-/
@[simp] theorem left_cancel_inv (h : X ⟶ Z) : g ≫ (g⁻¹ ≫ h) = h := by
  have := left_inv_cancel g⁻¹ h
  rw [inv_inv] at this; assumption

/--
@isnad1 id=eq.0h6v.s6.e54ed1474017 from=translated src=- shape=8123c228 vocab=aad9930e
-/
@[simp] theorem inv_comp : (g ≫ h)⁻¹ = h⁻¹ ≫ g⁻¹ := by
  have := left_cancel_inv (g ≫ h)⁻¹ (h⁻¹ ≫ g⁻¹)
  simp at this; assumption

/--
@isnad1 id=iff.0h7v.s6.6d7a0d27ba83 from=translated src=- shape=5aa5ba5a vocab=9490fedb
-/
@[simp] theorem left_cancel : g ≫ h = g ≫ h' ↔ h = h' :=
  ⟨fun hyp => by have := congrArg (g⁻¹ ≫ ·) hyp; simp at this; exact this,
    congrArg _⟩

/--
@isnad1 id=iff.0h7v.s6.4828f6c895ba from=translated src=- shape=37403043 vocab=9490fedb
-/
@[simp] theorem right_cancel : g ≫ h = g' ≫ h ↔ g = g' :=
  ⟨fun hyp => by have := congrArg (· ≫ h⁻¹) hyp; simp at this; exact this,
    congrArg (· ≫ h)⟩

/--
@isnad1 id=iff.0h5v.s6.12d207b4004f from=translated src=- shape=652525fc vocab=87be6792
-/
@[simp] theorem left_cancel_id : (g = g ≫ e) ↔ 𝟙 Y = e := by
  have := left_cancel g (𝟙 _) e; simp at this; exact this

/--
@isnad1 id=iff.0h5v.s6.68dc8901f7c2 from=translated src=- shape=4dd6f8c1 vocab=87be6792
-/
@[simp] theorem left_cancel_id' : (g ≫ e = g) ↔ e = 𝟙 Y := by
  have := left_cancel g e (𝟙 Y); simp at this; exact this

/--
@isnad1 id=iff.0h5v.s6.f30d4d668b5e from=translated src=- shape=d939a11c vocab=87be6792
-/
@[simp] theorem right_cancel_id : (g = e ≫ g) ↔ 𝟙 X = e := by
  have := right_cancel (𝟙 X) e g; simp at this; exact this

/--
@isnad1 id=iff.0h5v.s6.0751ac57f0b0 from=translated src=- shape=4d8ec548 vocab=87be6792
-/
@[simp] theorem right_cancel_id' : (e ≫ g = g) ↔ e = 𝟙 X := by
  have := right_cancel e (𝟙 X) g; simp at this; exact this

end Groupoid

namespace Groupoid

/-- A `Functor` is a morphism of `Groupoid`s. -/
structure Functor {S S' : Sort _} (G : Groupoid S) (G' : Groupoid S')
    extends Category.Functor G.toCategory G'.toCategory

namespace Functor

variable {R S T : Sort _} [F : Groupoid R] [G : Groupoid S] [H : Groupoid T]
variable (Ψ : Groupoid.Functor F G) (Φ : Groupoid.Functor G H)

/--
@isnad1 id=eq.0h4v.s7.1af42c05cc30 from=translated src=- shape=37c53c5a vocab=7566a40d
-/
theorem map_id' {X : S} : Φ.map (𝟙 X) = 𝟙 (Φ.obj X) := by
  simp_all

/--
@isnad1 id=eq.0h6v.s7.dc0efcee57dc from=translated src=- shape=ca520372 vocab=356b740b
-/
@[simp] theorem map_inv {X Y : S} (g : X ⟶ Y) : Φ.map g⁻¹ = (Φ.map g)⁻¹ := by
  apply (Groupoid.left_cancel (Φ.map g) _ _).mp
  rw [← Φ.map_comp]
  simp

end Functor

end Groupoid
end LeanPool.Polylean

/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.AlgebraicGeometry.Modules.Sheaf

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The action on top sections of a module-sheaf pushforward

For an arbitrary scheme morphism `f : Z ⟶ Y`, the action of `Γ(Y, ⊤)` on
top sections of `f_* M` is restriction of the native `Γ(Z, ⊤)`-action along
`f.appTop`. The carrier identification explicitly uses `f ⁻¹ᵁ ⊤ = ⊤`.
This is an underived identity; no affineness or quasi-coherence is needed.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Top sections of a pushforward are top sections of the original sheaf, as
abelian groups. This records the preimage-of-top transport; the two module
actions are compared separately in `pushforward_smul_appTop`.
@isnad1 id=eq.0h4v.s8.e3967be92125 from=translated src=- shape=fa446278 vocab=2d99079a
-/
theorem pushforward_obj_obj_top {Z Y : Scheme.{u}} (f : Z ⟶ Y) (M : Z.Modules) :
    Γ((pushforward f).obj M, (⊤ : Y.Opens)) = Γ(M, (⊤ : Z.Opens)) := by
  rw [pushforward_obj_obj, TopologicalSpace.Opens.map_top]

/-- The `Γ(Y, ⊤)`-action on `Γ(f_* M, ⊤)` is the native action on
`Γ(M, ⊤)` after applying `f.appTop`. The `show` identifies the underlying
section carriers; `pushforward_obj_obj_top` records the top-open equality.
@isnad1 id=eq.0h6v.s15.038027665151 from=translated src=- shape=120c9e43 vocab=800f6c23
-/
theorem pushforward_smul_appTop {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    (M : Z.Modules) (a : Γ(Y, ⊤))
    (m : Γ((pushforward f).obj M, ⊤)) :
    a • m = f.appTop.hom a • (show Γ(M, ⊤) from m) := by
  rfl

end AlgebraicGeometry.Scheme.Modules

import Tengoku.HodgeStructuresLean4.HodgePilot.Tier6

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Morphisms of pure rational Hodge structures

A morphism of pure Hodge structures of the same weight is a ℚ-linear map
whose complexification carries each `H^{p,q}` into `H^{p,q}`. Identity and
composition make them the morphisms of a category (packaging as a
`CategoryTheory.Category` instance comes later). -/

open scoped TensorProduct

noncomputable section

namespace HodgePilot

variable {n : ℤ} {V W U : Type*}
  [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
  [AddCommGroup W] [Module ℚ W] [Module.Finite ℚ W]
  [AddCommGroup U] [Module ℚ U] [Module.Finite ℚ U]

/-- A morphism of pure rational Hodge structures of weight `n`: a ℚ-linear
map whose complexification respects the `(p,q)`-decomposition.-/
structure HodgeHom (hV : QHodgeStructure n V) (hW : QHodgeStructure n W) where
  toLinearMap : V →ₗ[ℚ] W
  maps_pieces : ∀ pq : ℤ × ℤ,
    (hV.H pq).map (toLinearMap.baseChange ℂ) ≤ hW.H pq

namespace HodgeHom

/-- The identity morphism.-/
def id (hV : QHodgeStructure n V) : HodgeHom hV hV where
  toLinearMap := LinearMap.id
  maps_pieces := fun pq => by
    rw [LinearMap.baseChange_id, Submodule.map_id]

/-- Composition of morphisms of Hodge structures.-/
def comp {hV : QHodgeStructure n V} {hW : QHodgeStructure n W}
    {hU : QHodgeStructure n U}
    (g : HodgeHom hW hU) (f : HodgeHom hV hW) : HodgeHom hV hU where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  maps_pieces := fun pq => by
    rw [LinearMap.baseChange_comp, Submodule.map_comp]
    exact le_trans (Submodule.map_mono (f.maps_pieces pq)) (g.maps_pieces pq)

@[simp] theorem id_toLinearMap (hV : QHodgeStructure n V) :
    (HodgeHom.id hV).toLinearMap = LinearMap.id := rfl

@[simp] theorem comp_toLinearMap {hV : QHodgeStructure n V}
    {hW : QHodgeStructure n W} {hU : QHodgeStructure n U}
    (g : HodgeHom hW hU) (f : HodgeHom hV hW) :
    (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap := rfl

theorem comp_id {hV : QHodgeStructure n V} {hW : QHodgeStructure n W}
    (f : HodgeHom hV hW) : f.comp (HodgeHom.id hV) = f := by
  cases f; rfl

theorem id_comp {hV : QHodgeStructure n V} {hW : QHodgeStructure n W}
    (f : HodgeHom hV hW) : (HodgeHom.id hW).comp f = f := by
  cases f; rfl

theorem comp_assoc {S : Type*} [AddCommGroup S] [Module ℚ S] [Module.Finite ℚ S]
    {hV : QHodgeStructure n V} {hW : QHodgeStructure n W}
    {hU : QHodgeStructure n U} {hS : QHodgeStructure n S}
    (h : HodgeHom hU hS) (g : HodgeHom hW hU) (f : HodgeHom hV hW) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  cases h; cases g; cases f; rfl

end HodgeHom

end HodgePilot

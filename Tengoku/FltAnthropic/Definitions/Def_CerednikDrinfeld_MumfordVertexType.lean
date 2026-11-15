import Tengoku.Seed.Combinatorics.SimpleGraph.Metric
import Tengoku.Seed.Algebra.Group.Subgroup.Defs
import Tengoku.Seed.GroupTheory.GroupAction.Defs
import Tengoku.Seed.Data.ZMod.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld.Mumford

variable {W : Type}

def vertexType (𝒯 : SimpleGraph W) (w₀ w : W) : ZMod 2 := (𝒯.dist w₀ w : ZMod 2)

/--
@isnad1 id=eq.0h4v.s6.88b9c01bc6db from=translated src=- shape=8cf97fce vocab=1cdff0a9
-/
theorem vertexType_apply (𝒯 : SimpleGraph W) (w₀ w : W) : vertexType 𝒯 w₀ w = (𝒯.dist w₀ w : ZMod 2) := rfl

/--
@isnad1 id=eq.0h3v.s6.ab4b3814870a from=translated src=- shape=b0257822 vocab=9d38d3c4
-/
@[simp] theorem vertexType_self (𝒯 : SimpleGraph W) (w₀ : W) : vertexType 𝒯 w₀ w₀ = 0 := by
  rw [vertexType, SimpleGraph.dist_self, Nat.cast_zero]

def typePreserving (G : Type) [Group G] [MulAction G W] (𝒯 : SimpleGraph W) (w₀ : W) : Subgroup G where
  carrier := {g | ∀ w : W, vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ w}
  one_mem' := fun w => by rw [one_smul]
  mul_mem' {g h} hg hh := fun w => by rw [mul_smul, hg, hh]
  inv_mem' {g} hg := fun w => by rw [← hg (g⁻¹ • w), smul_inv_smul]

/--
@isnad1 id=iff.0h5v.s6.58e3ce92821f from=translated src=- shape=0f75529c vocab=9f2bf928
-/
@[simp] theorem mem_typePreserving_iff {G : Type} [Group G] [MulAction G W] (𝒯 : SimpleGraph W) (w₀ : W) (g : G) :
    g ∈ typePreserving G 𝒯 w₀ ↔ ∀ w : W, vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ w := Iff.rfl

end CerednikDrinfeld.Mumford

end

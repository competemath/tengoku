/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.LanaOka.Oka.Topology.Sheaves.Cohomology.Pullback

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Connecting homomorphisms and the pullback map in degree zero

Two complements to `Oka/Topology/Sheaves/Cohomology/Basic.lean` and
`Oka/Topology/Sheaves/Cohomology/Pullback.lean`:

* `TopCat.Sheaf.H.δ_naturality`: the connecting homomorphisms are natural with respect to
  morphisms of short exact sequences of abelian sheaves.
* `TopCat.Sheaf.H.equiv₀_pullback`: in degree zero, the pullback map
  `H⁰(X, F) → H⁰(Y, f⁻¹ F)` along a continuous map `f : Y ⟶ X` is, on global sections, the
  unit `F(X) → (f⁻¹ F)(f⁻¹ X) = (f⁻¹ F)(Y)` of the adjunction `f⁻¹ ⊣ f_*`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite Abelian

namespace TopCat.Sheaf

variable {X Y : TopCat.{u}}

/-- `H.equiv₀` unfolded: evaluate the adjoint `ℤ → F(X)` of a morphism `ℤ_X ⟶ F` at `1`. -/
lemma H.equiv₀_apply (F : AbSheaf X) (x : H F 0) :
    H.equiv₀ F x = AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((constantSheafAdj _ AddCommGrpCat.{u} isTerminalTop).homEquiv _ F (Ext.addEquiv₀ x)) :=
  rfl

/-- The connecting homomorphisms are natural with respect to morphisms of short exact
sequences. -/
lemma H.δ_naturality {S₁ S₂ : ShortComplex (AbSheaf X)} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : H S₁.X₃ n₀) :
    H.δ h₂ n₀ n₁ h (H.map φ.τ₃ n₀ x) = H.map φ.τ₁ n₁ (H.δ h₁ n₀ n₁ h x) := by
  rw [H.δ_apply, H.δ_apply, H.map_apply, H.map_apply,
    Ext.comp_assoc_of_second_deg_zero, ← ShortComplex.ShortExact.extClass_naturality h₁ h₂ φ,
    Ext.comp_assoc_of_third_deg_zero]

variable (f : Y ⟶ X)

end TopCat.Sheaf

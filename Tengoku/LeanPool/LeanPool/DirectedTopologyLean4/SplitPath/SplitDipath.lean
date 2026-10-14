/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
module

public import Tengoku.LeanPool.LeanPool.DirectedTopologyLean4.SplitPath.SplitPath
public import Tengoku.LeanPool.LeanPool.DirectedTopologyLean4.Dipath
public import Tengoku

/-!
# LeanPool.DirectedTopologyLean4.SplitPath.SplitDipath
-/

@[expose] public section

/- This file contains definitions for splitting a directed path `γ : Dipath x y` at some point
  `T : I` yielding two different directed paths:
  * Its first part, from `x` to `γ T`, given by evaluating `γ` on `[0, T]`.
  * Its second part, from `γ T` to `y`, given by evaluating `γ` on `[T, 1]`.
-/

noncomputable section
universe u
variable {X : Type u} [DirectedSpace X] {x₀ x₁ : X}

namespace SplitDipath

open SplitPath
open scoped unitInterval

/--
@isnad1 id=isdipath.1h5v.s6.57c1e802da46 from=translated src=- shape=646827d2 vocab=e04225dd
-/
lemma first_part_is_dipath {γ : Path x₀ x₁} (γ_dipath : IsDipath γ) (T : I) :
  IsDipath (FirstPart γ T) := by
  let φ : Path 0 T := {
    toFun := fun t => ⟨(T : ℝ) * (t : ℝ), unitInterval.mul_mem T.2 t.2⟩
    source' := by simp
    target' := by simp
  }
  have φ_mono : Monotone φ := fun x y hxy => by
    change (T : ℝ) * x ≤ T * y
    apply mul_le_mul_of_nonneg_left (Subtype.coe_le_coe.mpr hxy) T.2.1
  have : FirstPart γ T = (φ.map γ.continuous_toFun).cast γ.source.symm rfl := by { ext; rfl }
  rw [this]
  apply isDipath_cast _ γ.source.symm rfl
  exact isDipath_reparam φ_mono γ_dipath

/--
@isnad1 id=isdipath.1h5v.s6.71ff25ee8143 from=translated src=- shape=e0abc0c9 vocab=c021970d
-/
lemma second_part_is_dipath {γ : Path x₀ x₁} (γ_dipath : IsDipath γ) (T : I) :
  IsDipath (SecondPart γ T) := by
  let φ : Path T 1 := {
    toFun := fun t => ⟨(σ T : ℝ) * (t : ℝ) + (T : ℝ), interp_left_mem_I T t⟩
    source' := by simp
    target' := by simp
  }
  have φ_mono : Monotone φ := fun x y hxy => by
    change (σ T : ℝ) * x + T ≤ (σ T : ℝ) * y + T
    have hmul : (σ T : ℝ) * x ≤ (σ T : ℝ) * y :=
      mul_le_mul_of_nonneg_left (Subtype.coe_le_coe.mpr hxy) (σ T).2.1
    linarith
  have : SecondPart γ T = ((φ.map γ.continuous_toFun).cast rfl γ.target.symm) := by { ext; rfl }
  rw [this]
  apply isDipath_cast _ rfl γ.target.symm
  exact isDipath_reparam φ_mono γ_dipath

/-- The first half of a dipath split at parameter `T`, viewed as a dipath from `γ 0` to `γ T`. -/
def FirstPart (γ : Dipath x₀ x₁) (T : I) : Dipath x₀ (γ T) := {
  SplitPath.FirstPart (γ : Path x₀ x₁) T with
  dipath_toPath := first_part_is_dipath γ.dipath_toPath T
}

/-- The second half of a dipath split at parameter `T`, viewed as a dipath from `γ T` to `γ 1`. -/
def SecondPart (γ : Dipath x₀ x₁) (T : I) : Dipath (γ T) x₁ := {
  SplitPath.SecondPart (γ : Path x₀ x₁) T with
  dipath_toPath := second_part_is_dipath γ.dipath_toPath T
}

/--
@isnad1 id=eq.0h6v.s7.298570a03862 from=translated src=- shape=4ac6a833 vocab=940049e6
-/
@[simp]
lemma first_part_apply (γ : Dipath x₀ x₁) (T t : I) :
  (FirstPart γ T) t = γ ⟨ T* t, unitInterval.mul_mem T.2 t.2⟩ := rfl

/--
@isnad1 id=eq.0h6v.s7.5269bf21f176 from=translated src=- shape=9d20f7f0 vocab=7f0bef5c
-/
@[simp]
lemma second_part_apply (γ : Dipath x₀ x₁) (T t : I) :
  (SecondPart γ T) t = γ ⟨(σ T : ℝ) * (t : ℝ) + (T : ℝ), interp_left_mem_I T t⟩ := rfl

/-- The reparametrization of `I` used to glue the first and second part of a dipath split at
`T` back into the original dipath, packaged as a directed self-map of `I`. -/
def transReparamMap {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) : D(I,I) where
  toFun := fun t => ⟨transReparam T t, trans_reparam_mem_I t hT₀ hT₁⟩
  continuous_toFun := Continuous.subtype_mk (continuous_trans_reparam hT₀ hT₁) _
  directed_toFun := DirectedUnitInterval.directed_of_monotone _ (monotone_trans_reparam hT₀ hT₁)

/--
@isnad1 id=eq.2h1v.s7.59e77aa910fc from=translated src=- shape=73754b58 vocab=bf562312
-/
lemma trans_reparam_map_zero {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) : transReparamMap hT₀ hT₁ 0 = 0
    :=
  Subtype.ext (trans_reparam_zero T)
/--
@isnad1 id=eq.2h1v.s7.a543b061d10b from=translated src=- shape=73754b58 vocab=bf562312
-/
lemma trans_reparam_map_one {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) : transReparamMap hT₀ hT₁ 1 = 1 :=
  Subtype.ext (trans_reparam_one hT₁)

/--
@isnad1 id=eq.2h5v.s7.839ad2b473c6 from=translated src=- shape=427ddfc8 vocab=b731b10f
-/
lemma first_trans_second_reparam_eq_self (γ : Dipath x₀ x₁) {T : I} (hT₀ : 0 < T) (hT₁ : T < 1) :
  γ = ((FirstPart γ T).trans (SecondPart γ T)).reparam
    (transReparamMap hT₀ hT₁) (trans_reparam_map_zero _ _) (trans_reparam_map_one _ _) := by
  ext t
  exact first_trans_second_reparam_eq_self_aux (γ : Path x₀ x₁) t hT₀ hT₁

end SplitDipath

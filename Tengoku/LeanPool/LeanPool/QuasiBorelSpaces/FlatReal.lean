/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.OmegaQuasiBorelSpace
public import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Basic
public import Tengoku

/-!
# LeanPool.QuasiBorelSpaces.FlatReal

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.FlatReal`.
-/

@[expose] public section

open MeasureTheory
open MeasureSpace

/-- Reals with the Lebesgue measure and a discrete ωCPO structure. -/
structure FlatReal where
  /-- The underlying real number. -/
  val : ℝ

namespace FlatReal

instance : Inhabited FlatReal := ⟨⟨0⟩⟩

instance : MeasurableSpace FlatReal :=
  MeasurableSpace.comap FlatReal.val (inferInstance : MeasurableSpace ℝ)

noncomputable instance : MeasureSpace FlatReal where
  volume := Measure.map FlatReal.mk volume

namespace R

/--
@isnad1 id=measurab.0h0v.s2.42ffaf860c22 from=translated src=- shape=54c8eceb vocab=d8a8af92
-/
@[simp, fun_prop]
lemma measurable_mk : Measurable FlatReal.mk := by
  rw [measurable_comap_iff]
  apply measurable_id

/--
@isnad1 id=measurab.0h0v.s2.3de9483f96eb from=translated src=- shape=54c8eceb vocab=a0b9c7a3
-/
@[simp, fun_prop]
lemma measurable_val : Measurable FlatReal.val := by
  apply comap_measurable

end R

instance : QuasiBorelSpace FlatReal := QuasiBorelSpace.ofMeasurableSpace

instance : PartialOrder FlatReal where
  le x y := x = y
  le_refl _ := rfl
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm _ _ h₁ _ := h₁

/-- `FlatReal` is trivially an ωCPO: chains are constant by discreteness. -/
instance : OmegaCompletePartialOrder FlatReal where
  ωSup c := c 0
  le_ωSup c n := by rw [(OrderHomClass.mono c) (Nat.zero_le n)]
  ωSup_le c x hx := by rw [hx 0]

/-- `FlatReal` is trivially an ωQBS. -/
instance : OmegaQuasiBorelSpace FlatReal where
  isHom_ωSup := by
    change QuasiBorelSpace.IsHom fun c : OmegaCompletePartialOrder.Chain FlatReal ↦ c 0
    fun_prop

instance : TopologicalSpace FlatReal :=
  TopologicalSpace.induced val inferInstance

/--
@isnad1 id=iff.0h2v.s4.e8701193b14f from=translated src=- shape=64317b01 vocab=c0891417
-/
@[simp]
lemma le_iff_eq {x y : FlatReal} : x ≤ y ↔ x = y := by rfl

open OmegaCompletePartialOrder

/--
@isnad1 id=scottcon.0h2v.s3.e44402c03c50 from=translated src=- shape=04cfd3de vocab=e9626403
-/
@[simp, fun_prop]
lemma ωScottContinuous_of
    {A : Type*} [OmegaCompletePartialOrder A] (f : FlatReal → A)
    : ωScottContinuous f := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun x y hxy ↦ ?_, fun c ↦ ?_⟩
  · simp_all
  · simp only [ωSup]
    apply le_antisymm
    · apply le_ωSup_of_le 0
      change f (c 0) ≤ f (c 0)
      exact le_rfl
    · simp only [ωSup_le_iff, Chain.coe_map, Function.comp_apply]
      intro i
      apply le_of_eq
      change f (c i) = f (c 0)
      congr 1
      symm
      apply (OrderHomClass.mono c)
      simp only [zero_le]

end FlatReal

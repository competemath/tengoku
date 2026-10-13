/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Depth.Defs
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Internal

/-!
# Computational depth -- proof internals
-/

public section

namespace Complexity

/--
@isnad1 id=eq.0h1v.s4.488bc21aa9e0 from=translated src=- shape=0a237b80 vocab=bc35d233
-/
theorem descriptionDifference_top_left_internal (lower : WithTop ℕ) :
    descriptionDifference ⊤ lower = ⊤ := by
  rfl

/--
@isnad1 id=eq.0h1v.s4.8e7b081d564c from=translated src=- shape=0ea9bcb8 vocab=bc35d233
-/
theorem descriptionDifference_top_right_internal (upper : WithTop ℕ) :
    descriptionDifference upper ⊤ = ⊤ := by
  induction upper using WithTop.recTopCoe <;> rfl

/--
@isnad1 id=eq.0h2v.s5.f80ab75bbbab from=translated src=- shape=ba82d10c vocab=c6c7ff85
-/
theorem descriptionDifference_coe_internal (upper lower : ℕ) :
    descriptionDifference (upper : WithTop ℕ) (lower : WithTop ℕ) =
      (upper - lower : ℕ) := by
  rfl

/--
@isnad1 id=eq.1h2v.s5.25a7a4502471 from=translated src=- shape=b6b4c107 vocab=e27507bb
-/
theorem descriptionDifference_add_lower_internal
    {upper lower : WithTop ℕ} (horder : lower ≤ upper) :
    descriptionDifference upper lower + lower = upper := by
  induction upper using WithTop.recTopCoe with
  | top => simp [descriptionDifference]
  | coe upper =>
      induction lower using WithTop.recTopCoe with
      | top => simp at horder
      | coe lower =>
          change ((upper - lower + lower : ℕ) : WithTop ℕ) = upper
          exact WithTop.coe_eq_coe.mpr <|
            Nat.sub_add_cancel (WithTop.coe_le_coe.mp horder)

/--
@isnad1 id=le.1h2v.s4.136dc7f7aa56 from=translated src=- shape=59b3db05 vocab=2f0fed00
-/
theorem descriptionDifference_le_upper_internal
    {upper lower : WithTop ℕ} (horder : lower ≤ upper) :
    descriptionDifference upper lower ≤ upper := by
  induction upper using WithTop.recTopCoe with
  | top => exact le_top
  | coe upper =>
      induction lower using WithTop.recTopCoe with
      | top => simp at horder
      | coe lower =>
          exact WithTop.coe_le_coe.mpr (Nat.sub_le upper lower)

/--
@isnad1 id=le.2h3v.s5.7bfe9bc5f80a from=translated src=- shape=d3afb294 vocab=2f0fed00
-/
theorem descriptionDifference_mono_left_internal
    {lower first second : WithTop ℕ}
    (hlower : lower ≤ first) (hupper : first ≤ second) :
    descriptionDifference first lower ≤
      descriptionDifference second lower := by
  induction second using WithTop.recTopCoe with
  | top => exact le_top
  | coe second =>
      induction first using WithTop.recTopCoe with
      | top => simp at hupper
      | coe first =>
          induction lower using WithTop.recTopCoe with
          | top => simp at hlower
          | coe lower =>
              exact WithTop.coe_le_coe.mpr <|
                Nat.sub_le_sub_right (WithTop.coe_le_coe.mp hupper) lower

/--
@isnad1 id=le.2h3v.s5.538be3d3bf29 from=translated src=- shape=16ca8f18 vocab=2f0fed00
-/
theorem descriptionDifference_anti_right_internal
    {upper firstLower secondLower : WithTop ℕ}
    (hlower : secondLower ≤ firstLower) (hupper : firstLower ≤ upper) :
    descriptionDifference upper firstLower ≤
      descriptionDifference upper secondLower := by
  induction upper using WithTop.recTopCoe with
  | top => simp [descriptionDifference]
  | coe upper =>
      induction firstLower using WithTop.recTopCoe with
      | top => simp at hupper
      | coe firstLower =>
          induction secondLower using WithTop.recTopCoe with
          | top => simp at hlower
          | coe secondLower =>
              exact WithTop.coe_le_coe.mpr <|
                Nat.sub_le_sub_left
                  (WithTop.coe_le_coe.mp hlower) upper

/--
@isnad1 id=iff.1h2v.s5.d9f55b0daa23 from=translated src=- shape=cd413d0a vocab=1a9531b7
-/
theorem descriptionDifference_eq_top_iff_internal
    {upper lower : WithTop ℕ} (horder : lower ≤ upper) :
    descriptionDifference upper lower = ⊤ ↔ upper = ⊤ := by
  induction upper using WithTop.recTopCoe with
  | top => simp [descriptionDifference]
  | coe upper =>
      induction lower using WithTop.recTopCoe with
      | top => simp at horder
      | coe lower =>
          simp only [descriptionDifference, WithTop.recTopCoe_coe]
          exact iff_of_false WithTop.coe_ne_top WithTop.coe_ne_top

/--
@isnad1 id=iff.2h2v.s5.e3d7d7aca7a4 from=translated src=- shape=6fbab447 vocab=1a9531b7
-/
theorem descriptionDifference_eq_zero_iff_internal
    {upper lower : WithTop ℕ} (horder : lower ≤ upper)
    (hfinite : upper ≠ ⊤) :
    descriptionDifference upper lower = 0 ↔ upper = lower := by
  have hlowerFinite : lower ≠ ⊤ := by
    intro hlower
    rw [hlower] at horder
    exact hfinite (top_unique horder)
  obtain ⟨upperValue, hupperValue⟩ := WithTop.ne_top_iff_exists.mp hfinite
  obtain ⟨lowerValue, hlowerValue⟩ :=
    WithTop.ne_top_iff_exists.mp hlowerFinite
  have hvalueOrder : lowerValue ≤ upperValue := by
    rw [← hlowerValue, ← hupperValue] at horder
    exact WithTop.coe_le_coe.mp horder
  rw [← hupperValue, ← hlowerValue]
  change ((upperValue - lowerValue : ℕ) : WithTop ℕ) = (0 : ℕ) ↔
    (upperValue : WithTop ℕ) = (lowerValue : ℕ)
  constructor
  · intro hzero
    apply WithTop.coe_eq_coe.mpr
    have hsub := WithTop.coe_eq_coe.mp hzero
    exact Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp hsub) hvalueOrder
  · intro heq
    apply WithTop.coe_eq_coe.mpr
    have hvalues : upperValue = lowerValue := by
      exact WithTop.coe_injective heq
    simp [hvalues]

/--
@isnad1 id=eq.2h3v.s5.d22166f7c59c from=translated src=- shape=4590e86d vocab=e27507bb
-/
theorem descriptionDifference_add_internal
    {upper middle lower : WithTop ℕ}
    (hlower : lower ≤ middle) (hupper : middle ≤ upper) :
    descriptionDifference upper middle +
        descriptionDifference middle lower =
      descriptionDifference upper lower := by
  induction upper using WithTop.recTopCoe with
  | top => simp [descriptionDifference, WithTop.top_add]
  | coe upper =>
      induction middle using WithTop.recTopCoe with
      | top => simp at hupper
      | coe middle =>
          induction lower using WithTop.recTopCoe with
          | top => simp at hlower
          | coe lower =>
              change (((upper - middle) + (middle - lower) : ℕ) : WithTop ℕ) =
                ((upper - lower : ℕ) : WithTop ℕ)
              have hlowerValue : lower ≤ middle := by
                exact_mod_cast hlower
              have hupperValue : middle ≤ upper := by
                exact_mod_cast hupper
              have hidentity :
                  (upper - middle) + (middle - lower) = upper - lower := by
                omega
              exact congrArg (Nat.cast (R := WithTop ℕ)) hidentity
namespace TM
variable {n : ℕ}

/--
@isnad1 id=eq.1h5v.s5.823d3e2c3693 from=translated src=- shape=a4f0a6f7 vocab=74a49760
-/
theorem computationalDepthBetween_add_later_internal
    (machine : TM n) (output : List Bool)
    {firstTime laterTime : ℕ} (hclock : firstTime ≤ laterTime) :
    machine.computationalDepthBetween output firstTime laterTime +
        machine.timeBoundedKolmogorovComplexity output laterTime =
      machine.timeBoundedKolmogorovComplexity output firstTime := by
  exact descriptionDifference_add_lower_internal
    (timeBoundedKolmogorovComplexity_mono_internal
      machine output hclock)

/--
@isnad1 id=le.1h5v.s5.86aa457b129f from=translated src=- shape=25f15808 vocab=ae6b6b67
-/
theorem computationalDepthBetween_le_first_internal
    (machine : TM n) (output : List Bool)
    {firstTime laterTime : ℕ} (hclock : firstTime ≤ laterTime) :
    machine.computationalDepthBetween output firstTime laterTime ≤
      machine.timeBoundedKolmogorovComplexity output firstTime := by
  exact descriptionDifference_le_upper_internal
    (timeBoundedKolmogorovComplexity_mono_internal
      machine output hclock)

/--
@isnad1 id=iff.1h5v.s5.9d59bd4c3732 from=translated src=- shape=3f9bd50f vocab=96307e98
-/
theorem computationalDepthBetween_eq_top_iff_internal
    (machine : TM n) (output : List Bool)
    {firstTime laterTime : ℕ} (hclock : firstTime ≤ laterTime) :
    machine.computationalDepthBetween output firstTime laterTime = ⊤ ↔
      machine.timeBoundedKolmogorovComplexity output firstTime = ⊤ := by
  exact descriptionDifference_eq_top_iff_internal
    (timeBoundedKolmogorovComplexity_mono_internal
      machine output hclock)

/--
@isnad1 id=le.2h6v.s5.cd882cf76c41 from=translated src=- shape=22f60a4a vocab=f7225459
-/
theorem computationalDepthBetween_mono_first_internal
    (machine : TM n) (output : List Bool)
    {firstTime secondTime laterTime : ℕ}
    (hfirst : firstTime ≤ secondTime) (hsecond : secondTime ≤ laterTime) :
    machine.computationalDepthBetween output secondTime laterTime ≤
      machine.computationalDepthBetween output firstTime laterTime := by
  apply descriptionDifference_mono_left_internal
  · exact timeBoundedKolmogorovComplexity_mono_internal
      machine output hsecond
  · exact timeBoundedKolmogorovComplexity_mono_internal
      machine output hfirst

/--
@isnad1 id=le.2h6v.s5.a04840badf23 from=translated src=- shape=327bae19 vocab=f7225459
-/
theorem computationalDepthBetween_mono_later_internal
    (machine : TM n) (output : List Bool)
    {firstTime secondTime laterTime : ℕ}
    (hfirst : firstTime ≤ secondTime) (hsecond : secondTime ≤ laterTime) :
    machine.computationalDepthBetween output firstTime secondTime ≤
      machine.computationalDepthBetween output firstTime laterTime := by
  apply descriptionDifference_anti_right_internal
  · exact timeBoundedKolmogorovComplexity_mono_internal
      machine output hsecond
  · exact timeBoundedKolmogorovComplexity_mono_internal
      machine output hfirst

/--
@isnad1 id=iff.2h5v.s6.4f47c3e77952 from=translated src=- shape=9e4f0689 vocab=96307e98
-/
theorem computationalDepthBetween_eq_zero_iff_internal
    (machine : TM n) (output : List Bool)
    {firstTime laterTime : ℕ} (hclock : firstTime ≤ laterTime)
    (hfinite : machine.timeBoundedKolmogorovComplexity output firstTime ≠ ⊤) :
    machine.computationalDepthBetween output firstTime laterTime = 0 ↔
      machine.timeBoundedKolmogorovComplexity output firstTime =
        machine.timeBoundedKolmogorovComplexity output laterTime := by
  exact descriptionDifference_eq_zero_iff_internal
    (timeBoundedKolmogorovComplexity_mono_internal
      machine output hclock) hfinite

/--
@isnad1 id=eq.1h5v.s5.51b17376699c from=translated src=- shape=e61c42e6 vocab=ae6ca469
-/
theorem computationalDepthBetween_eq_computationalDepth_internal
    (machine : TM n) (output : List Bool) (firstTime laterTime : ℕ)
    (hlater : machine.timeBoundedKolmogorovComplexity output laterTime =
      machine.plainKolmogorovComplexity output) :
    machine.computationalDepthBetween output firstTime laterTime =
      machine.computationalDepth output firstTime := by
  rw [computationalDepthBetween, computationalDepth, hlater]

/--
@isnad1 id=eq.2h6v.s5.0334672d6f6e from=translated src=- shape=84b9bee0 vocab=86c606d9
-/
theorem computationalDepthBetween_add_internal
    (machine : TM n) (output : List Bool)
    {firstTime secondTime laterTime : ℕ}
    (hfirst : firstTime ≤ secondTime) (hsecond : secondTime ≤ laterTime) :
    machine.computationalDepthBetween output firstTime secondTime +
        machine.computationalDepthBetween output secondTime laterTime =
      machine.computationalDepthBetween output firstTime laterTime := by
  exact descriptionDifference_add_internal
    (timeBoundedKolmogorovComplexity_mono_internal
      machine output hsecond)
    (timeBoundedKolmogorovComplexity_mono_internal
      machine output hfirst)

/--
@isnad1 id=eq.0h4v.s5.176e23311f7c from=translated src=- shape=568c948d vocab=17df733a
-/
theorem computationalDepth_add_plain_internal
    (machine : TM n) (output : List Bool) (time : ℕ) :
    machine.computationalDepth output time +
        machine.plainKolmogorovComplexity output =
      machine.timeBoundedKolmogorovComplexity output time := by
  exact descriptionDifference_add_lower_internal
    (plainKolmogorovComplexity_le_timeBounded_internal machine output time)

/--
@isnad1 id=le.0h4v.s4.043a878c327a from=translated src=- shape=cde05369 vocab=8a9b193e
-/
theorem computationalDepth_le_timeBoundedKolmogorovComplexity_internal
    (machine : TM n) (output : List Bool) (time : ℕ) :
    machine.computationalDepth output time ≤
      machine.timeBoundedKolmogorovComplexity output time := by
  exact descriptionDifference_le_upper_internal
    (plainKolmogorovComplexity_le_timeBounded_internal machine output time)

/--
@isnad1 id=iff.0h4v.s5.90011eb8c158 from=translated src=- shape=c5e5d7d6 vocab=bf78b76e
-/
theorem computationalDepth_eq_top_iff_internal
    (machine : TM n) (output : List Bool) (time : ℕ) :
    machine.computationalDepth output time = ⊤ ↔
      machine.timeBoundedKolmogorovComplexity output time = ⊤ := by
  exact descriptionDifference_eq_top_iff_internal
    (plainKolmogorovComplexity_le_timeBounded_internal machine output time)

/--
@isnad1 id=le.1h5v.s5.e3b35a9f0925 from=translated src=- shape=09081fa1 vocab=61daacf8
-/
theorem computationalDepth_mono_internal
    (machine : TM n) (output : List Bool)
    {first second : ℕ} (hclock : first ≤ second) :
    machine.computationalDepth output second ≤
      machine.computationalDepth output first := by
  apply descriptionDifference_mono_left_internal
  · exact plainKolmogorovComplexity_le_timeBounded_internal
      machine output second
  · exact timeBoundedKolmogorovComplexity_mono_internal
      machine output hclock

/--
@isnad1 id=iff.1h4v.s5.161ea5fa7cbf from=translated src=- shape=21cae9b5 vocab=27492801
-/
theorem computationalDepth_eq_zero_iff_internal
    (machine : TM n) (output : List Bool) (time : ℕ)
    (hfinite : machine.timeBoundedKolmogorovComplexity output time ≠ ⊤) :
    machine.computationalDepth output time = 0 ↔
      machine.timeBoundedKolmogorovComplexity output time =
        machine.plainKolmogorovComplexity output := by
  exact descriptionDifference_eq_zero_iff_internal
    (plainKolmogorovComplexity_le_timeBounded_internal machine output time)
    hfinite

end TM

end Complexity

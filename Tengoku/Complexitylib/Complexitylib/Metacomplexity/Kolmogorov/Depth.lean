/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Depth.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Depth.Internal

/-!
# Computational depth

Machine-relative computational depth is formalized as
`C_M^time(output) - C_M(output)`. The extended-natural difference preserves
`⊤` rather than totalizing a missing description as zero. The exact additive
decomposition, finiteness criterion, clock monotonicity, and zero-depth
characterization are proved before any symmetry-of-information hypothesis.
-/

public section

namespace Complexity

/-- Infinite upper description length gives infinite difference.
@isnad1 id=eq.0h1v.s4.488bc21aa9e0 from=translated src=- shape=0a237b80 vocab=bc35d233
-/
@[simp] theorem descriptionDifference_top_left (lower : WithTop ℕ) :
    descriptionDifference ⊤ lower = ⊤ :=
  descriptionDifference_top_left_internal lower

/-- Infinite lower description length gives infinite difference.
@isnad1 id=eq.0h1v.s4.8e7b081d564c from=translated src=- shape=0ea9bcb8 vocab=bc35d233
-/
@[simp] theorem descriptionDifference_top_right (upper : WithTop ℕ) :
    descriptionDifference upper ⊤ = ⊤ :=
  descriptionDifference_top_right_internal upper

/-- On finite values, description difference is natural subtraction.
@isnad1 id=eq.0h2v.s5.f80ab75bbbab from=translated src=- shape=ba82d10c vocab=c6c7ff85
-/
@[simp] theorem descriptionDifference_coe (upper lower : ℕ) :
    descriptionDifference (upper : WithTop ℕ) (lower : WithTop ℕ) =
      (upper - lower : ℕ) :=
  descriptionDifference_coe_internal upper lower

/-- If the lower description length is at most the upper one, their difference
adds back to the upper length exactly.
@isnad1 id=eq.1h2v.s5.25a7a4502471 from=translated src=- shape=b6b4c107 vocab=e27507bb
-/
theorem descriptionDifference_add_lower
    {upper lower : WithTop ℕ} (horder : lower ≤ upper) :
    descriptionDifference upper lower + lower = upper :=
  descriptionDifference_add_lower_internal horder

/-- Under the same order, description difference is infinite exactly when its
upper value is infinite.
@isnad1 id=iff.1h2v.s5.d9f55b0daa23 from=translated src=- shape=cd413d0a vocab=1a9531b7
-/
theorem descriptionDifference_eq_top_iff
    {upper lower : WithTop ℕ} (horder : lower ≤ upper) :
    descriptionDifference upper lower = ⊤ ↔ upper = ⊤ :=
  descriptionDifference_eq_top_iff_internal horder

/-- For a finite ordered pair, description difference vanishes exactly when
the two lengths coincide.
@isnad1 id=iff.2h2v.s5.e3d7d7aca7a4 from=translated src=- shape=6fbab447 vocab=1a9531b7
-/
theorem descriptionDifference_eq_zero_iff
    {upper lower : WithTop ℕ} (horder : lower ≤ upper)
    (hfinite : upper ≠ ⊤) :
    descriptionDifference upper lower = 0 ↔ upper = lower :=
  descriptionDifference_eq_zero_iff_internal horder hfinite

/-- Description differences telescope through an ordered intermediate value.
@isnad1 id=eq.2h3v.s5.d22166f7c59c from=translated src=- shape=4590e86d vocab=e27507bb
-/
theorem descriptionDifference_add
    {upper middle lower : WithTop ℕ}
    (hlower : lower ≤ middle) (hupper : middle ≤ upper) :
    descriptionDifference upper middle +
        descriptionDifference middle lower =
      descriptionDifference upper lower :=
  descriptionDifference_add_internal hlower hupper

namespace TM

variable {n : ℕ}

/-- Two-clock depth plus the later-clock complexity reconstructs the earlier-
clock complexity exactly.
@isnad1 id=eq.1h5v.s5.823d3e2c3693 from=translated src=- shape=a4f0a6f7 vocab=74a49760
-/
theorem computationalDepthBetween_add_later
    (machine : TM n) (output : List Bool)
    {firstTime laterTime : ℕ} (hclock : firstTime ≤ laterTime) :
    machine.computationalDepthBetween output firstTime laterTime +
        machine.timeBoundedKolmogorovComplexity output laterTime =
      machine.timeBoundedKolmogorovComplexity output firstTime :=
  computationalDepthBetween_add_later_internal
    machine output hclock

/-- Two-clock depth never exceeds the earlier-clock complexity.
@isnad1 id=le.1h5v.s5.86aa457b129f from=translated src=- shape=25f15808 vocab=ae6b6b67
-/
theorem computationalDepthBetween_le_first
    (machine : TM n) (output : List Bool)
    {firstTime laterTime : ℕ} (hclock : firstTime ≤ laterTime) :
    machine.computationalDepthBetween output firstTime laterTime ≤
      machine.timeBoundedKolmogorovComplexity output firstTime :=
  computationalDepthBetween_le_first_internal machine output hclock

/-- Ordered two-clock depth is infinite exactly when the earlier-clock
complexity is infinite.
@isnad1 id=iff.1h5v.s5.9d59bd4c3732 from=translated src=- shape=3f9bd50f vocab=96307e98
-/
theorem computationalDepthBetween_eq_top_iff
    (machine : TM n) (output : List Bool)
    {firstTime laterTime : ℕ} (hclock : firstTime ≤ laterTime) :
    machine.computationalDepthBetween output firstTime laterTime = ⊤ ↔
      machine.timeBoundedKolmogorovComplexity output firstTime = ⊤ :=
  computationalDepthBetween_eq_top_iff_internal machine output hclock

/-- Delaying the earlier clock toward a fixed later clock cannot increase the
remaining depth.
@isnad1 id=le.2h6v.s5.cd882cf76c41 from=translated src=- shape=22f60a4a vocab=f7225459
-/
theorem computationalDepthBetween_mono_first
    (machine : TM n) (output : List Bool)
    {firstTime secondTime laterTime : ℕ}
    (hfirst : firstTime ≤ secondTime) (hsecond : secondTime ≤ laterTime) :
    machine.computationalDepthBetween output secondTime laterTime ≤
      machine.computationalDepthBetween output firstTime laterTime :=
  computationalDepthBetween_mono_first_internal
    machine output hfirst hsecond

/-- Extending the later clock away from a fixed earlier clock cannot decrease
the accumulated depth.
@isnad1 id=le.2h6v.s5.a04840badf23 from=translated src=- shape=327bae19 vocab=f7225459
-/
theorem computationalDepthBetween_mono_later
    (machine : TM n) (output : List Bool)
    {firstTime secondTime laterTime : ℕ}
    (hfirst : firstTime ≤ secondTime) (hsecond : secondTime ≤ laterTime) :
    machine.computationalDepthBetween output firstTime secondTime ≤
      machine.computationalDepthBetween output firstTime laterTime :=
  computationalDepthBetween_mono_later_internal
    machine output hfirst hsecond

/-- On a finite earlier-clock instance, two-clock depth is zero exactly when
the extra time does not improve description length.
@isnad1 id=iff.2h5v.s6.4f47c3e77952 from=translated src=- shape=9e4f0689 vocab=96307e98
-/
theorem computationalDepthBetween_eq_zero_iff
    (machine : TM n) (output : List Bool)
    {firstTime laterTime : ℕ} (hclock : firstTime ≤ laterTime)
    (hfinite : machine.timeBoundedKolmogorovComplexity output firstTime ≠ ⊤) :
    machine.computationalDepthBetween output firstTime laterTime = 0 ↔
      machine.timeBoundedKolmogorovComplexity output firstTime =
        machine.timeBoundedKolmogorovComplexity output laterTime :=
  computationalDepthBetween_eq_zero_iff_internal
    machine output hclock hfinite

/-- Once the later clock attains plain complexity, two-clock depth is exactly
the usual one-clock computational depth.
@isnad1 id=eq.1h5v.s5.51b17376699c from=translated src=- shape=e61c42e6 vocab=ae6ca469
-/
theorem computationalDepthBetween_eq_computationalDepth
    (machine : TM n) (output : List Bool) (firstTime laterTime : ℕ)
    (hlater : machine.timeBoundedKolmogorovComplexity output laterTime =
      machine.plainKolmogorovComplexity output) :
    machine.computationalDepthBetween output firstTime laterTime =
      machine.computationalDepth output firstTime :=
  computationalDepthBetween_eq_computationalDepth_internal
    machine output firstTime laterTime hlater

/-- Two-clock depths telescope exactly across three ordered clocks.
@isnad1 id=eq.2h6v.s5.0334672d6f6e from=translated src=- shape=84b9bee0 vocab=86c606d9
-/
theorem computationalDepthBetween_add
    (machine : TM n) (output : List Bool)
    {firstTime secondTime laterTime : ℕ}
    (hfirst : firstTime ≤ secondTime) (hsecond : secondTime ≤ laterTime) :
    machine.computationalDepthBetween output firstTime secondTime +
        machine.computationalDepthBetween output secondTime laterTime =
      machine.computationalDepthBetween output firstTime laterTime :=
  computationalDepthBetween_add_internal machine output hfirst hsecond

/-- Computational depth plus plain complexity is exactly bounded complexity;
the subtraction is therefore nontruncated on every finite instance.
@isnad1 id=eq.0h4v.s5.176e23311f7c from=translated src=- shape=568c948d vocab=17df733a
-/
theorem computationalDepth_add_plain
    (machine : TM n) (output : List Bool) (time : ℕ) :
    machine.computationalDepth output time +
        machine.plainKolmogorovComplexity output =
      machine.timeBoundedKolmogorovComplexity output time :=
  computationalDepth_add_plain_internal machine output time

/-- Computational depth never exceeds the corresponding bounded complexity.
@isnad1 id=le.0h4v.s4.043a878c327a from=translated src=- shape=cde05369 vocab=8a9b193e
-/
theorem computationalDepth_le_timeBoundedKolmogorovComplexity
    (machine : TM n) (output : List Bool) (time : ℕ) :
    machine.computationalDepth output time ≤
      machine.timeBoundedKolmogorovComplexity output time :=
  computationalDepth_le_timeBoundedKolmogorovComplexity_internal
    machine output time

/-- Depth is infinite exactly when bounded complexity is infinite. Plain
complexity cannot be the sole source of infinitude because `C_M ≤ C_M^time`.
@isnad1 id=iff.0h4v.s5.90011eb8c158 from=translated src=- shape=c5e5d7d6 vocab=bf78b76e
-/
theorem computationalDepth_eq_top_iff
    (machine : TM n) (output : List Bool) (time : ℕ) :
    machine.computationalDepth output time = ⊤ ↔
      machine.timeBoundedKolmogorovComplexity output time = ⊤ :=
  computationalDepth_eq_top_iff_internal machine output time

/-- More computation time cannot increase computational depth.
@isnad1 id=le.1h5v.s5.e3b35a9f0925 from=translated src=- shape=09081fa1 vocab=61daacf8
-/
theorem computationalDepth_mono
    (machine : TM n) (output : List Bool)
    {first second : ℕ} (hclock : first ≤ second) :
    machine.computationalDepth output second ≤
      machine.computationalDepth output first :=
  computationalDepth_mono_internal machine output hclock

/-- On a finite bounded instance, depth is zero exactly when the time bound
already attains plain complexity.
@isnad1 id=iff.1h4v.s5.161ea5fa7cbf from=translated src=- shape=21cae9b5 vocab=27492801
-/
theorem computationalDepth_eq_zero_iff
    (machine : TM n) (output : List Bool) (time : ℕ)
    (hfinite : machine.timeBoundedKolmogorovComplexity output time ≠ ⊤) :
    machine.computationalDepth output time = 0 ↔
      machine.timeBoundedKolmogorovComplexity output time =
        machine.plainKolmogorovComplexity output :=
  computationalDepth_eq_zero_iff_internal machine output time hfinite

end TM

end Complexity

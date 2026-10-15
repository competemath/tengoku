/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Tengoku

/-!
# LeanPool.SardMoreira.UpperLowerSemicontinuous
-/

@[expose] public section

open Set Filter Function TopologicalSpace

namespace Topology

variable {X Y : Type*} [TopologicalSpace X] [LinearOrder Y] {f : X → Y} {s : Set X} {x : X}

/--
@isnad1 id=iff.0h5v.s6.dfd9a7f353b5 from=translated src=- shape=a763765d vocab=5f3b7158
-/
theorem continuousWithinAt_toLower_comp_iff :
    ContinuousWithinAt (WithLower.toLower ∘ f) s x ↔ UpperSemicontinuousWithinAt f s x :=
  IsLower.tendsto_nhds_iff_lt

/--
@isnad1 id=iff.0h5v.s6.6be0de2eb567 from=translated src=- shape=a763765d vocab=df242ce2
-/
theorem continuousWithinAt_toUpper_comp_iff :
    ContinuousWithinAt (WithUpper.toUpper ∘ f) s x ↔ LowerSemicontinuousWithinAt f s x :=
  IsUpper.tendsto_nhds_iff_lt

/--
@isnad1 id=iff.0h4v.s6.05595cc702c7 from=translated src=- shape=a9000ff2 vocab=06ad9e32
-/
theorem continuousAt_toLower_comp_iff :
    ContinuousAt (WithLower.toLower ∘ f) x ↔ UpperSemicontinuousAt f x :=
  IsLower.tendsto_nhds_iff_lt

/--
@isnad1 id=iff.0h4v.s6.e5fea3db0fde from=translated src=- shape=a9000ff2 vocab=8af03c3a
-/
theorem continuousAt_toUpper_comp_iff :
    ContinuousAt (WithUpper.toUpper ∘ f) x ↔ LowerSemicontinuousAt f x :=
  IsUpper.tendsto_nhds_iff_lt

/--
@isnad1 id=iff.0h4v.s6.dfb14dcd7e89 from=translated src=- shape=11adbbb2 vocab=1e379dc0
-/
theorem continuousOn_toLower_comp_iff :
    ContinuousOn (WithLower.toLower ∘ f) s ↔ UpperSemicontinuousOn f s :=
  forall₂_congr fun _ _ ↦ continuousWithinAt_toLower_comp_iff

/--
@isnad1 id=iff.0h4v.s6.2e6484f2563c from=translated src=- shape=11adbbb2 vocab=71d5166f
-/
theorem continuousOn_toUpper_comp_iff :
    ContinuousOn (WithUpper.toUpper ∘ f) s ↔ LowerSemicontinuousOn f s :=
  forall₂_congr fun _ _ ↦ continuousWithinAt_toUpper_comp_iff

/--
@isnad1 id=iff.0h3v.s6.022dacbe5a65 from=translated src=- shape=2856ccb4 vocab=8b6e27f6
-/
theorem continuous_toLower_comp_iff : Continuous (WithLower.toLower ∘ f) ↔ UpperSemicontinuous f :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ ↦ continuousAt_toLower_comp_iff

/--
@isnad1 id=iff.0h3v.s6.f8be794a0008 from=translated src=- shape=2856ccb4 vocab=0829d5a3
-/
theorem continuous_toUpper_comp_iff : Continuous (WithUpper.toUpper ∘ f) ↔ LowerSemicontinuous f :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ ↦ continuousAt_toUpper_comp_iff

end Topology

-- Mathlib has this lemma, but the proof is less elegant there. TODO: upstream the proof
/--
@isnad1 id=ex.3h4v.s6.91465f7a5ecf from=translated src=- shape=ac168cb3 vocab=3302cdd9
-/
theorem LowerSemicontinuousOn.exists_isMinOn' {X α : Type*} [TopologicalSpace X] [LinearOrder α]
    {f : X → α} {s : Set X} (hf : LowerSemicontinuousOn f s) (hs : IsCompact s) (hne : s.Nonempty) :
    ∃ x ∈ s, IsMinOn f s x := by
  rw [← Topology.continuousOn_toUpper_comp_iff] at hf
  exact hs.exists_isMinOn (f := Topology.WithUpper.toUpper ∘ f) hne hf

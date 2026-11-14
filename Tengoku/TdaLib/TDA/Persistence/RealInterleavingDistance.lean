import Tengoku.TdaLib.TDA.Persistence.RealInterleavingLaws
import Tengoku.Seed.Data.ENNReal.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Extended real interleaving distance

The distance is the infimum of finite parameters with witnesses. Empty infima are
infinite; no attainment or separation assumption is imposed.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence

open CategoryTheory
open scoped NNReal ENNReal

variable {R : Type u} [Ring R]
variable {M N P M' N' : PModule.{u,0,w} R ℝ}

/-- The infimum of all finite parameters admitting a real interleaving.-/
noncomputable def realInterleavingDistance (M N : PModule.{u,0,w} R ℝ) : ℝ≥0∞ :=
  ⨅ (ε : ℝ≥0) (_ : Nonempty (RealInterleaving ε M N)), (ε : ℝ≥0∞)

/-- Any witness gives an upper bound on the infimum.
@isnad1 id=le.1h4v.s5.8f0b9f79a82a from=translated src=- shape=810b37b2 vocab=69968be1
-/
theorem realInterleavingDistance_le_of_nonempty {ε : ℝ≥0}
    (h : Nonempty (RealInterleaving ε M N)) : realInterleavingDistance M N ≤ ε :=
  iInf₂_le ε h

/-- An explicit interleaving bounds the distance.
@isnad1 id=le.0h5v.s5.f72ecd32bdb9 from=translated src=- shape=1a1be81a vocab=80e24f1c
-/
theorem RealInterleaving.distance_le {ε : ℝ≥0} (i : RealInterleaving ε M N) :
    realInterleavingDistance M N ≤ ε := realInterleavingDistance_le_of_nonempty ⟨i⟩

/-- A lower bound on every admissible parameter is a lower bound on the distance.
@isnad1 id=iff.0h4v.s5.f9ef68bc6968 from=translated src=- shape=a3b79959 vocab=69968be1
-/
theorem le_realInterleavingDistance_iff {r : ℝ≥0∞} :
    r ≤ realInterleavingDistance M N ↔
      ∀ ε : ℝ≥0, Nonempty (RealInterleaving ε M N) → r ≤ ε := le_iInf₂_iff

/-- Approximate from above at any extended bound, including zero and infinity.
@isnad1 id=iff.0h4v.s5.5976603c9da7 from=translated src=- shape=7e579f32 vocab=ed8b74a9
-/
theorem realInterleavingDistance_lt_iff {r : ℝ≥0∞} :
    realInterleavingDistance M N < r ↔
      ∃ ε : ℝ≥0, (ε : ℝ≥0∞) < r ∧ Nonempty (RealInterleaving ε M N) := by
  simp only [realInterleavingDistance, iInf_lt_iff, exists_prop]
  exact exists_congr fun _ => and_comm

/-- Infinity occurs exactly when every finite-parameter witness type is empty.
@isnad1 id=iff.0h3v.s5.19cf9a81dbdd from=translated src=- shape=a4998b60 vocab=f56d16ca
-/
theorem realInterleavingDistance_eq_top_iff :
    realInterleavingDistance M N = ⊤ ↔ ∀ ε : ℝ≥0, IsEmpty (RealInterleaving ε M N) := by
  simp only [realInterleavingDistance, iInf_eq_top, ENNReal.coe_ne_top, imp_false,
    not_nonempty_iff]

/-- A zero-interleaving gives zero distance; this implication need not reverse.
@isnad1 id=eq.0h4v.s5.2856771927c0 from=translated src=- shape=918ac802 vocab=6d332397
-/
theorem RealInterleaving.distance_eq_zero (i : RealInterleaving 0 M N) :
    realInterleavingDistance M N = 0 :=
  nonpos_iff_eq_zero.1 (by simpa using i.distance_le)

/--
@isnad1 id=eq.0h2v.s4.63ea17b51e0c from=translated src=- shape=70617585 vocab=8edcc5ee
-/
theorem realInterleavingDistance_self (M : PModule.{u,0,w} R ℝ) :
    realInterleavingDistance M M = 0 := (RealInterleaving.refl 0 M).distance_eq_zero

/--
@isnad1 id=eq.0h4v.s5.e9791daf3177 from=translated src=- shape=04f1cd99 vocab=e01ac477
-/
theorem realInterleavingDistance_eq_zero_of_iso (e : M ≅ N) :
    realInterleavingDistance M N = 0 := (RealInterleaving.ofIso e).distance_eq_zero

/--
@isnad1 id=eq.0h3v.s4.bf55491aaa32 from=translated src=- shape=e91013d0 vocab=8edcc5ee
-/
theorem realInterleavingDistance_comm (M N : PModule.{u,0,w} R ℝ) :
    realInterleavingDistance M N = realInterleavingDistance N M :=
  le_antisymm (le_iInf₂ fun _ ⟨i⟩ => i.symm.distance_le)
    (le_iInf₂ fun _ ⟨i⟩ => i.symm.distance_le)

/-- Triangle holds also for empty witness sets and infinite summands.
@isnad1 id=le.0h4v.s5.569494fa495b from=translated src=- shape=31af968e vocab=4e286802
-/
theorem realInterleavingDistance_triangle (M N P : PModule.{u,0,w} R ℝ) :
    realInterleavingDistance M P ≤ realInterleavingDistance M N +
      realInterleavingDistance N P := by
  apply ENNReal.le_iInf₂_add_iInf₂
  intro ε hi δ hj
  obtain ⟨i⟩ := hi
  obtain ⟨j⟩ := hj
  simpa only [ENNReal.coe_add] using (i.trans j).distance_le

/-- Natural isomorphisms preserve the distance in both arguments.
@isnad1 id=eq.0h7v.s6.8c5b3a061ab2 from=translated src=- shape=e7880f94 vocab=e01ac477
-/
theorem realInterleavingDistance_congr (e : M ≅ M') (d : N ≅ N') :
    realInterleavingDistance M N = realInterleavingDistance M' N' :=
  le_antisymm (le_iInf₂ fun _ ⟨i⟩ => (i.congr e.symm d.symm).distance_le)
    (le_iInf₂ fun _ ⟨i⟩ => (i.congr e d).distance_le)

/-- Zero distance means witnesses at every positive parameter, without attainment.
@isnad1 id=iff.0h3v.s5.04472e6cc89e from=translated src=- shape=15cb5dd8 vocab=a7f9baa1
-/
theorem realInterleavingDistance_eq_zero_iff :
    realInterleavingDistance M N = 0 ↔
      ∀ ε : ℝ≥0, 0 < ε → Nonempty (RealInterleaving ε M N) := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, ⟨i⟩⟩ :=
      realInterleavingDistance_lt_iff.1 (h.trans_lt (ENNReal.coe_pos.2 hε))
    exact ⟨i.mono (ENNReal.coe_lt_coe.1 hδ).le⟩
  · intro h
    refine nonpos_iff_eq_zero.1 (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_)
    simpa using realInterleavingDistance_le_of_nonempty (h ε hε)

end TDA.Persistence

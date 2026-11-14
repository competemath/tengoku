import Tengoku.TdaLib.TDA.Persistence.CoordinateInterleaving
import Tengoku.Seed.Data.ENNReal.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Extended coordinatewise interleaving distance

The distance is the infimum of finite parameters with coordinatewise
interleaving witnesses. Empty infima are infinite; no attainment or separation
assumption is imposed.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence

open CategoryTheory
open scoped TDA.Persistence NNReal ENNReal

variable {R : Type u} [Ring R] {n : ℕ}
variable {M N P M' N' : PModule.{u,0,w} R (Fin n → ℝ)}

/-- The infimum of finite parameters admitting a coordinatewise interleaving.-/
noncomputable def coordinateInterleavingDistance (M N : PModule.{u,0,w} R (Fin n → ℝ)) : ℝ≥0∞ :=
  ⨅ (ε : ℝ≥0) (_ : Nonempty (CoordinateInterleaving ε M N)), (ε : ℝ≥0∞)

/-- Any coordinatewise witness gives an upper bound on the infimum.
@isnad1 id=le.1h5v.s6.45d080c04c63 from=translated src=- shape=b133e775 vocab=c3abf160
-/
theorem coordinateInterleavingDistance_le_of_nonempty {ε : ℝ≥0}
    (h : Nonempty (CoordinateInterleaving ε M N)) :
    coordinateInterleavingDistance M N ≤ ε :=
  iInf₂_le ε h

/-- An explicit coordinatewise interleaving bounds the distance.
@isnad1 id=le.0h6v.s6.30bb9fe7887b from=translated src=- shape=e106c890 vocab=336b0288
-/
theorem CoordinateInterleaving.distance_le {ε : ℝ≥0}
    (i : CoordinateInterleaving ε M N) :
    coordinateInterleavingDistance M N ≤ ε :=
  coordinateInterleavingDistance_le_of_nonempty ⟨i⟩

/-- A lower bound on every admissible parameter is a lower bound on the distance.
@isnad1 id=iff.0h5v.s6.e2f043f0e066 from=translated src=- shape=d8095afd vocab=c3abf160
-/
theorem le_coordinateInterleavingDistance_iff {r : ℝ≥0∞} :
    r ≤ coordinateInterleavingDistance M N ↔
      ∀ ε : ℝ≥0, Nonempty (CoordinateInterleaving ε M N) → r ≤ ε := le_iInf₂_iff

/-- Approximate from above at any extended bound, including zero and infinity.
@isnad1 id=iff.0h5v.s6.561a019d0e4e from=translated src=- shape=2578fb93 vocab=16ce601f
-/
theorem coordinateInterleavingDistance_lt_iff {r : ℝ≥0∞} :
    coordinateInterleavingDistance M N < r ↔
      ∃ ε : ℝ≥0, (ε : ℝ≥0∞) < r ∧ Nonempty (CoordinateInterleaving ε M N) := by
  simp only [coordinateInterleavingDistance, iInf_lt_iff, exists_prop]
  exact exists_congr fun _ => and_comm

/-- Infinity occurs exactly when every finite-parameter witness type is empty.
@isnad1 id=iff.0h4v.s6.a0d2056d8138 from=translated src=- shape=7ba84cf9 vocab=e87a6392
-/
theorem coordinateInterleavingDistance_eq_top_iff :
    coordinateInterleavingDistance M N = ⊤ ↔
      ∀ ε : ℝ≥0, IsEmpty (CoordinateInterleaving ε M N) := by
  simp only [coordinateInterleavingDistance, iInf_eq_top, ENNReal.coe_ne_top, imp_false,
    not_nonempty_iff]

/-- A zero interleaving gives zero distance; this implication need not reverse.
@isnad1 id=eq.0h5v.s6.97b49aa6a88f from=translated src=- shape=4d11a6ae vocab=1e53654e
-/
theorem CoordinateInterleaving.distance_eq_zero (i : CoordinateInterleaving 0 M N) :
    coordinateInterleavingDistance M N = 0 :=
  nonpos_iff_eq_zero.1 (by simpa using i.distance_le)

/--
@isnad1 id=eq.0h3v.s5.099e63b7587a from=translated src=- shape=11ce968c vocab=9806b693
-/
theorem coordinateInterleavingDistance_self
    (M : PModule.{u,0,w} R (Fin n → ℝ)) :
    coordinateInterleavingDistance M M = 0 :=
  (CoordinateInterleaving.refl 0 M).distance_eq_zero

/--
@isnad1 id=eq.0h5v.s6.f852f483caea from=translated src=- shape=3e66c315 vocab=7010debf
-/
theorem coordinateInterleavingDistance_eq_zero_of_iso (e : M ≅ N) :
    coordinateInterleavingDistance M N = 0 :=
  (CoordinateInterleaving.ofIso e).distance_eq_zero

/--
@isnad1 id=eq.0h4v.s5.44b5719ac020 from=translated src=- shape=e4eed521 vocab=9806b693
-/
theorem coordinateInterleavingDistance_comm
    (M N : PModule.{u,0,w} R (Fin n → ℝ)) :
    coordinateInterleavingDistance M N = coordinateInterleavingDistance N M :=
  le_antisymm (le_iInf₂ fun _ ⟨i⟩ => i.symm.distance_le)
    (le_iInf₂ fun _ ⟨i⟩ => i.symm.distance_le)

/-- Triangle holds also for empty witness sets and infinite summands.
@isnad1 id=le.0h5v.s6.9965f68f9a14 from=translated src=- shape=0cb8e076 vocab=2c3d7a06
-/
theorem coordinateInterleavingDistance_triangle
    (M N P : PModule.{u,0,w} R (Fin n → ℝ)) :
    coordinateInterleavingDistance M P ≤ coordinateInterleavingDistance M N +
      coordinateInterleavingDistance N P := by
  apply ENNReal.le_iInf₂_add_iInf₂
  intro ε hi δ hj
  obtain ⟨i⟩ := hi
  obtain ⟨j⟩ := hj
  simpa only [ENNReal.coe_add] using (i.trans j).distance_le

/-- Natural isomorphisms preserve the distance in both arguments.
@isnad1 id=eq.0h8v.s7.007307fce801 from=translated src=- shape=ce156f4e vocab=7010debf
-/
theorem coordinateInterleavingDistance_congr (e : M ≅ M') (d : N ≅ N') :
    coordinateInterleavingDistance M N = coordinateInterleavingDistance M' N' :=
  le_antisymm (le_iInf₂ fun _ ⟨i⟩ => (i.congr e.symm d.symm).distance_le)
    (le_iInf₂ fun _ ⟨i⟩ => (i.congr e d).distance_le)

/-- Zero distance means witnesses at every positive parameter, without attainment.
@isnad1 id=iff.0h4v.s6.eba022a37152 from=translated src=- shape=9d34021f vocab=3d99ae9f
-/
theorem coordinateInterleavingDistance_eq_zero_iff :
    coordinateInterleavingDistance M N = 0 ↔
      ∀ ε : ℝ≥0, 0 < ε → Nonempty (CoordinateInterleaving ε M N) := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, ⟨i⟩⟩ :=
      coordinateInterleavingDistance_lt_iff.1 (h.trans_lt (ENNReal.coe_pos.2 hε))
    exact ⟨i.mono (ENNReal.coe_lt_coe.1 hδ).le⟩
  · intro h
    refine nonpos_iff_eq_zero.1 (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_)
    simpa using coordinateInterleavingDistance_le_of_nonempty (h ε hε)

end TDA.Persistence

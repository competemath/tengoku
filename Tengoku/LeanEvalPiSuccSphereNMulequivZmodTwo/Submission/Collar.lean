import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Collaring generalized loops

Every generalized loop `p : Ω^ N X x` is homotopic rel boundary to a "collared"
reparametrization which is constantly equal to the basepoint on the collar
neighborhood of the boundary where some coordinate lies within `1/4` of `{0, 1}`.

The reparametrization applies, in each coordinate, the clamp
`t ↦ projIcc 0 1 (2 * t - 1/2)`, which squashes `[0, 1/4]` to `0` and `[3/4, 1]` to `1`.

Main declarations:

* `Submission.collared p`: the collared loop;
* `Submission.collared_eq_basepoint`: `collared p` equals `x` on the collar;
* `Submission.collarHomotopy`, `Submission.homotopic_collared`: the straight-line
  reparametrization homotopy `p ≃ collared p` rel `Cube.boundary N`.
-/

noncomputable section

open scoped Topology unitInterval
open Topology.Homotopy Set

namespace Submission

/-- Clamping a nonpositive real to `[0, 1]` gives `0`.
@isnad1 id=eq.1h1v.s6.568f938b8d69 from=translated src=- shape=7bf93669 vocab=34ad4935
-/
theorem projIcc_eq_zero {r : ℝ} (hr : r ≤ 0) :
    Set.projIcc (0 : ℝ) 1 zero_le_one r = 0 := by
  apply Subtype.ext
  rw [Set.coe_projIcc, Set.Icc.coe_zero, min_eq_right (hr.trans zero_le_one),
    max_eq_left hr]

/-- Clamping a real that is at least `1` to `[0, 1]` gives `1`.
@isnad1 id=eq.1h1v.s6.10e872a294d3 from=translated src=- shape=7d7db020 vocab=34ad4935
-/
theorem projIcc_eq_one {r : ℝ} (hr : 1 ≤ r) :
    Set.projIcc (0 : ℝ) 1 zero_le_one r = 1 := by
  apply Subtype.ext
  rw [Set.coe_projIcc, Set.Icc.coe_one, min_eq_left hr, max_eq_right zero_le_one]

variable {N X : Type*} [TopologicalSpace X] {x : X}

/-- The coordinatewise collar reparametrization of the cube: each coordinate `r` is
sent to the clamp of `2 * r - 1/2` to `[0, 1]`.-/
def collarMap (t : I^N) : I^N := fun i =>
  Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (t i : ℝ) - 1 / 2)

/--
@isnad1 id=continuo.0h1v.s6.5c5006cf7576 from=translated src=- shape=ddae8c6b vocab=b2372706
-/
theorem continuous_collarMap : Continuous (collarMap (N := N)) :=
  continuous_pi fun _ => continuous_projIcc.comp <| by fun_prop

/--
@isnad1 id=mem.1h2v.s5.d03376067eaf from=translated src=- shape=6ade49a9 vocab=931e96db
-/
theorem collarMap_mem_boundary {t : I^N} (ht : t ∈ Cube.boundary N) :
    collarMap t ∈ Cube.boundary N := by
  obtain ⟨i, hi | hi⟩ := ht
  · have h0 : (t i : ℝ) = 0 := by rw [hi, Set.Icc.coe_zero]
    exact ⟨i, Or.inl (by simp only [collarMap, h0]; exact projIcc_eq_zero (by norm_num))⟩
  · have h1 : (t i : ℝ) = 1 := by rw [hi, Set.Icc.coe_one]
    exact ⟨i, Or.inr (by simp only [collarMap, h1]; exact projIcc_eq_one (by norm_num))⟩

/-- The collared reparametrization of a generalized loop: constant equal to the
basepoint whenever some coordinate is within `1/4` of the boundary of `I`.-/
def collared (p : Ω^ N X x) : Ω^ N X x :=
  ⟨p.1.comp ⟨collarMap, continuous_collarMap⟩, fun t ht =>
    p.2 (collarMap t) (collarMap_mem_boundary ht)⟩

/--
@isnad1 id=eq.0h5v.s7.468bbe9f086c from=translated src=- shape=5edfea4b vocab=0e21c38c
-/
@[simp]
theorem collared_apply (p : Ω^ N X x) (t : I^N) : collared p t = p (collarMap t) :=
  rfl

/-- On the collar (some coordinate within `1/4` of `{0, 1}`), the collared loop is
constantly the basepoint.
@isnad1 id=eq.1h5v.s7.c3ae6ea57540 from=translated src=- shape=aca820a3 vocab=694cd0c7
-/
theorem collared_eq_basepoint (p : Ω^ N X x) {t : I^N}
    (h : ∃ i, (t i : ℝ) ≤ 1 / 4 ∨ 3 / 4 ≤ (t i : ℝ)) :
    collared p t = x := by
  obtain ⟨i, hi | hi⟩ := h
  · exact p.2 (collarMap t)
      ⟨i, Or.inl (by simp only [collarMap]; exact projIcc_eq_zero (by linarith))⟩
  · exact p.2 (collarMap t)
      ⟨i, Or.inr (by simp only [collarMap]; exact projIcc_eq_one (by linarith))⟩

/-- The linear interpolation, at time `s`, between the identity of the cube and the
collar clamp, applied coordinatewise. At `s = 0` it is the identity; at `s = 1` it is
`collarMap`.-/
def collarHomotopyMap (s : I) (t : I^N) : I^N := fun i =>
  Set.projIcc (0 : ℝ) 1 zero_le_one ((1 + (s : ℝ)) * (t i : ℝ) - (s : ℝ) / 2)

/--
@isnad1 id=continuo.0h1v.s6.f22ab4b32ecf from=translated src=- shape=cbf390b9 vocab=657beb0a
-/
theorem continuous_collarHomotopyMap :
    Continuous fun st : I × (I^N) => collarHomotopyMap st.1 st.2 :=
  continuous_pi fun _ => continuous_projIcc.comp <| by fun_prop

/--
@isnad1 id=eq.0h2v.s5.66e37f664bc6 from=translated src=- shape=13c3458e vocab=ecf5f0a5
-/
theorem collarHomotopyMap_zero (t : I^N) : collarHomotopyMap 0 t = t := by
  funext i
  have h : (1 + ((0 : I) : ℝ)) * (t i : ℝ) - ((0 : I) : ℝ) / 2 = (t i : ℝ) := by
    rw [Set.Icc.coe_zero]; ring
  simp only [collarHomotopyMap]
  rw [h]
  exact Set.projIcc_val zero_le_one (t i)

/--
@isnad1 id=eq.0h2v.s5.89109baa4ddb from=translated src=- shape=65d184ba vocab=1ab98a87
-/
theorem collarHomotopyMap_one (t : I^N) : collarHomotopyMap 1 t = collarMap t := by
  funext i
  have h : (1 + ((1 : I) : ℝ)) * (t i : ℝ) - ((1 : I) : ℝ) / 2
      = 2 * (t i : ℝ) - 1 / 2 := by
    rw [Set.Icc.coe_one]; ring
  simp only [collarHomotopyMap, collarMap]
  rw [h]

/--
@isnad1 id=mem.1h3v.s5.2e0d4450a9a7 from=translated src=- shape=e0f52373 vocab=af6d91aa
-/
theorem collarHomotopyMap_mem_boundary (s : I) {t : I^N} (ht : t ∈ Cube.boundary N) :
    collarHomotopyMap s t ∈ Cube.boundary N := by
  obtain ⟨i, hi | hi⟩ := ht
  · have h0 : (t i : ℝ) = 0 := by rw [hi, Set.Icc.coe_zero]
    refine ⟨i, Or.inl ?_⟩
    simp only [collarHomotopyMap, h0]
    exact projIcc_eq_zero (by have := s.2.1; linarith)
  · have h1 : (t i : ℝ) = 1 := by rw [hi, Set.Icc.coe_one]
    refine ⟨i, Or.inr ?_⟩
    simp only [collarHomotopyMap, h1]
    exact projIcc_eq_one (by have := s.2.1; linarith)

/-- The straight-line reparametrization homotopy from `p` to `collared p`,
rel the cube boundary.-/
def collarHomotopy (p : Ω^ N X x) :
    ContinuousMap.HomotopyRel p.1 (collared p).1 (Cube.boundary N) where
  toFun st := p (collarHomotopyMap st.1 st.2)
  continuous_toFun := (map_continuous p.1).comp continuous_collarHomotopyMap
  map_zero_left t := by
    show p (collarHomotopyMap 0 t) = p.1 t
    rw [collarHomotopyMap_zero]
    rfl
  map_one_left t := by
    show p (collarHomotopyMap 1 t) = (collared p).1 t
    rw [collarHomotopyMap_one]
    rfl
  prop' s t ht := by
    show p (collarHomotopyMap s t) = p.1 t
    exact (p.2 _ (collarHomotopyMap_mem_boundary s ht)).trans (p.2 t ht).symm

/-- Every generalized loop is homotopic rel boundary to its collared version.
@isnad1 id=homotopi.0h4v.s5.5be0ed20892d from=translated src=- shape=05cb6d2c vocab=cbd0ff30
-/
theorem homotopic_collared (p : Ω^ N X x) : GenLoop.Homotopic p (collared p) :=
  ⟨collarHomotopy p⟩

end Submission

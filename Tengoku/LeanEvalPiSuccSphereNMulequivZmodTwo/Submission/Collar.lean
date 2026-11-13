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

/-- Clamping a nonpositive real to `[0, 1]` gives `0`.-/
theorem projIcc_eq_zero {r : ℝ} (hr : r ≤ 0) :
    Set.projIcc (0 : ℝ) 1 zero_le_one r = 0 := by
  apply Subtype.ext
  rw [Set.coe_projIcc, Set.Icc.coe_zero, min_eq_right (hr.trans zero_le_one),
    max_eq_left hr]

/-- Clamping a real that is at least `1` to `[0, 1]` gives `1`.-/
theorem projIcc_eq_one {r : ℝ} (hr : 1 ≤ r) :
    Set.projIcc (0 : ℝ) 1 zero_le_one r = 1 := by
  apply Subtype.ext
  rw [Set.coe_projIcc, Set.Icc.coe_one, min_eq_left hr, max_eq_right zero_le_one]

variable {N X : Type*} [TopologicalSpace X] {x : X}

/-- The coordinatewise collar reparametrization of the cube: each coordinate `r` is
sent to the clamp of `2 * r - 1/2` to `[0, 1]`.-/
def collarMap (t : I^N) : I^N := fun i =>
  Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (t i : ℝ) - 1 / 2)

theorem continuous_collarMap : Continuous (collarMap (N := N)) :=
  continuous_pi fun _ => continuous_projIcc.comp <| by fun_prop

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

@[simp]
theorem collared_apply (p : Ω^ N X x) (t : I^N) : collared p t = p (collarMap t) :=
  rfl

/-- On the collar (some coordinate within `1/4` of `{0, 1}`), the collared loop is
constantly the basepoint.-/
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

theorem continuous_collarHomotopyMap :
    Continuous fun st : I × (I^N) => collarHomotopyMap st.1 st.2 :=
  continuous_pi fun _ => continuous_projIcc.comp <| by fun_prop

theorem collarHomotopyMap_zero (t : I^N) : collarHomotopyMap 0 t = t := by
  funext i
  have h : (1 + ((0 : I) : ℝ)) * (t i : ℝ) - ((0 : I) : ℝ) / 2 = (t i : ℝ) := by
    rw [Set.Icc.coe_zero]; ring
  simp only [collarHomotopyMap]
  rw [h]
  exact Set.projIcc_val zero_le_one (t i)

theorem collarHomotopyMap_one (t : I^N) : collarHomotopyMap 1 t = collarMap t := by
  funext i
  have h : (1 + ((1 : I) : ℝ)) * (t i : ℝ) - ((1 : I) : ℝ) / 2
      = 2 * (t i : ℝ) - 1 / 2 := by
    rw [Set.Icc.coe_one]; ring
  simp only [collarHomotopyMap, collarMap]
  rw [h]

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

/-- Every generalized loop is homotopic rel boundary to its collared version.-/
theorem homotopic_collared (p : Ω^ N X x) : GenLoop.Homotopic p (collared p) :=
  ⟨collarHomotopy p⟩

end Submission

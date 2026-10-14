/-
Copyright (c) 2026 Math_XMUM. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math_XMUM
-/
module

public import Tengoku.LeanPool.LeanPool.Brouwer.Scarf
public import Tengoku

/-!
# The Scarf path graph

This file builds the graph `G_i` whose vertices are the colorful and typed
nearly-colorful rooms and doors of a fixed type `i`, and whose edges are
room-door incidences. Following a path in this graph between odd-degree vertices
is the combinatorial heart of the path-following proof of Scarf's lemma.
-/

@[expose] public section

attribute [local instance] Classical.propDecidable
open Finset

noncomputable section

namespace IndexedLOrder

variable {T I : Type*} [Inhabited T] [Fintype T] [Fintype I]
variable [DecidableEq T] [DecidableEq I] [IST : IndexedLOrder I T]

/-- A room/door cell, represented as the pair `(σ, C)`. -/
abbrev GiCell (T I : Type*) := Finset T × Finset I

/-- The room-type vertices of the graph `G_i`: colorful rooms and typed nearly-colorful rooms. -/
def GiRoomVertex (c : T → I) (i : I) (v : GiCell T I) : Prop :=
  IST.isColorful c v.1 v.2 ∨
    (IST.isRoom v.1 v.2 ∧ IST.isTypedNC c i v.1 v.2)

/-- The door-type vertices of the graph `G_i`: typed nearly-colorful doors. -/
def GiDoorVertex (c : T → I) (i : I) (v : GiCell T I) : Prop :=
  IST.isDoor v.1 v.2 ∧ IST.isTypedNC c i v.1 v.2

/-- Vertices of `G_i`: the relevant rooms and doors of fixed type `i`. -/
def GiVertex (c : T → I) (i : I) (v : GiCell T I) : Prop :=
  GiRoomVertex (IST := IST) c i v ∨ GiDoorVertex (IST := IST) c i v

/-- Edges of `G_i`: room-door incidence, made symmetric. -/
def GiEdge (c : T → I) (i : I) (v w : GiCell T I) : Prop :=
  (GiRoomVertex (IST := IST) c i v ∧
    GiDoorVertex (IST := IST) c i w ∧
      IST.isDoorof w.1 w.2 v.1 v.2) ∨
  (GiRoomVertex (IST := IST) c i w ∧
    GiDoorVertex (IST := IST) c i v ∧
      IST.isDoorof v.1 v.2 w.1 w.2)

omit [Inhabited T] [Fintype T] [Fintype I] in
/--
@isnad1 id=giedge.1h6v.s5.6fb0b3e6d303 from=translated src=- shape=cc9bbea4 vocab=13eb20fe
-/
lemma GiEdge.symm {c : T → I} {i : I} {v w : GiCell T I}
    (h : GiEdge (IST := IST) c i v w) :
    GiEdge (IST := IST) c i w v :=
  h.elim Or.inr Or.inl

omit [Inhabited T] [Fintype T] [Fintype I] in
/--
@isnad1 id=givertex.1h6v.s5.c700c7e4b955 from=translated src=- shape=599b866b vocab=5c8e97fe
-/
lemma GiEdge.left_vertex {c : T → I} {i : I} {v w : GiCell T I}
    (h : GiEdge (IST := IST) c i v w) :
    GiVertex (IST := IST) c i v :=
  h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2.1)

omit [Inhabited T] [Fintype T] [Fintype I] in
/--
@isnad1 id=givertex.1h6v.s5.c8e801d95650 from=translated src=- shape=1b60d73d vocab=5c8e97fe
-/
lemma GiEdge.right_vertex {c : T → I} {i : I} {v w : GiCell T I}
    (h : GiEdge (IST := IST) c i v w) :
    GiVertex (IST := IST) c i w :=
  (GiEdge.symm h).left_vertex

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
/--
@isnad1 id=isroom.1h5v.s5.33d6a7669132 from=translated src=- shape=072f2076 vocab=9b5f727a
-/
lemma GiRoomVertex.room {c : T → I} {i : I} {v : GiCell T I}
    (h : GiRoomVertex (IST := IST) c i v) :
    IST.isRoom v.1 v.2 :=
  h.elim IST.room_of_colorful (·.1)

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
/--
@isnad1 id=isdoor.1h5v.s5.61db1e854d8e from=translated src=- shape=072f2076 vocab=1d1e0fca
-/
lemma GiDoorVertex.door {c : T → I} {i : I} {v : GiCell T I}
    (h : GiDoorVertex (IST := IST) c i v) :
    IST.isDoor v.1 v.2 := h.1

omit [Inhabited T] [Fintype T] [Fintype I] in
/--
@isnad1 id=not.0h5v.s5.2c47f830f685 from=translated src=- shape=9cd75d4e vocab=13eb20fe
-/
lemma GiEdge.irrefl {c : T → I} {i : I} (v : GiCell T I) :
    ¬ GiEdge (IST := IST) c i v v := by
  intro h
  rcases h with h | h <;>
    exact absurd h.2.1.door.2 (by have := h.1.room.2; omega)

/-- The Mathlib `SimpleGraph` whose vertices and edges are the graph `G_i`. -/
def GiGraph (c : T → I) (i : I) : SimpleGraph (GiCell T I) where
  Adj := GiEdge (IST := IST) c i
  symm := ⟨fun _ _ h => GiEdge.symm h⟩
  loopless := ⟨fun v => GiEdge.irrefl (IST := IST) (c := c) (i := i) v⟩

/-- The finite neighbor set of a vertex in `G_i`. -/
def GiNeighbors (c : T → I) (i : I) (v : GiCell T I) : Finset (GiCell T I) :=
  (GiGraph (IST := IST) c i).neighborFinset v

omit [Inhabited T] in
/--
@isnad1 id=iff.0h6v.s6.e4d49c0f85a6 from=translated src=- shape=d6ffe8cb vocab=ee0f3250
-/
lemma mem_GiNeighbors {c : T → I} {i : I} {v w : GiCell T I} :
    w ∈ GiNeighbors (IST := IST) c i v ↔ GiEdge (IST := IST) c i v w := by
  exact SimpleGraph.mem_neighborFinset (GiGraph (IST := IST) c i) v w

/-- Degree in `G_i`. -/
def GiDegree (c : T → I) (i : I) (v : GiCell T I) : Nat :=
  (GiNeighbors (IST := IST) c i v).card

/-- Endpoint vertices of `G_i`. -/
def GiEndpoint (c : T → I) (i : I) (v : GiCell T I) : Prop :=
  GiVertex (IST := IST) c i v ∧ GiDegree (IST := IST) c i v = 1

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] [DecidableEq I] in
/--
@isnad1 id=not.1h4v.s4.42bb8f61d95f from=translated src=- shape=3ec442cd vocab=98e2910a
-/
lemma not_room_of_door {τ : Finset T} {D : Finset I}
    (hDoor : IST.isDoor τ D) :
    ¬ IST.isRoom τ D := by
  simp_all

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
/--
@isnad1 id=not.1h5v.s5.fb0284dfa17e from=translated src=- shape=fc7db3fc vocab=ef8ac4b1
-/
lemma not_colorful_of_door {c : T → I} {τ : Finset T} {D : Finset I}
    (hDoor : IST.isDoor τ D) :
    ¬ IST.isColorful c τ D :=
  fun hColorful => not_room_of_door hDoor (IST.room_of_colorful hColorful)

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
/--
@isnad1 id=not.1h6v.s5.86b9f9e7ee3d from=translated src=- shape=b2960574 vocab=168c8a59
-/
lemma not_GiRoomVertex_of_door {c : T → I} {i : I} {τ : Finset T} {D : Finset I}
    (hDoor : IST.isDoor τ D) :
    ¬ GiRoomVertex (IST := IST) c i (τ, D) :=
  fun hRoomVertex => hRoomVertex.elim (not_colorful_of_door hDoor)
    (fun hTypedRoom => not_room_of_door hDoor hTypedRoom.1)

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] [DecidableEq I] in
/--
@isnad1 id=not.1h4v.s4.040a4d52aed6 from=translated src=- shape=3ec442cd vocab=98e2910a
-/
lemma not_door_of_room {σ : Finset T} {C : Finset I}
    (hRoom : IST.isRoom σ C) :
    ¬ IST.isDoor σ C :=
  fun hDoor => not_room_of_door hDoor hRoom

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
/--
@isnad1 id=not.1h6v.s5.449431575449 from=translated src=- shape=b2960574 vocab=7d308f6f
-/
lemma not_GiDoorVertex_of_room {c : T → I} {i : I} {σ : Finset T} {C : Finset I}
    (hRoom : IST.isRoom σ C) :
    ¬ GiDoorVertex (IST := IST) c i (σ, C) :=
  fun hDoorVertex => not_door_of_room hRoom hDoorVertex.1

omit [Inhabited T] [Fintype T] [Fintype I] in
/--
@isnad1 id=isdoor.1h6v.s5.91640c1a3119 from=translated src=- shape=d5e56857 vocab=ddf9a62e
-/
lemma isDoor_of_Doorof {τ σ : Finset T} {D C : Finset I}
    (hDoorof : IST.isDoorof τ D σ C) :
    IST.isDoor τ D := by
  cases hDoorof with
  | idoor _ hDoor _ _ _ _ => exact hDoor
  | odoor _ hDoor _ _ _ _ => exact hDoor

omit [Inhabited T] [Fintype T] [Fintype I] in
/--
@isnad1 id=giroomve.2h8v.s6.4149d35dcad9 from=translated src=- shape=c1a83485 vocab=1f100867
-/
lemma GiRoomVertex_of_incident_typed_door {c : T → I} {i : I}
    {τ σ : Finset T} {D C : Finset I}
    (hTypedDoor : IST.isTypedNC c i τ D)
    (hDoorof : IST.isDoorof τ D σ C) :
    GiRoomVertex (IST := IST) c i (σ, C) := by
  exact (IST.NC_or_C_of_door hTypedDoor hDoorof).elim
    (fun hTypedRoom => Or.inr ⟨IST.isRoom_of_Door hDoorof, hTypedRoom⟩) Or.inl

omit [Inhabited T] in
/--
@isnad1 id=eq.2h6v.s6.08509f28f9d5 from=translated src=- shape=8e388891 vocab=fb21341a
-/
theorem GiDegree_internalDoor {c : T → I} {i : I} {τ : Finset T} {D : Finset I}
    (hInternal : IST.isInternalDoor τ D) (hTyped : IST.isTypedNC c i τ D) :
    GiDegree (IST := IST) c i (τ, D) = 2 := by
  obtain ⟨σ₁, σ₂, C₁, C₂, hNe, hRoom₁, hRoom₂, hDoor₁, hDoor₂, hUnique⟩ :=
    IST.internal_door_two_rooms τ D hInternal
  have hNeighbors :
      GiNeighbors (IST := IST) c i (τ, D) = ({(σ₁, C₁), (σ₂, C₂)} : Finset (GiCell T I)) := by
    ext w
    constructor
    · intro hw
      have hEdge : GiEdge (IST := IST) c i (τ, D) w := (mem_GiNeighbors).1 hw
      rcases hEdge with hBad | hGood
      · exact False.elim (not_GiRoomVertex_of_door hInternal.1 hBad.1)
      · obtain hCases := hUnique w.1 w.2 (IST.isRoom_of_Door hGood.2.2) hGood.2.2
        rw [Finset.mem_insert, Finset.mem_singleton]
        rcases hCases with hLeft | hRight
        · exact Or.inl (Prod.ext hLeft.1 hLeft.2)
        · exact Or.inr (Prod.ext hRight.1 hRight.2)
    · intro hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      apply (mem_GiNeighbors).2
      rcases hw with hEq | hEq
      · exact hEq ▸ Or.inr ⟨GiRoomVertex_of_incident_typed_door hTyped hDoor₁,
          ⟨hInternal.1, hTyped⟩, hDoor₁⟩
      · exact hEq ▸ Or.inr ⟨GiRoomVertex_of_incident_typed_door hTyped hDoor₂,
          ⟨hInternal.1, hTyped⟩, hDoor₂⟩
  rw [GiDegree, hNeighbors]
  exact Finset.card_pair hNe

omit [Inhabited T] in
/--
@isnad1 id=eq.2h6v.s6.3fb37515c305 from=translated src=- shape=8e388891 vocab=89da0931
-/
theorem GiDegree_typedNCRoom {c : T → I} {i : I} {σ : Finset T} {C : Finset I}
    (hRoom : IST.isRoom σ C) (hTyped : IST.isTypedNC c i σ C) :
    GiDegree (IST := IST) c i (σ, C) = 2 := by
  obtain ⟨door₁, door₂, hNe, hDoors⟩ :=
    IST.doors_of_NCroom (c := c) hRoom (IST.NC_of_TNC hTyped)
  have hNeighbors :
      GiNeighbors (IST := IST) c i (σ, C) = ({door₁, door₂} : Finset (GiCell T I)) := by
    ext w
    constructor
    · intro hw
      have hEdge : GiEdge (IST := IST) c i (σ, C) w := (mem_GiNeighbors).1 hw
      rcases hEdge with hGood | hBad
      · have hwDoor : w ∈ IST.NCdoors c σ C := by
          change IST.isNearlyColorful c w.1 w.2 ∧ IST.isDoorof w.1 w.2 σ C
          exact ⟨IST.NC_of_TNC hGood.2.1.2, hGood.2.2⟩
        simp_all
      · exact False.elim (not_GiDoorVertex_of_room hRoom hBad.2.1)
    · intro hw
      have hwDoor : w ∈ IST.NCdoors c σ C := by
        simp_all
      change IST.isNearlyColorful c w.1 w.2 ∧ IST.isDoorof w.1 w.2 σ C at hwDoor
      let hTypedDoor := IST.isTypedNC_of_isNearlyColorful_of_isDoorof_isTypedNC
        hwDoor.1 hwDoor.2 hTyped
      apply (mem_GiNeighbors).2
      exact Or.inl ⟨Or.inr ⟨hRoom, hTyped⟩,
        ⟨isDoor_of_Doorof hwDoor.2, hTypedDoor⟩,
        hwDoor.2⟩
  rw [GiDegree, hNeighbors]
  exact Finset.card_pair hNe

/--
@isnad1 id=eq.2h6v.s6.2c51ae897a72 from=translated src=- shape=f035db22 vocab=ceac3868
-/
theorem GiDegree_outsideDoor {c : T → I} {i : I} {τ : Finset T} {D : Finset I}
    (hOutside : IST.isOutsideDoor τ D) (hTyped : IST.isTypedNC c i τ D) :
    GiDegree (IST := IST) c i (τ, D) = 1 := by
  have hτ : τ = Finset.empty := hOutside.2
  have hD : D = ({i} : Finset I) := by
    have h := hTyped.2
    rw [hτ] at h
    have hImg : Finset.image c (Finset.empty : Finset T) = Finset.empty := Finset.image_empty c
    rw [hImg] at h
    have hsdiff : D \ (Finset.empty : Finset I) = D :=
      Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_empty_right D)
    rwa [hsdiff] at h
  let xMax : T := @Finset.max' T (IST i) Finset.univ
    (Finset.univ_nonempty_iff.mpr ⟨(default : T)⟩)
  let room : GiCell T I := ({xMax}, ({i} : Finset I))
  have hCellRoom : IST.isCell ({xMax} : Finset T) ({i} : Finset I) := by
    intro y
    refine ⟨i, by simp, ?_⟩
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact @Finset.le_max' T (IST i) Finset.univ y (Finset.mem_univ y)
  have hDoorofRoom : IST.isDoorof τ D ({xMax} : Finset T) ({i} : Finset I) := by
    rw [hτ, hD]
    apply isDoorof.idoor hCellRoom (IST.outsidedoor_singleton i).1 xMax
    · exact Finset.notMem_empty xMax
    · rfl
    · rfl
  have hNeighbors :
      GiNeighbors (IST := IST) c i (τ, D) = ({room} : Finset (GiCell T I)) := by
    ext w
    constructor
    · intro hw
      have hEdge : GiEdge (IST := IST) c i (τ, D) w := (mem_GiNeighbors).1 hw
      rcases hEdge with hBad | hGood
      · exact False.elim (not_GiRoomVertex_of_door hOutside.1 hBad.1)
      · have hDoorof : IST.isDoorof τ D w.1 w.2 := hGood.2.2
        have hRoomW : IST.isRoom w.1 w.2 := IST.isRoom_of_Door hDoorof
        rw [hτ, hD] at hDoorof
        cases hDoorof with
        | idoor hCell _ x _ hInsert hDEq =>
            rw [Finset.mem_singleton]
            apply Prod.ext
            · have hwσ : w.1 = ({x} : Finset T) := by
                rw [← hInsert]
                rfl
              have hxMax : x = xMax := by
                have hAbove : ∀ y : T, (IST i).le y x := by
                  intro y
                  obtain ⟨j, hj, hle⟩ := hCell y
                  have hji : j = i := by
                    rw [← hDEq] at hj
                    exact Finset.mem_singleton.mp hj
                  simp_all
                have hx_le_max : (IST i).le x xMax :=
                  @Finset.le_max' T (IST i) Finset.univ x (Finset.mem_univ x)
                have hmax_le_x : (IST i).le xMax x := hAbove xMax
                exact @le_antisymm T (IST i).toPartialOrder x xMax hx_le_max hmax_le_x
              rw [hwσ, hxMax]
            · exact hDEq.symm
        | odoor _ _ _ _ hτEq _ =>
            exfalso
            have hσEmpty : w.1 = Finset.empty := by
              simpa using hτEq.symm
            have hNonempty := IST.sigma_nonempty_of_room hRoomW
            rw [hσEmpty] at hNonempty
            exact Finset.not_nonempty_empty hNonempty
    · intro hw
      rw [Finset.mem_singleton] at hw
      rw [hw]
      apply (mem_GiNeighbors).2
      exact Or.inr ⟨GiRoomVertex_of_incident_typed_door hTyped hDoorofRoom,
        ⟨hOutside.1, hTyped⟩, hDoorofRoom⟩
  rw [GiDegree, hNeighbors]
  simp

omit [Inhabited T] in
/--
@isnad1 id=eq.1h6v.s6.41721f10bd9e from=translated src=- shape=b1527d6a vocab=6c5b2655
-/
theorem GiDegree_colorfulRoom {c : T → I} {i : I} {σ : Finset T} {C : Finset I}
    (hColorful : IST.isColorful c σ C) :
    GiDegree (IST := IST) c i (σ, C) = 1 := by
  have hRoom : IST.isRoom σ C := IST.room_of_colorful hColorful
  have hInj : Set.InjOn c (↑σ : Set T) := by
    apply (Finset.card_image_iff).mp
    rw [hColorful.2, hRoom.2]
  by_cases hiC : i ∈ C
  · have hiImage : i ∈ σ.image c := by
      rwa [hColorful.2]
    obtain ⟨x, hxσ, hcx⟩ := Finset.mem_image.mp hiImage
    let door : GiCell T I := (σ.erase x, C)
    have hxUnique : ∀ ⦃y⦄, y ∈ σ → c y = c x → y = x := by
      intro y hy hcy
      exact hInj hy hxσ hcy
    have hDoorof : IST.isDoorof (σ.erase x) C σ C :=
      IST.collision_door_valid σ C c x hColorful.1 hxσ hRoom.2
    have hTypedDoor : IST.isTypedNC c i (σ.erase x) C := by
      constructor
      · exact IST.Dominant_of_subset σ (σ.erase x) C (Finset.erase_subset x σ) hColorful.1
      · have hImgErase :
            (σ.erase x).image c = (σ.image c).erase (c x) :=
          image_erase_eq_erase_image_of_unique σ c hxσ hxUnique
        rw [hImgErase, ← hColorful.2, hcx]
        ext j
        constructor
        · intro hj
          rcases Finset.mem_sdiff.mp hj with ⟨hjC, hjNotErase⟩
          simp_all
        · simp_all
    have hNeighbors :
        GiNeighbors (IST := IST) c i (σ, C) = ({door} : Finset (GiCell T I)) := by
      ext w
      constructor
      · intro hw
        have hEdge : GiEdge (IST := IST) c i (σ, C) w := (mem_GiNeighbors).1 hw
        rcases hEdge with hGood | hBad
        · have hDoorofW : IST.isDoorof w.1 w.2 σ C := hGood.2.2
          have hTypedW : IST.isTypedNC c i w.1 w.2 := hGood.2.1.2
          cases hDoorofW with
          | idoor _ _ y hyNot hInsert hDEq =>
              have hyσ : y ∈ σ := by
                rw [← hInsert]
                exact Finset.mem_insert_self y w.1
              have hwσ : w.1 = σ.erase y := by
                rw [← Finset.erase_insert hyNot, hInsert]
              have hcyNotErase : c y ∉ (σ.erase y).image c := by
                intro hmem
                rcases Finset.mem_image.mp hmem with ⟨z, hzErase, hcz⟩
                have hzσ : z ∈ σ := Finset.erase_subset y σ hzErase
                have hzEq : z = y := hInj hzσ hyσ hcz
                exact (Finset.mem_erase.mp hzErase).1 hzEq
              have hcyDiff : c y ∈ w.2 \ w.1.image c := by
                rw [hDEq, hwσ]
                exact Finset.mem_sdiff.mpr
                  ⟨by rw [← hColorful.2]; exact Finset.mem_image_of_mem c hyσ, hcyNotErase⟩
              have hcyi : c y = i := by
                rw [hTypedW.2] at hcyDiff
                exact Finset.mem_singleton.mp hcyDiff
              have hyx : y = x := hInj hyσ hxσ (hcyi.trans hcx.symm)
              rw [Finset.mem_singleton]
              apply Prod.ext
              · rw [hwσ, hyx]
              · exact hDEq
          | odoor _ _ j _ hτEq _ =>
              exfalso
              have hiDiff : i ∈ w.2 \ w.1.image c := by
                rw [hTypedW.2]
                simp
              simp_all
        · exact False.elim (not_GiDoorVertex_of_room hRoom hBad.2.1)
      · intro hw
        rw [Finset.mem_singleton] at hw
        rw [hw]
        apply (mem_GiNeighbors).2
        exact Or.inl ⟨Or.inl hColorful, ⟨isDoor_of_Doorof hDoorof, hTypedDoor⟩, hDoorof⟩
    rw [GiDegree, hNeighbors]
    simp
  · let door : GiCell T I := (σ, insert i C)
    have hDoor : IST.isDoor σ (insert i C) := by
      constructor
      · exact IST.Dominant_of_supset σ C (insert i C) (Finset.subset_insert i C) hColorful.1
      · rw [Finset.card_insert_of_notMem hiC, hRoom.2]
    have hDoorof : IST.isDoorof σ (insert i C) σ C :=
      isDoorof.odoor hColorful.1 hDoor i hiC rfl rfl
    have hTypedDoor : IST.isTypedNC c i σ (insert i C) := by
      constructor
      · exact hDoor.1
      · rw [← hColorful.2]
        ext j
        constructor
        · intro hj
          rcases Finset.mem_sdiff.mp hj with ⟨hjInsert, hjNotImage⟩
          simp_all
        · intro hj
          have hji : j = i := Finset.mem_singleton.mp hj
          rw [hji]
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_insert_self i (σ.image c), by
              rwa [hColorful.2]⟩
    have hNeighbors :
        GiNeighbors (IST := IST) c i (σ, C) = ({door} : Finset (GiCell T I)) := by
      ext w
      constructor
      · intro hw
        have hEdge : GiEdge (IST := IST) c i (σ, C) w := (mem_GiNeighbors).1 hw
        rcases hEdge with hGood | hBad
        · have hDoorofW : IST.isDoorof w.1 w.2 σ C := hGood.2.2
          have hTypedW : IST.isTypedNC c i w.1 w.2 := hGood.2.1.2
          cases hDoorofW with
          | idoor _ _ y _ _ hDEq =>
              exfalso
              have hiDiff : i ∈ w.2 \ w.1.image c := by
                rw [hTypedW.2]
                simp
              simp_all
          | odoor _ _ j hjNotC hτEq hDEq =>
              have hjDiff : j ∈ w.2 \ w.1.image c := by
                rw [hDEq, hτEq]
                exact Finset.mem_sdiff.mpr
                  ⟨Finset.mem_insert_self j C, by
                    rw [hColorful.2]
                    exact hjNotC⟩
              have hji : j = i := by
                rw [hTypedW.2] at hjDiff
                exact Finset.mem_singleton.mp hjDiff
              rw [Finset.mem_singleton]
              apply Prod.ext
              · exact hτEq
              · rw [hDEq, hji]
        · exact False.elim (not_GiDoorVertex_of_room hRoom hBad.2.1)
      · intro hw
        rw [Finset.mem_singleton] at hw
        rw [hw]
        apply (mem_GiNeighbors).2
        exact Or.inl ⟨Or.inl hColorful, ⟨hDoor, hTypedDoor⟩, hDoorof⟩
    rw [GiDegree, hNeighbors]
    simp

/-- A graph has degree at most two at each vertex. -/
def simpleGraphDegreeAtMostTwo {α : Type*} [Fintype α] (G : SimpleGraph α) : Prop :=
  ∀ v, G.degree v ≤ 2

/-- A connected component is represented by a Mathlib graph path. -/
def simpleGraphPathComponent {α : Type*}
    (G : SimpleGraph α) (component : G.ConnectedComponent) : Prop :=
  ∃ (u v : α) (p : G.Walk u v),
    p.IsPath ∧ {x : α | x ∈ p.support} = component.supp

/-- A connected component is represented by a Mathlib graph cycle. -/
def simpleGraphCycleComponent {α : Type*}
    (G : SimpleGraph α) (component : G.ConnectedComponent) : Prop :=
  ∃ (u : α) (p : G.Walk u u),
    p.IsCycle ∧ {x : α | x ∈ p.support} = component.supp

/-- The literal "disjoint paths and cycles" component statement for a finite `SimpleGraph`. -/
def simpleGraphComponentsArePathsOrCycles {α : Type*}
    (G : SimpleGraph α) : Prop :=
  ∀ component : G.ConnectedComponent,
    simpleGraphPathComponent G component ∨ simpleGraphCycleComponent G component

/--
The degree characterization of `G_i`: every vertex has degree one or two, and
the degree-one vertices are exactly the unique outside door of type `i` and
the colorful rooms.
-/
def GiDegreeCharacterization (c : T → I) (i : I) : Prop :=
  (∀ v, GiVertex (IST := IST) c i v →
    GiDegree (IST := IST) c i v = 1 ∨ GiDegree (IST := IST) c i v = 2) ∧
  (∀ v, GiEndpoint (IST := IST) c i v ↔
    (GiDoorVertex (IST := IST) c i v ∧ IST.isOutsideDoor v.1 v.2) ∨
      IST.isColorful c v.1 v.2)

/--
@isnad1 id=gidegree.0h4v.s5.f03171e7a507 from=translated src=- shape=833f8465 vocab=7e1cf948
-/
theorem GiDegreeCharacterization_holds (c : T → I) (i : I) :
    GiDegreeCharacterization (IST := IST) c i := by
  constructor
  · intro v hv
    rcases hv with hRoomVertex | hDoorVertex
    · rcases hRoomVertex with hColorful | hTypedRoom
      · exact Or.inl (GiDegree_colorfulRoom (IST := IST) (i := i) hColorful)
      · exact Or.inr (GiDegree_typedNCRoom (IST := IST) hTypedRoom.1 hTypedRoom.2)
    · by_cases hNonempty : v.1.Nonempty
      · exact Or.inr (GiDegree_internalDoor (IST := IST) ⟨hDoorVertex.1, hNonempty⟩ hDoorVertex.2)
      · have hOutside : IST.isOutsideDoor v.1 v.2 :=
          ⟨hDoorVertex.1, Finset.not_nonempty_iff_eq_empty.mp hNonempty⟩
        exact Or.inl (GiDegree_outsideDoor (IST := IST) hOutside hDoorVertex.2)
  · intro v
    constructor
    · intro hend
      rcases hend with ⟨hv, hDegreeOne⟩
      rcases hv with hRoomVertex | hDoorVertex
      · rcases hRoomVertex with hColorful | hTypedRoom
        · exact Or.inr hColorful
        · have hDegreeTwo := GiDegree_typedNCRoom (IST := IST) hTypedRoom.1 hTypedRoom.2
          rw [hDegreeOne] at hDegreeTwo; norm_num at hDegreeTwo
      · by_cases hNonempty : v.1.Nonempty
        · have hDegreeTwo := GiDegree_internalDoor (IST := IST) ⟨hDoorVertex.1,
          hNonempty⟩ hDoorVertex.2
          rw [hDegreeOne] at hDegreeTwo; norm_num at hDegreeTwo
        · have hOutside : IST.isOutsideDoor v.1 v.2 :=
            ⟨hDoorVertex.1, Finset.not_nonempty_iff_eq_empty.mp hNonempty⟩
          exact Or.inl ⟨hDoorVertex, hOutside⟩
    · intro hEndpointKind
      rcases hEndpointKind with hOutsideDoor | hColorful
      · exact ⟨Or.inr hOutsideDoor.1,
          GiDegree_outsideDoor (IST := IST) hOutsideDoor.2 hOutsideDoor.1.2⟩
      · exact ⟨Or.inl (Or.inl hColorful),
          GiDegree_colorfulRoom (IST := IST) (i := i) hColorful⟩

/--
The path-structure target for `G_i`: degree characterization plus the local
degree-at-most-two property used by path-following.
-/
def GiPathStructure (c : T → I) (i : I) : Prop :=
  GiDegreeCharacterization (IST := IST) c i ∧
    simpleGraphDegreeAtMostTwo (GiGraph (IST := IST) c i)

/--
The faithful component-level target for `G_i`: its connected components are
paths or cycles, and the endpoints of path components are exactly colorful
rooms except for the unique outside door of type `i`.
-/
def GiComponentStructure (c : T → I) (i : I) : Prop :=
  simpleGraphComponentsArePathsOrCycles (GiGraph (IST := IST) c i) ∧
    (∀ v, GiEndpoint (IST := IST) c i v ↔
      (GiDoorVertex (IST := IST) c i v ∧ IST.isOutsideDoor v.1 v.2) ∨
        IST.isColorful c v.1 v.2)

omit [Inhabited T] in
/--
@isnad1 id=gipathst.1h4v.s5.9258bbb4db48 from=translated src=- shape=dad3e45f vocab=56e1093e
-/
theorem GiPathStructure_of_degreeCharacterization {c : T → I} {i : I}
    (hdegStmt : GiDegreeCharacterization (IST := IST) c i) :
    GiPathStructure (IST := IST) c i := by
  refine ⟨hdegStmt, ?_⟩
  intro v
  rw [SimpleGraph.degree]
  change GiDegree (IST := IST) c i v ≤ 2
  by_cases hv : GiVertex (IST := IST) c i v
  · rcases hdegStmt.1 v hv with hOne | hTwo <;> omega
  · have hNoNeighbors : GiNeighbors (IST := IST) c i v = ∅ := by
      ext w
      simpa only [Finset.notMem_empty, iff_false]
        using fun hw => hv (GiEdge.left_vertex ((mem_GiNeighbors).1 hw))
    rw [GiDegree, hNoNeighbors]
    simp

omit [Inhabited T] in
/--
@isnad1 id=gicompon.2h4v.s5.413603fb339f from=translated src=- shape=d6c27cf3 vocab=11f9f3ac
-/
theorem GiComponentStructure_of_components_are_paths_or_cycles {c : T → I} {i : I}
    (hdegStmt : GiDegreeCharacterization (IST := IST) c i)
    (hcomponents :
      simpleGraphComponentsArePathsOrCycles (GiGraph (IST := IST) c i)) :
    GiComponentStructure (IST := IST) c i :=
  ⟨hcomponents, hdegStmt.2⟩

/--
Generic graph-theoretic step 1: in a finite connected component of a graph of
degree at most two, choose a path whose support is maximal inside that
component.
@isnad1 id=ex.1h3v.s7.c9127d966ff8 from=translated src=- shape=0eae32e2 vocab=48db46a0
-/
theorem exists_maximal_component_path_of_degree_le_two
    {α : Type*} [Fintype α] (G : SimpleGraph α)
    (_hdeg : simpleGraphDegreeAtMostTwo G) (component : G.ConnectedComponent) :
    ∃ (u v : α) (p : G.Walk u v),
      p.IsPath ∧
        {x : α | x ∈ p.support} ⊆ component.supp ∧
        ∀ (u' v' : α) (p' : G.Walk u' v'),
          p'.IsPath →
            {x : α | x ∈ p'.support} ⊆ component.supp →
              p'.length ≤ p.length := by
  classical
  let lengths : Set ℕ :=
    {n | ∃ (u v : α) (p : G.Walk u v),
      p.IsPath ∧ {x : α | x ∈ p.support} ⊆ component.supp ∧ p.length = n}
  have hfinite : lengths.Finite := by
    apply Set.Finite.subset (Set.finite_le_nat (Fintype.card α))
    intro n hn
    rcases hn with ⟨u, v, p, hp, _hsub, rfl⟩
    exact Nat.le_of_lt (SimpleGraph.Walk.IsPath.length_lt hp)
  obtain ⟨x, hxcomp⟩ := component.nonempty_supp
  have hnonempty : (0 : ℕ) ∈ lengths := by
    refine ⟨x, x, SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, ?_, rfl⟩
    simp_all
  obtain ⟨n, ⟨hn_mem, hn_max⟩⟩ := hfinite.exists_maximal ⟨0, hnonempty⟩
  rcases hn_mem with ⟨u, v, p, hp, hp_sub, hp_len⟩
  refine ⟨u, v, p, hp, hp_sub, ?_⟩
  intro u' v' p' hp' hp'_sub
  have hp'_len_mem : p'.length ∈ lengths :=
    ⟨u', v', p', hp', hp'_sub, rfl⟩
  have := hn_max hp'_len_mem
  omega

/--
Generic graph-theoretic step 2b: if a component path has no edge escaping its
support inside the component, then its support is the whole component.
@isnad1 id=eq.2h6v.s6.c5270600e392 from=translated src=- shape=3a51d74c vocab=8dc2a986
-/
theorem component_path_support_eq_component_of_no_escape
    {α : Type*} (G : SimpleGraph α)
    {component : G.ConnectedComponent} {u v : α} {p : G.Walk u v}
    (hp_sub : {x : α | x ∈ p.support} ⊆ component.supp)
    (hend :
      ∀ ⦃x y : α⦄,
        x ∈ p.support →
          G.Adj x y →
            y ∈ component.supp →
              y ∈ p.support) :
    {x : α | x ∈ p.support} = component.supp := by
  ext z
  constructor
  · intro hz
    exact hp_sub hz
  · intro hzcomp
    by_contra hzNot
    have huSupport : u ∈ p.support := p.start_mem_support
    have hucomp : u ∈ component.supp := hp_sub huSupport
    have hReach : G.Reachable u z := by
      apply SimpleGraph.ConnectedComponent.exact
      simp_all
    rcases hReach with ⟨q⟩
    obtain ⟨d, hdq, hdfst, hdsnd⟩ :=
      q.exists_boundary_dart {x : α | x ∈ p.support} huSupport hzNot
    have hdfstComp : d.fst ∈ component.supp := hp_sub hdfst
    have hdsndComp : d.snd ∈ component.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_congr_adj component d.adj).1 hdfstComp
    exact hdsnd (hend hdfst d.adj hdsndComp)

/- Generic graph-theoretic step 3: if a maximal component path in a degree-at-most
two graph has a closing edge not already used by the path, then the component
is a cycle.  The extra edge condition excludes the two-vertex path case. -/
/--
@isnad1 id=simplegr.4h6v.s6.d85d42180ced from=translated src=- shape=42f528d0 vocab=9105a991
-/
theorem component_cycle_of_maximal_path_closes
    {α : Type*} (G : SimpleGraph α)
    {component : G.ConnectedComponent} {u v : α} {p : G.Walk u v}
    (hp : p.IsPath)
    (hsupp : {x : α | x ∈ p.support} = component.supp)
    (hclose : G.Adj v u)
    (hnew : s(v, u) ∉ p.edges) :
    simpleGraphCycleComponent G component := by
  refine ⟨v, SimpleGraph.Walk.cons hclose p, ?_, ?_⟩
  · exact (SimpleGraph.Walk.cons_isCycle_iff p hclose).2 ⟨hp, hnew⟩
  · rw [← hsupp]
    ext x
    constructor
    · intro hx
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons, Set.mem_ofPred_eq] at hx
      rcases hx with rfl | hx
      · exact p.end_mem_support
      · exact hx
    · intro hx
      simpa only [SimpleGraph.Walk.support_cons, List.mem_cons, Set.mem_ofPred_eq] using Or.inr hx

/-- A path whose support is exactly a component represents that component as a path.
@isnad1 id=simplegr.2h6v.s5.1a1ef3cdb41e from=translated src=- shape=0b0608e3 vocab=42ce5502
-/
theorem component_path_of_support_eq_component
    {α : Type*} (G : SimpleGraph α)
    {component : G.ConnectedComponent} {u v : α} {p : G.Walk u v}
    (hp : p.IsPath)
    (hsupp : {x : α | x ∈ p.support} = component.supp) :
    simpleGraphPathComponent G component :=
  ⟨u, v, p, hp, hsupp⟩

end IndexedLOrder

end

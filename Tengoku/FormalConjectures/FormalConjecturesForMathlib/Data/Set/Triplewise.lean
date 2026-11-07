/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Tengoku

@[expose] public section

def Triplewise {α : Type*} (r : α → α → α → Prop) : Prop :=
  ∀ ⦃i j k ⦄, i ≠ j → j ≠ k → i ≠ k → r i j k

namespace Set

variable {α : Type*} {r : α → α → α → Prop} {s t : Set α} {x y z : α}

/--
The ternary relation `r` holds triplewise on the set `s`
if `r x y z` for all *distinct* `x y z ∈ s`.-/
protected def Triplewise (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

/--
@isnad1 id=or.5h6v.s6.93b8264d718a from=translated src=- shape=880d62a1 vocab=2544a171
-/
protected theorem Triplewise.eq (hs : s.Triplewise r)
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (h : ¬r x y z) :
    x = y ∨ y = z ∨ x = z := by
  have := (h <| hs hx hy hz · · ·)
  tauto

/--
@isnad1 id=triplewi.2h4v.s5.9f17d72875fa from=translated src=- shape=f1c4afa0 vocab=fbf01e7d
-/
theorem Triplewise.mono (h : t ⊆ s) (hs : s.Triplewise r) :
    t.Triplewise r :=
  fun _ hx _ hy _ hz hxy hyz hxz ↦ hs (h hx) (h hy) (h hz) hxy hyz hxz

/--
@isnad1 id=iff.0h2v.s4.84e21cf35a5f from=translated src=- shape=db07d69a vocab=87fec90f
-/
@[simp]
theorem Triplewise_univ_iff :
    Set.univ.Triplewise r ↔ Triplewise r := by
  simp [Set.Triplewise, Triplewise]

/--
@isnad1 id=triplewi.1h3v.s5.7dcf4669f338 from=translated src=- shape=b82c6b2b vocab=bac9edf3
-/
theorem triplewise_of_encard_lt (r : α → α → α → Prop)
    (h : s.encard < 3) : s.Triplewise r := by
  unfold Set.Triplewise
  contrapose! h
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, _⟩ := h
  trans encard {x, y, z}
  · simp [Set.encard_insert_of_notMem, *]
    norm_num
  · exact encard_le_encard_of_injOn (by simp [MapsTo, hx, hy, hz]) (injOn_id _)

/--
@isnad1 id=triplewi.0h2v.s4.ca03287ace18 from=translated src=- shape=4d5d959d vocab=f98e81a2
-/
@[simp]
theorem triplewise_empty (r : α → α → α → Prop) :
    Set.Triplewise ∅ r :=
  (notMem_empty · · |>.elim)

/--
@isnad1 id=triplewi.0h3v.s4.a5c541d48771 from=translated src=- shape=06018960 vocab=2d21262e
-/
@[simp]
theorem triplewise_singleton (r : α → α → α → Prop) :
    Set.Triplewise {x} r := by
  apply triplewise_of_encard_lt
  simp

/--
@isnad1 id=triplewi.0h4v.s4.593e543c0484 from=translated src=- shape=d4a7a649 vocab=91afd1cf
-/
@[simp]
theorem triplewise_pair
    (r : α → α → α → Prop) : Set.Triplewise {x, y} r := by
  apply triplewise_of_encard_lt
  apply (encard_insert_le {y} x).trans_lt
  simp
  norm_num

/--
@isnad1 id=iff.0h4v.s6.a4ab216ec509 from=translated src=- shape=aa317b5d vocab=f57af19e
-/
theorem triplewise_insert :
    (insert x s).Triplewise r ↔ s.Triplewise r ∧
    ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z → r x y z ∧ r y x z ∧ r y z x := by
  refine ⟨fun hxs ↦ ?_, fun ⟨hs, hxs⟩ ↦ ?_⟩
  · refine ⟨hxs.mono (subset_insert x s), fun y hy z hz hxy hxz hyz ↦ ⟨?_, ?_, ?_⟩⟩
    · exact hxs (mem_insert x s) (mem_insert_of_mem x hy) (mem_insert_of_mem x hz) hxy hyz hxz
    · exact hxs (mem_insert_of_mem x hy) (mem_insert x s) (mem_insert_of_mem x hz) hxy.symm hxz hyz
    · exact hxs (mem_insert_of_mem x hy) (mem_insert_of_mem x hz)
        (mem_insert x s) hyz hxz.symm hxy.symm
  · intro w hw y hy z hz hwy hyz hwz
    rw [mem_insert_iff] at hw hy hz
    obtain rfl | hw := hw
    · refine (hxs y ?_ z ?_ hwy hwz hyz).1
      · simpa [hwy.symm] using hy
      · simpa [hwz.symm] using hz
    obtain rfl | hy := hy
    · exact (hxs w hw z (by simpa [hyz.symm] using hz) hwy.symm hyz hwz).2.1
    obtain rfl | hz := hz
    · exact (hxs w hw y hy hwz.symm hyz.symm hwy).2.2
    exact hs hw hy hz hwy hyz hwz

/--
@isnad1 id=iff.1h4v.s6.00f8231a8259 from=translated src=- shape=83ef7ecd vocab=f57af19e
-/
theorem triplewise_insert_of_not_mem (hx : x ∉ s) :
    (insert x s).Triplewise r ↔ s.Triplewise r ∧
    ∀ y ∈ s, ∀ z ∈ s, y ≠ z → r x y z ∧ r y x z ∧ r y z x := by
  refine Set.triplewise_insert.trans <| and_congr_right' <| forall₄_congr ?_
  intro y hy z hz
  simp [(ne_of_mem_of_not_mem hy hx).symm, (ne_of_mem_of_not_mem hz hx).symm]

/--
@isnad1 id=triplewi.2h4v.s6.430de96d88d7 from=translated src=- shape=9755d977 vocab=f57af19e
-/
protected theorem Triplewise.insert (hs : s.Triplewise r)
    (h : ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z → r x y z ∧ r y x z ∧ r y z x) :
    (insert x s).Triplewise r :=
  Set.triplewise_insert.mpr ⟨hs, h⟩

/--
@isnad1 id=triplewi.3h4v.s6.7a39ac15d90a from=translated src=- shape=7028614d vocab=f57af19e
-/
protected theorem Triplewise.insert_of_not_mem
    (hx : x ∉ s) (hs : s.Triplewise r)
    (h : ∀ y ∈ s, ∀ z ∈ s, y ≠ z → r x y z ∧ r y x z ∧ r y z x) :
    (insert x s).Triplewise r :=
  (Set.triplewise_insert_of_not_mem hx).mpr ⟨hs, h⟩

/--
@isnad1 id=iff.0h3v.s6.de9908bde31e from=translated src=- shape=c6f48fc7 vocab=06b0e373
-/
theorem triplewise_set_pred_iff {S : Set α} {P : Set α → Prop} :
    S.Triplewise (P {·, ·, ·}) ↔ ∀ T ⊆ S, T.ncard = 3 → P T := by
  constructor
  · intro h T hT T_ncard
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := ncard_eq_three.mp T_ncard
    simp_rw [insert_subset_iff, singleton_subset_iff] at hT
    exact h hT.1 hT.2.1 hT.2.2 hxy hyz hxz
  · intro h x hx y hy z hz hxy hyz hxz
    refine h _ ?_ (ncard_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩)
    simp [insert_subset_iff, hx, hy, hz]

end Set

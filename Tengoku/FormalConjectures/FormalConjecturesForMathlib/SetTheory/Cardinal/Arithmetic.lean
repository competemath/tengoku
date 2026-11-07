/-
Copyright 2026 The Formal Conjectures Authors.

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

namespace Cardinal
variable {α : Type*} {s t : Set α}

/--
@isnad1 id=iff.0h2v.s4.d252df17d40f from=translated src=- shape=675d2770 vocab=06588081
-/
@[simp] lemma aleph0_le_mk_set : ℵ₀ ≤ #s ↔ s.Infinite := by
  rw [aleph0_le_mk_iff, Set.infinite_coe_iff]

/--
@isnad1 id=eq.2h3v.s5.fee6cd2d0658 from=translated src=- shape=7ec38a9e vocab=65b9dc31
-/
@[simp]
lemma mk_sdiff_eq_left' (hs : s.Infinite) (hst : #↑(s ∩ t) < #s) : #↑(s \ t) = #s := by
  refine (mk_le_mk_of_subset Set.sdiff_subset).eq_of_not_lt
    fun h ↦ (add_lt_of_lt (by simpa) hst h).not_ge ?_
  grw [← mk_union_le .., Set.inter_union_sdiff]

/--
@isnad1 id=eq.2h3v.s5.981eda2d5ca7 from=translated src=- shape=1cd06c50 vocab=a49e3110
-/
@[simp]
lemma mk_sdiff_eq_left (hs : s.Infinite) (hts : #t < #s) : #↑(s \ t) = #s :=
  mk_sdiff_eq_left' hs <| hts.trans_le' <| mk_subtype_mono Set.inter_subset_right

/--
@isnad1 id=eq.2h3v.s5.e107b18b96e6 from=translated src=- shape=d05be088 vocab=4b1d7a9f
-/
@[simp]
lemma mk_sdiff_eq_left_of_finite' (hs : s.Infinite) (hst : (s ∩ t).Finite) : #↑(s \ t) = #s :=
  mk_sdiff_eq_left' hs <| (aleph0_le_mk_set.2 hs).trans_lt' <| by simpa

/--
@isnad1 id=eq.2h3v.s5.c38b2bba9efa from=translated src=- shape=2a142458 vocab=4383e53d
-/
@[simp]
lemma mk_sdiff_eq_left_of_finite (hs : s.Infinite) (ht : t.Finite) : #↑(s \ t) = #s :=
  mk_sdiff_eq_left hs <| (aleph0_le_mk_set.2 hs).trans_lt' <| by simpa

end Cardinal

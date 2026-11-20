/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Tengoku.Seed.Order.PFilter
import Tengoku.Forcing.Forcing.Order.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Forcing filters and family-relative genericity

Mathlib's `Order.PFilter` is exactly the forcing-filter notion under the smaller-is-stronger
convention: nonempty, closed under weakening (`Order.PFilter.mem_of_le`), and any two members have
a common strengthening inside the filter (`Order.PFilter.directed`). This file adds the forcing
vocabulary on top: what it means for a filter to *meet* a set of conditions, and for a filter to
be *generic for* a supplied family of sets.

Genericity here is family-relative and purely order-theoretic. Genericity over a ground model
(`GenericOver`) is deliberately not defined in the kernel; it arrives with the model layer.

## Main definitions

* `Forcing.Meets G D`: the filter `G` intersects the set of conditions `D`.
* `Forcing.GenericFor 𝒟 G`: `G` meets every member of the family `𝒟`.

## Main results

* `Forcing.exists_mem_le_le`: any two members of a filter have a common strengthening in the
  filter; hence `Forcing.compatible_of_mem` — members of a filter are pairwise compatible.
* `Forcing.meets_lowerClosure`: a filter meets a set iff it meets its downward closure.
* `Forcing.Meets.exists_mem_le`: a filter meeting a downward-closed set contains a member of it
  strengthening any given member of the filter (the localization lemma).
* `Forcing.genericFor_principal_bot`: a trivial-forcing sanity check. With smaller-is-stronger,
  `⊥` is a *strongest* condition, so the principal filter at `⊥` is all of `P`
  (`Forcing.coe_principal_bot`) and trivially meets every dense set.
-/

namespace Forcing

open Order

variable {P : Type*} [Preorder P] {G : PFilter P} {D D' : Set P} {𝒟 𝒟' : Set (Set P)} {p q : P}

/-- A filter *meets* a set of conditions if they intersect.-/
def Meets (G : PFilter P) (D : Set P) : Prop :=
  ((G : Set P) ∩ D).Nonempty

/-- A filter is *generic for* a family of sets of conditions if it meets every member of the
family.-/
def GenericFor (𝒟 : Set (Set P)) (G : PFilter P) : Prop :=
  ∀ D ∈ 𝒟, Meets G D

/--
@isnad1 id=iff.0h3v.s5.5e3833dc2822 from=translated src=- shape=8da4ea99 vocab=735cac0f
-/
theorem meets_iff_exists : Meets G D ↔ ∃ p ∈ G, p ∈ D :=
  .rfl

/--
@isnad1 id=ex.1h3v.s5.8a74014cb248 from=translated src=- shape=d3081d42 vocab=735cac0f
-/
theorem Meets.exists_mem (h : Meets G D) : ∃ p ∈ G, p ∈ D :=
  h

/-- Any two members of a filter have a common strengthening inside the filter.
@isnad1 id=ex.2h4v.s6.29a986d8e799 from=translated src=- shape=2c057c39 vocab=08d29df6
-/
theorem exists_mem_le_le (hp : p ∈ G) (hq : q ∈ G) : ∃ r ∈ G, r ≤ p ∧ r ≤ q := by
  obtain ⟨r, hrG, hrp, hrq⟩ := G.directed p hp q hq
  exact ⟨r, hrG, hrp, hrq⟩

/-- Members of a filter are pairwise compatible.
@isnad1 id=compatib.2h4v.s5.8b8d64fcb061 from=translated src=- shape=eff8c1d7 vocab=3460b1eb
-/
theorem compatible_of_mem (hp : p ∈ G) (hq : q ∈ G) : Compatible p q :=
  let ⟨r, _, hrp, hrq⟩ := exists_mem_le_le hp hq
  ⟨r, hrp, hrq⟩

/--
@isnad1 id=meets.2h4v.s5.d393a4606397 from=translated src=- shape=c3d02c23 vocab=45f326a4
-/
theorem Meets.mono (h : Meets G D) (hDD' : D ⊆ D') : Meets G D' :=
  let ⟨p, hpG, hpD⟩ := h
  ⟨p, hpG, hDD' hpD⟩

/--
@isnad1 id=meets.2h4v.s5.1f59938294f2 from=translated src=- shape=36ad73a2 vocab=45f326a4
-/
theorem Meets.mono_filter {G' : PFilter P} (h : Meets G D) (hGG' : G ≤ G') : Meets G' D :=
  let ⟨p, hpG, hpD⟩ := h
  ⟨p, hGG' hpG, hpD⟩

/-- Genericity is antitone in the family: generic for a family, generic for any subfamily.
@isnad1 id=genericf.2h4v.s5.47b3a27af4f1 from=translated src=- shape=1a95cf1c vocab=7bd72a7b
-/
theorem GenericFor.anti (h : GenericFor 𝒟 G) (h𝒟 : 𝒟' ⊆ 𝒟) : GenericFor 𝒟' G :=
  fun D hD ↦ h D (h𝒟 hD)

/-- A filter meets a set iff it meets its downward closure.
@isnad1 id=iff.0h3v.s5.b35d7bde80e7 from=translated src=- shape=060fcc6b vocab=11711285
-/
theorem meets_lowerClosure : Meets G (↑(lowerClosure D) : Set P) ↔ Meets G D := by
  constructor
  · rintro ⟨g, hgG, hgLC⟩
    obtain ⟨d, hdD, hgd⟩ := mem_lowerClosure.1 hgLC
    exact ⟨d, PFilter.mem_of_le hgd hgG, hdD⟩
  · exact fun h ↦ h.mono subset_lowerClosure

/-- Localization: a filter meeting a downward-closed set contains a member of that set
strengthening any given member of the filter.
@isnad1 id=ex.3h4v.s6.e3719b204289 from=translated src=- shape=88451bd7 vocab=75399df7
-/
theorem Meets.exists_mem_le (h : Meets G D) (hD : IsLowerSet D) (hp : p ∈ G) :
    ∃ q ∈ G, q ∈ D ∧ q ≤ p := by
  obtain ⟨g, hgG, hgD⟩ := h
  obtain ⟨r, hrG, hrg, hrp⟩ := exists_mem_le_le hgG hp
  exact ⟨r, hrG, hD hrg hgD, hrp⟩

/--
@isnad1 id=iff.0h3v.s5.cb66a2e23ccc from=translated src=- shape=96a25e20 vocab=3982d9e1
-/
@[simp] theorem meets_principal {x : P} : Meets (PFilter.principal x) D ↔ ∃ q ∈ D, x ≤ q := by
  constructor
  · rintro ⟨q, hqx, hqD⟩
    exact ⟨q, hqD, PFilter.mem_principal.1 hqx⟩
  · rintro ⟨q, hqD, hxq⟩
    exact ⟨q, PFilter.mem_principal.2 hxq, hqD⟩

/-- With a strongest condition `⊥`, the principal filter at `⊥` is all of `P`.
@isnad1 id=eq.0h1v.s5.e5b256c89035 from=translated src=- shape=eadc16ff vocab=9e663ebb
-/
@[simp] theorem coe_principal_bot [OrderBot P] :
    (PFilter.principal (⊥ : P) : Set P) = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ PFilter.mem_principal.2 bot_le

/-- Trivial-forcing sanity check: with a strongest condition `⊥`, the principal filter at `⊥` is
all of `P`, so it is generic for every family of dense sets.
@isnad1 id=genericf.1h2v.s5.c10805a2b15d from=translated src=- shape=d5d64d66 vocab=c4591bda
-/
theorem genericFor_principal_bot [OrderBot P] (h : ∀ D ∈ 𝒟, IsDense D) :
    GenericFor 𝒟 (PFilter.principal (⊥ : P)) := by
  intro D hD
  obtain ⟨q, hqD, -⟩ := h D hD ⊥
  exact meets_principal.2 ⟨q, hqD, bot_le⟩

/-!
### Sanity examples

`ℤ` has no strongest condition, and the strictly negative integers are dense; the principal
filter at `0` fails to meet them, so principal filters are not generic in general. Contrast with
`genericFor_principal_bot`.
-/

end Forcing

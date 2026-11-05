/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Seed.RingTheory.RegularLocalRing.Defs
import Tengoku.Hironaka.Hironaka.Algebra.Local.RegularSystem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quotients by an arbitrary subset of a regular system of parameters

[Kol07, Definition 24 (4)] cuts `Z` out by an unordered subset `z_{j_1}, …, z_{j_s}` of the local
coordinates; the quotient lemmas of `Hironaka.Algebra.Local.RegularSystem` are stated for the
initial segments `x_0, …, x_{i-1}`. This module moves a `Finset s` of coordinates to the front
through the enumeration of `Fin n` by `s` and then `sᶜ` (`finsetEquiv`) and transports those lemmas:

* `R ⧸ (z_l : l ∈ s)` is a regular local ring of dimension `n − |s|`
  (`isRegularLocalRing_quotient_span_image_finset`, `ringKrullDim_quotient_span_image_finset`);
* a coordinate `z_j`, `j ∉ s`, lies neither in `(z_l : l ∈ s)` nor in `𝔪² + (z_l : l ∈ s)`: the
  classes of the coordinates form a basis of `𝔪/𝔪²`, so `z_j` cannot be a combination of the others
  modulo `𝔪²` (`notMem_sq_sup_span_image`, `mem_span_image_iff`).

`Hironaka.Scheme.Snc.HasSncWith` sees the quotient through the surjection `𝒪_{X,x} → 𝒪_{Z,w}` with
kernel `I_{Z,x} = (z_l : l ∈ s)`, so the last section restates everything for a surjective ring
homomorphism `φ : R →+* S` with kernel `(z_l : l ∈ s)`: `S` is regular of dimension `n − |s|`, the
images of the `z_l`, `l ∉ s`, generate `𝔪_S`, and for `j ∉ s` the image `φ z_j` lies in `𝔪_S ∖ 𝔪_S²`
with `S ⧸ (φ z_j)` regular — the local form of Kollár's remark after Definition 24 that `E|_Z` is
again a simple normal crossing divisor on `Z`, whose members `E^i ∩ Z` are smooth divisors of `Z`.
-/

@[expose] public section

namespace AlgebraicGeometry

open IsLocalRing Ideal

universe u v

/-! ### Enumerating `Fin n` with a `Finset` first -/

section Enumeration

variable {n : ℕ}

/-- The enumeration of `Fin n` by the members of `s` (in order) and then those of `sᶜ`.-/
noncomputable def finsetPerm (s : Finset (Fin n)) : Fin (s.card + sᶜ.card) → Fin n :=
  fun i => Sum.elim (s.orderEmbOfFin rfl) (sᶜ.orderEmbOfFin rfl) (finSumFinEquiv.symm i)

/--
@isnad1 id=injectiv.0h2v.s5.dc34568b1c80 from=translated src=- shape=35d29739 vocab=bf03049d
-/
theorem finsetPerm_injective (s : Finset (Fin n)) : Function.Injective (finsetPerm s) := by
  intro a b hab
  apply finSumFinEquiv.symm.injective
  rcases ha : finSumFinEquiv.symm a with a' | a' <;>
    rcases hb : finSumFinEquiv.symm b with b' | b' <;>
    simp only [finsetPerm, ha, hb, Sum.elim_inl, Sum.elim_inr] at hab
  · rw [(s.orderEmbOfFin rfl).injective hab]
  · exact absurd (hab ▸ s.orderEmbOfFin_mem rfl a')
      (Finset.mem_compl.mp (sᶜ.orderEmbOfFin_mem rfl b'))
  · exact absurd (hab.symm ▸ s.orderEmbOfFin_mem rfl b')
      (Finset.mem_compl.mp (sᶜ.orderEmbOfFin_mem rfl a'))
  · rw [(sᶜ.orderEmbOfFin rfl).injective hab]

/--
@isnad1 id=eq.0h2v.s5.e7fb6225e9f7 from=translated src=- shape=ce9c4f5f vocab=89204201
-/
theorem card_add_card_compl_eq (s : Finset (Fin n)) : s.card + sᶜ.card = n := by
  rw [Finset.card_add_card_compl, Fintype.card_fin]

/-- The enumeration as an equivalence.-/
noncomputable def finsetEquiv (s : Finset (Fin n)) : Fin (s.card + sᶜ.card) ≃ Fin n :=
  Equiv.ofBijective (finsetPerm s) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨finsetPerm_injective s, by rw [Fintype.card_fin, Fintype.card_fin, card_add_card_compl_eq]⟩)

/--
@isnad1 id=eq.0h3v.s8.e5f71faad62c from=translated src=- shape=617317c3 vocab=3cb39a43
-/
theorem finsetEquiv_castAdd (s : Finset (Fin n)) (i : Fin s.card) :
    finsetEquiv s (Fin.castAdd sᶜ.card i) = s.orderEmbOfFin rfl i := by
  simp [finsetEquiv, finsetPerm]

/--
@isnad1 id=eq.0h3v.s8.75314e73c0ce from=translated src=- shape=461995ca vocab=81c2ad7f
-/
theorem finsetEquiv_natAdd (s : Finset (Fin n)) (i : Fin sᶜ.card) :
    finsetEquiv s (Fin.natAdd s.card i) = sᶜ.orderEmbOfFin rfl i := by
  simp [finsetEquiv, finsetPerm]

/-- The initial segment of length `|s|` of the enumeration is `s`.
@isnad1 id=eq.0h2v.s8.bf00897610a3 from=translated src=- shape=5b81ec52 vocab=9d0bafb9
-/
theorem finsetEquiv_image_lt (s : Finset (Fin n)) :
    finsetEquiv s '' {j : Fin (s.card + sᶜ.card) | j.val < s.card} = ↑s := by
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj' : j.val < s.card := hj
    have : j = Fin.castAdd sᶜ.card ⟨j.val, hj'⟩ := Fin.ext rfl
    rw [this, finsetEquiv_castAdd]
    exact s.orderEmbOfFin_mem rfl _
  · intro hx
    obtain ⟨i, hi⟩ : x ∈ Set.range (s.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact hx
    exact ⟨Fin.castAdd sᶜ.card i, i.2, by rw [finsetEquiv_castAdd, hi]⟩

/-- The tail of the enumeration is the complement `sᶜ`.
@isnad1 id=not.0h3v.s8.97d4bec0d852 from=translated src=- shape=697ffe5a vocab=33d55e0e
-/
theorem finsetEquiv_natAdd_notMem (s : Finset (Fin n)) (i : Fin sᶜ.card) :
    finsetEquiv s (Fin.natAdd s.card i) ∉ s := by
  rw [finsetEquiv_natAdd]
  exact Finset.mem_compl.mp (sᶜ.orderEmbOfFin_mem rfl i)

/-- The position of `j ∉ s` in the enumeration of `sᶜ`.-/
noncomputable def complIndex {s : Finset (Fin n)} {j : Fin n} (hj : j ∉ s) : Fin sᶜ.card :=
  (sᶜ.orderIsoOfFin rfl).symm ⟨j, Finset.mem_compl.mpr hj⟩

/--
@isnad1 id=eq.1h3v.s7.bd86da693665 from=translated src=- shape=7899d18b vocab=91928a77
-/
theorem orderEmbOfFin_complIndex {s : Finset (Fin n)} {j : Fin n} (hj : j ∉ s) :
    sᶜ.orderEmbOfFin rfl (complIndex hj) = j := by
  rw [← Finset.coe_orderIsoOfFin_apply, complIndex, OrderIso.apply_symm_apply]

/--
@isnad1 id=eq.0h4v.s8.7138a1645df5 from=translated src=- shape=1ced31b8 vocab=ac5b81e0
-/
theorem image_finset_eq_image_lt {R : Type u} (z : Fin n → R) (s : Finset (Fin n)) :
    z '' ↑s = (z ∘ finsetEquiv s) '' {j : Fin (s.card + sᶜ.card) | j.val < s.card} := by
  rw [Set.image_comp, finsetEquiv_image_lt]

end Enumeration

/-! ### Quotients by a subset of the coordinates -/

section Ring

variable {R : Type u} [CommRing R] {n : ℕ}

/--
@isnad1 id=eq.1h3v.s6.7fd3e1344755 from=translated src=- shape=1edd5106 vocab=0cb4f8df
-/
theorem natCast_card_add_card_compl (hn : (n : WithBot ℕ∞) = ringKrullDim R)
    (s : Finset (Fin n)) : ((s.card + sᶜ.card : ℕ) : WithBot ℕ∞) = ringKrullDim R := by
  rw [card_add_card_compl_eq]; exact hn

/--
@isnad1 id=eq.0h5v.s7.e07626f3851b from=translated src=- shape=426e8fed vocab=8fb16df5
-/
theorem span_image_insert (z : Fin n → R) (s : Finset (Fin n)) (j : Fin n) :
    span (z '' ↑(insert j s)) = span (z '' ↑s) ⊔ span {z j} := by
  rw [Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert, sup_comm]

/--
@isnad1 id=eq.1h4v.s8.e9de73f51af5 from=translated src=- shape=3a46e40b vocab=1f30e710
-/
theorem span_range_comp_finsetEquiv [IsLocalRing R] {z : Fin n → R}
    (hz : maximalIdeal R = span (Set.range z)) (s : Finset (Fin n)) :
    maximalIdeal R = span (Set.range (z ∘ finsetEquiv s)) := by
  rw [hz, (finsetEquiv s).surjective.range_comp]

end Ring

section Quotient

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] {n : ℕ} {z : Fin n → R}

/-- The quotient of a regular local ring by part of a regular system of parameters — an unordered
subset of the coordinates — is regular.
@isnad1 id=isregula.2h4v.s6.9ae436c70145 from=translated src=- shape=1dec96fe vocab=1a1c2f73
-/
theorem isRegularLocalRing_quotient_span_image_finset (hz : maximalIdeal R = span (Set.range z))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) (s : Finset (Fin n)) :
    IsRegularLocalRing (R ⧸ span (z '' ↑s)) := by
  rw [image_finset_eq_image_lt]
  exact isRegularLocalRing_quotient_span_image_lt (z ∘ finsetEquiv s)
    (span_range_comp_finsetEquiv hz s) (natCast_card_add_card_compl hn s) s.card

/-- `dim R ⧸ (z_l : l ∈ s) + |s| = dim R`.
@isnad1 id=eq.2h4v.s7.fa1e73390563 from=translated src=- shape=35446e85 vocab=4ad56e7e
-/
theorem ringKrullDim_quotient_span_image_finset (hz : maximalIdeal R = span (Set.range z))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) (s : Finset (Fin n)) :
    ringKrullDim (R ⧸ span (z '' ↑s)) + s.card = ringKrullDim R := by
  rw [image_finset_eq_image_lt]
  exact ringKrullDim_quotient_span_image_lt (z ∘ finsetEquiv s)
    (span_range_comp_finsetEquiv hz s) (natCast_card_add_card_compl hn s) (Nat.le_add_right _ _)

/-- `dim R ⧸ (z_l : l ∈ s) = n − |s|`, as a natural number.
@isnad1 id=eq.2h4v.s7.830336d19a41 from=translated src=- shape=0cd6e175 vocab=1de2bc54
-/
theorem natCast_sub_card_eq_ringKrullDim_quotient (hz : maximalIdeal R = span (Set.range z))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) (s : Finset (Fin n)) :
    ((n - s.card : ℕ) : WithBot ℕ∞) = ringKrullDim (R ⧸ span (z '' ↑s)) := by
  have := isRegularLocalRing_quotient_span_image_finset hz hn s
  have h := ringKrullDim_quotient_span_image_finset hz hn s
  rw [← hn, ← IsRegularLocalRing.spanFinrank_maximalIdeal] at h
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal]
  have h' : (((maximalIdeal (R ⧸ span (z '' ↑s))).spanFinrank + s.card : ℕ) : WithBot ℕ∞) =
      ((n : ℕ) : WithBot ℕ∞) := by
    rw [Nat.cast_add]; exact h
  rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, WithBot.coe_inj, Nat.cast_inj] at h'
  congr 1
  omega

/-! ### A coordinate outside `s` is independent of the coordinates in `s` -/

/-- A coordinate `z_j`, `j ∉ s`, is not a combination of the `z_l`, `l ∈ s`, modulo `𝔪²` — the
classes of the coordinates are a basis of `𝔪/𝔪²`.
@isnad1 id=not.3h5v.s8.71a3f35279ba from=translated src=- shape=7e8be446 vocab=aa342a52
-/
theorem notMem_sq_sup_span_image (hz : maximalIdeal R = span (Set.range z))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) {s : Finset (Fin n)} {j : Fin n} (hj : j ∉ s) :
    z j ∉ maximalIdeal R ^ 2 ⊔ span (z '' ↑s) := by
  classical
  intro hmem
  obtain ⟨b, hb⟩ := exists_basis_cotangentSpace_of_span_eq z hz hn
  have hzm : ∀ i, z i ∈ maximalIdeal R := x_mem_maximalIdeal_of_span_eq z hz
  rw [Submodule.mem_sup] at hmem
  obtain ⟨q, hq, w, hw, hqw⟩ := hmem
  rw [Set.image_eq_range] at hw
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hw
  have hqm : q ∈ maximalIdeal R := Ideal.pow_le_self two_ne_zero hq
  -- the identity `z_j = q + ∑ c_l z_l` inside `𝔪`
  have hid : (⟨z j, hzm j⟩ : maximalIdeal R) =
      ⟨q, hqm⟩ + ∑ l : (↑s : Set (Fin n)), c l • (⟨z l, hzm l⟩ : maximalIdeal R) := by
    ext
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul]
    rw [← hqw, hc]
  have h0 : (maximalIdeal R).toCotangent ⟨q, hqm⟩ = 0 := by
    rw [Ideal.toCotangent_eq_zero]; exact hq
  -- in the cotangent space: `b j` is a combination of the `b l`, `l ∈ s`
  have key : b j = ∑ l : (↑s : Set (Fin n)), residue R (c l) • b (l : Fin n) := by
    rw [hb j, hid, map_add, h0, zero_add, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [LinearMap.map_smul, hb (l : Fin n), ← ResidueField.algebraMap_eq, algebraMap_smul]
  have hmem' : b j ∈ Submodule.span (ResidueField R) (b '' ↑s) := by
    rw [key]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨(l : Fin n), l.2, rfl⟩)
  exact b.linearIndependent.notMem_span_image hj hmem'

/--
@isnad1 id=not.3h5v.s7.8976a54aca89 from=translated src=- shape=cb71b9c1 vocab=80b943c8
-/
theorem notMem_span_image_of_notMem (hz : maximalIdeal R = span (Set.range z))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) {s : Finset (Fin n)} {j : Fin n} (hj : j ∉ s) :
    z j ∉ span (z '' ↑s) := fun h =>
  notMem_sq_sup_span_image hz hn hj (Submodule.mem_sup_right h)

/-- `z_j ∈ (z_l : l ∈ s)` iff `j ∈ s`.
@isnad1 id=iff.2h5v.s7.9f2df88918f8 from=translated src=- shape=2b849f6c vocab=80b943c8
-/
theorem mem_span_image_iff (hz : maximalIdeal R = span (Set.range z))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) (s : Finset (Fin n)) (j : Fin n) :
    z j ∈ span (z '' ↑s) ↔ j ∈ s :=
  ⟨fun h => by_contra fun hj => notMem_span_image_of_notMem hz hn hj h,
    fun h => subset_span (Set.mem_image_of_mem z (Finset.mem_coe.mpr h))⟩

/-- `(z_j) ⊆ (z_l : l ∈ s)` iff `j ∈ s`.
@isnad1 id=iff.2h5v.s7.ba7e39409bb4 from=translated src=- shape=47179288 vocab=fc2d3617
-/
theorem span_singleton_le_span_image_iff (hz : maximalIdeal R = span (Set.range z))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) (s : Finset (Fin n)) (j : Fin n) :
    span {z j} ≤ span (z '' ↑s) ↔ j ∈ s := by
  rw [Ideal.span_singleton_le_iff_mem, mem_span_image_iff hz hn]

end Quotient

/-! ### Through a surjection with kernel `(z_l : l ∈ s)` -/

section Surjective

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] {φ : R →+* S} {n : ℕ}
  {z : Fin n → R} {s : Finset (Fin n)}

/--
@isnad1 id=eq.2h7v.s7.19838708c922 from=translated src=- shape=52385535 vocab=b0493783
-/
theorem apply_eq_zero_of_mem (hker : RingHom.ker φ = span (z '' ↑s)) {l : Fin n} (hl : l ∈ s) :
    φ (z l) = 0 := by
  rw [← RingHom.mem_ker, hker]
  exact subset_span (Set.mem_image_of_mem z (Finset.mem_coe.mpr hl))

/-- The images of the coordinates outside `s` span the image of `(z_0, …, z_{n-1})`.
@isnad1 id=eq.1h6v.s9.d59d6ddaca00 from=translated src=- shape=19dc28f9 vocab=1694d7d9
-/
theorem span_range_comp_compl_eq_map (hker : RingHom.ker φ = span (z '' ↑s)) :
    span (Set.range (φ ∘ z ∘ sᶜ.orderEmbOfFin rfl)) = (span (Set.range z)).map φ := by
  rw [Ideal.map_span, ← Set.range_comp]
  refine le_antisymm (span_mono ?_) (span_le.mpr ?_)
  · rintro _ ⟨l, rfl⟩
    exact ⟨sᶜ.orderEmbOfFin rfl l, rfl⟩
  · rintro _ ⟨i, rfl⟩
    by_cases hi : i ∈ s
    · rw [Function.comp_apply, apply_eq_zero_of_mem hker hi]
      exact zero_mem _
    · obtain ⟨l, hl⟩ : i ∈ Set.range (sᶜ.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]; exact Finset.mem_compl.mpr hi
      exact subset_span ⟨l, by simp [hl]⟩

/-- The kernel of `R → S → S ⧸ (φ z_j)` is `(z_l : l ∈ insert j s)`.
@isnad1 id=eq.2h7v.s10.a682552e9b3b from=translated src=- shape=7bc75c14 vocab=d19b3a4c
-/
theorem ker_mk_comp (hφ : Function.Surjective φ) (hker : RingHom.ker φ = span (z '' ↑s))
    (j : Fin n) :
    RingHom.ker ((Ideal.Quotient.mk (span {φ (z j)})).comp φ) = span (z '' ↑(insert j s)) := by
  have hmap : span {φ (z j)} = (span {z j}).map φ := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [← RingHom.comap_ker, Ideal.mk_ker, span_image_insert, hmap,
    Ideal.comap_map_of_surjective φ hφ, ← hker, sup_comm]
  rfl

variable [IsRegularLocalRing R]

/-- The target of a surjection with kernel `(z_l : l ∈ s)` is regular.
@isnad1 id=isregula.4h6v.s7.f0ea9d66bbe5 from=translated src=- shape=f52dc92e vocab=4faaecf4
-/
theorem isRegularLocalRing_of_ker_eq_span_image (hz : maximalIdeal R = span (Set.range z))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = span (z '' ↑s)) : IsRegularLocalRing S := by
  have := isRegularLocalRing_quotient_span_image_finset hz hn s
  rw [← hker] at this
  exact IsRegularLocalRing.of_ringEquiv (RingHom.quotientKerEquivOfSurjective hφ)

/-- `dim S = n − |s|`.
@isnad1 id=eq.4h6v.s7.8d7789387fd7 from=translated src=- shape=950848e6 vocab=fd5b4d4c
-/
theorem natCast_sub_card_eq_ringKrullDim_of_ker (hz : maximalIdeal R = span (Set.range z))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = span (z '' ↑s)) :
    ((n - s.card : ℕ) : WithBot ℕ∞) = ringKrullDim S := by
  rw [← ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hφ), hker]
  exact natCast_sub_card_eq_ringKrullDim_quotient hz hn s

/-- `S ⧸ (φ z_j)` is regular — it is `R ⧸ (z_l : l ∈ insert j s)`.
@isnad1 id=isregula.4h7v.s8.c4c3796bfccf from=translated src=- shape=c2c7a56d vocab=431a34c3
-/
theorem isRegularLocalRing_quotient_span_singleton_apply
    (hz : maximalIdeal R = span (Set.range z)) (hn : (n : WithBot ℕ∞) = ringKrullDim R)
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ = span (z '' ↑s)) (j : Fin n) :
    IsRegularLocalRing (S ⧸ span {φ (z j)}) := by
  have := isRegularLocalRing_quotient_span_image_finset hz hn (insert j s)
  rw [← ker_mk_comp hφ hker j] at this
  exact IsRegularLocalRing.of_ringEquiv (RingHom.quotientKerEquivOfSurjective
    (f := (Ideal.Quotient.mk (span {φ (z j)})).comp φ) (Ideal.Quotient.mk_surjective.comp hφ))

variable [IsLocalRing S]

/--
@isnad1 id=mem.2h6v.s7.6b3300f43db0 from=translated src=- shape=4c2b69a3 vocab=6dede60f
-/
theorem apply_mem_maximalIdeal (hz : maximalIdeal R = span (Set.range z))
    (hφ : Function.Surjective φ) (j : Fin n) : φ (z j) ∈ maximalIdeal S := by
  rw [← IsLocalRing.map_maximalIdeal_of_surjective φ hφ]
  exact Ideal.mem_map_of_mem φ (x_mem_maximalIdeal_of_span_eq z hz j)

/-- The image of `z_j`, `j ∉ s`, lies outside `𝔪_S²`.
@isnad1 id=not.5h7v.s8.345ca440d4d4 from=translated src=- shape=b53253cc vocab=600ad1b5
-/
theorem apply_notMem_maximalIdeal_sq (hz : maximalIdeal R = span (Set.range z))
    (hn : (n : WithBot ℕ∞) = ringKrullDim R) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = span (z '' ↑s)) {j : Fin n} (hj : j ∉ s) :
    φ (z j) ∉ maximalIdeal S ^ 2 := by
  intro h
  rw [← IsLocalRing.map_maximalIdeal_of_surjective φ hφ, ← Ideal.map_pow,
    Ideal.mem_map_iff_of_surjective φ hφ] at h
  obtain ⟨a, ha, hEq⟩ := h
  have hsub : z j - a ∈ span (z '' ↑s) := by
    rw [← hker, RingHom.mem_ker, map_sub, hEq, sub_self]
  apply notMem_sq_sup_span_image hz hn hj
  rw [show z j = a + (z j - a) by ring]
  exact Submodule.add_mem_sup ha hsub

/-- The images of the coordinates outside `s` generate `𝔪_S`.
@isnad1 id=eq.3h6v.s9.d54903e6eaf7 from=translated src=- shape=ab2b0d05 vocab=a34df4b1
-/
theorem span_range_comp_compl_eq_maximalIdeal (hz : maximalIdeal R = span (Set.range z))
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ = span (z '' ↑s)) :
    span (Set.range (φ ∘ z ∘ sᶜ.orderEmbOfFin rfl)) = maximalIdeal S := by
  rw [span_range_comp_compl_eq_map hker, ← hz, IsLocalRing.map_maximalIdeal_of_surjective φ hφ]

end Surjective

end AlgebraicGeometry

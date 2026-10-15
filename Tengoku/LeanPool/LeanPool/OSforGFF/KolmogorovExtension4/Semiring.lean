/-
Copyright (c) 2026 Rémy Degenne, Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Tengoku

/-! # Semirings of sets

A semi-ring of sets `C` is a family of sets containing `∅`, stable by intersection and such that
for all `s, t ∈ C`, `t \ s` is equal to a disjoint union of finitely many sets in `C`.

THIS FILE IS NOT USED FOR THE MAIN RESULT
-/

@[expose] public section

variable {α : Type*} {C : Set (Set α)} {s t : Set α} {J : Finset (Set α)}

open Finset Set

namespace MeasureTheory

/-- A field of sets is a family of sets which is stable under union, difference, and contains
the empty set and the whole space.
-/
structure IsSetField (C : Set (Set α)) : Prop extends IsSetRing C where
  univ_mem : Set.univ ∈ C

namespace IsSetField

/--
@isnad1 id=mem.3h4v.s5.0ed927f3e5e3 from=translated src=- shape=2366cb28 vocab=b0bfe714
-/
theorem inter_mem (hC : IsSetField C) (hs : s ∈ C) (ht : t ∈ C) : s ∩ t ∈ C :=
  hC.toIsSetRing.inter_mem hs ht

/--
@isnad1 id=mem.2h3v.s5.e00206040807 from=translated src=- shape=a2c62b73 vocab=182dc866
-/
theorem compl_mem (hC : IsSetField C) (hs : s ∈ C) : sᶜ ∈ C := by
  rw [compl_eq_univ_sdiff]; exact hC.sdiff_mem hC.univ_mem hs

/--
@isnad1 id=issetsem.1h2v.s3.d5310e3cef97 from=translated src=- shape=7d55a916 vocab=7825aa26
-/
theorem toIsSetSemiring (hC : IsSetField C) : IsSetSemiring C :=
  hC.toIsSetRing.isSetSemiring

/--
@isnad1 id=mem.2h4v.s6.f44840915124 from=translated src=- shape=87dcc1ce vocab=ffd7aaea
-/
theorem iUnion_le_mem (hC : IsSetField C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋃ i ≤ n, s i) ∈ C := hC.toIsSetRing.iUnion_le_mem hs n

/--
@isnad1 id=mem.2h4v.s6.d2bfa449a87a from=translated src=- shape=87dcc1ce vocab=0034cf96
-/
theorem iInter_le_mem (hC : IsSetField C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋂ i ≤ n, s i) ∈ C := hC.toIsSetRing.iInter_le_mem hs n

/--
@isnad1 id=mem.2h4v.s7.13cf8b21ff10 from=translated src=- shape=602de1e2 vocab=eb08131e
-/
theorem partialSups_mem (hC : IsSetField C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    partialSups s n ∈ C := hC.toIsSetRing.partialSups_mem hs n

/--
@isnad1 id=mem.2h4v.s5.dffd996c68bc from=translated src=- shape=4f8be327 vocab=7541e8f0
-/
theorem disjointed_mem (hC : IsSetField C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    disjointed s n ∈ C := hC.toIsSetRing.disjointed_mem hs n

end IsSetField

end MeasureTheory

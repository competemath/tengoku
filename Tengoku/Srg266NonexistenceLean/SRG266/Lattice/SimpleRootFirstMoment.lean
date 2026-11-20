/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.NormTwoRootReflection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

/--
@isnad1 id=eq.0h4v.s11.e8cb6c691cd2 from=translated src=- shape=c4145983 vocab=12153491
-/
theorem reflectNormTwoRoot_pairing {n : ℕ} (L : PDUnimodularLattice n)
    (a r : NormTwoRoot L) :
    L.pairing (reflectNormTwoRoot L a r).1 a.1 = -L.pairing r.1 a.1 := by
  simp only [reflectNormTwoRoot_val, map_sub, LinearMap.sub_apply, map_zsmul,
    LinearMap.smul_apply, zsmul_eq_mul, Int.cast_id, a.2]
  ring

/--
@isnad1 id=involuti.0h3v.s4.b52e36fd768c from=translated src=- shape=ee8cbc46 vocab=d57d4814
-/
theorem reflectNormTwoRoot_involutive {n : ℕ} (L : PDUnimodularLattice n)
    (a : NormTwoRoot L) : Function.Involutive (reflectNormTwoRoot L a) := by
  intro r
  apply Subtype.ext
  rw [reflectNormTwoRoot_val, reflectNormTwoRoot_pairing, reflectNormTwoRoot_val]
  simp only [neg_zsmul, sub_neg_eq_add]
  abel

/--
@isnad1 id=eq.0h3v.s4.967a58956110 from=translated src=- shape=e66419a2 vocab=7e6e337a
-/
theorem reflectNormTwoRoot_self {n : ℕ} (L : PDUnimodularLattice n)
    (a : NormTwoRoot L) : reflectNormTwoRoot L a a = -a := by
  apply Subtype.ext
  simp only [reflectNormTwoRoot_val, a.2, NormTwoRoot.coe_neg, two_zsmul]
  abel

/--
@isnad1 id=lt.4h5v.s10.737c6f885117 from=translated src=- shape=38625846 vocab=9e51619e
-/
theorem reflectNormTwoRoot_simple_positive {n : ℕ} {L : PDUnimodularLattice n}
    (f : L.carrier →+ ℤ) (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    {a r : NormTwoRoot L} (ha : a ∈ simpleRootSet f)
    (hr : 0 < f r.1) (hne : r ≠ a) :
    0 < f (reflectNormTwoRoot L a r).1 := by
  have hapos : 0 < f a.1 :=
    IsAddIndecomposable.baseOf_subset_pos normTwoRootVal f ha
  by_cases hp : 0 < L.pairing r.1 a.1
  · have hone := pairing_eq_one_of_simple_step hne hp
    apply sub_simpleRoot_positive f hf hr ha
    simp only [reflectNormTwoRoot_val, hone, one_zsmul]
  · have hn : L.pairing r.1 a.1 ≤ 0 := le_of_not_gt hp
    simp only [reflectNormTwoRoot_val, map_sub, map_zsmul, zsmul_eq_mul, Int.cast_id]
    nlinarith

/--
@isnad1 id=eq.2h4v.s11.1b2c4ffb825e from=translated src=- shape=8edb6a1a vocab=f54340c7
-/
theorem normTwoRoot_positive_sum_pairing_simple
    {n : ℕ} (L : PDUnimodularLattice n)
    (f : L.carrier →+ ℤ) (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (a : NormTwoRoot L) (ha : a ∈ simpleRootSet f) :
    (∑ r : NormTwoRoot L with 0 < f r.1, L.pairing r.1 a.1) = 2 := by
  classical
  let P : Finset (NormTwoRoot L) := Finset.univ.filter fun r => 0 < f r.1
  let S := P.erase a
  have hapos : 0 < f a.1 :=
    IsAddIndecomposable.baseOf_subset_pos normTwoRootVal f ha
  have haP : a ∈ P := by simp [P, hapos]
  have hkeep : ∀ r ∈ S, reflectNormTwoRoot L a r ∈ S := by
    intro r hr
    obtain ⟨hne, hrP⟩ := Finset.mem_erase.mp hr
    have hrpos : 0 < f r.1 := (Finset.mem_filter.mp hrP).2
    apply Finset.mem_erase.mpr
    constructor
    · intro heq
      have hroot : r = -a := by
        calc
          r = reflectNormTwoRoot L a (reflectNormTwoRoot L a r) :=
            (reflectNormTwoRoot_involutive L a r).symm
          _ = reflectNormTwoRoot L a a := congrArg (reflectNormTwoRoot L a) heq
          _ = -a := reflectNormTwoRoot_self L a
      have hfr : f r.1 = -f a.1 := by simp [hroot]
      omega
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        reflectNormTwoRoot_simple_positive f hf ha hrpos hne⟩
  have hcancel :
      (∑ r ∈ S, L.pairing r.1 a.1) = ∑ r ∈ S, -L.pairing r.1 a.1 := by
    apply Finset.sum_nbij' (reflectNormTwoRoot L a) (reflectNormTwoRoot L a)
      hkeep hkeep
      (fun r _ => reflectNormTwoRoot_involutive L a r)
      (fun r _ => reflectNormTwoRoot_involutive L a r)
    intro r _
    rw [reflectNormTwoRoot_pairing, neg_neg]
  have hzero : (∑ r ∈ S, L.pairing r.1 a.1) = 0 := by
    rw [Finset.sum_neg_distrib] at hcancel
    omega
  have hsum := Finset.sum_erase_add P (fun r => L.pairing r.1 a.1) haP
  change (∑ r ∈ S, L.pairing r.1 a.1) + L.pairing a.1 a.1 =
    ∑ r ∈ P, L.pairing r.1 a.1 at hsum
  rw [hzero, a.2, zero_add] at hsum
  exact hsum.symm

end SRG266.Lattice

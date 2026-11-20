/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.NormTwoRootBasis
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.NormTwoRootFinite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266
namespace Lattice

noncomputable def reflectNormTwoRoot {n : ℕ} (L : PDUnimodularLattice n)
    (a b : NormTwoRoot L) : NormTwoRoot L :=
  ⟨b.1 - (L.pairing b.1 a.1) • a.1, by
    have hsym : L.pairing a.1 b.1 = L.pairing b.1 a.1 :=
      L.symmetric.eq _ _
    simp only [map_sub, LinearMap.sub_apply, map_zsmul,
      LinearMap.smul_apply, zsmul_eq_mul, Int.cast_id]
    rw [a.2, b.2, hsym]
    ring⟩

/--
@isnad1 id=eq.0h4v.s11.3789f6df6787 from=translated src=- shape=6594fdb1 vocab=ec074924
-/
@[simp]
theorem reflectNormTwoRoot_val {n : ℕ} (L : PDUnimodularLattice n)
    (a b : NormTwoRoot L) :
    (reflectNormTwoRoot L a b).1 =
      b.1 - (L.pairing b.1 a.1) • a.1 :=
  rfl

/--
@isnad1 id=mem.1h4v.s10.4d6c68647843 from=translated src=- shape=2a8d93b6 vocab=98f7535c
-/
theorem positiveRoot_mem_simpleRootClosure {n : ℕ}
    {L : PDUnimodularLattice n} (f : L.carrier →+ ℤ)
    {r : NormTwoRoot L} (hr : 0 < f r.1) :
    r.1 ∈ AddSubmonoid.closure (normTwoRootVal '' simpleRootSet f) := by
  rw [simpleRootSet,
    AddSubmonoid.closure_image_isAddIndecomposable_baseOf]
  exact AddSubmonoid.subset_closure ⟨r, hr, rfl⟩

/--
@isnad1 id=ex.1h4v.s10.7c097fea8205 from=translated src=- shape=b1bb9dc9 vocab=a83d16c9
-/
theorem exists_simpleRoot_pairing_pos {n : ℕ}
    {L : PDUnimodularLattice n} (f : L.carrier →+ ℤ)
    {r : NormTwoRoot L} (hr : 0 < f r.1) :
    ∃ s : NormTwoRoot L, s ∈ simpleRootSet f ∧
      0 < L.pairing r.1 s.1 := by
  have hrmem := positiveRoot_mem_simpleRootClosure f hr
  by_contra hnot
  push Not at hnot
  have hnonpos : L.pairing r.1 r.1 ≤ 0 := by
    have hclosure : ∀ x,
        x ∈ AddSubmonoid.closure (normTwoRootVal '' simpleRootSet f) →
          L.pairing x r.1 ≤ 0 := by
      intro x hx
      induction hx using AddSubmonoid.closure_induction with
      | mem x hx =>
          obtain ⟨s, hs, rfl⟩ := hx
          rw [L.symmetric.eq]
          exact hnot s hs
      | zero => simp
      | add x y _ _ hx hy =>
          simpa only [map_add, LinearMap.add_apply] using add_nonpos hx hy
    exact hclosure r.1 hrmem
  rw [r.2] at hnonpos
  omega

/--
@isnad1 id=lt.4h6v.s11.f7210cdeae7d from=translated src=- shape=2b38111b vocab=af4e0cc3
-/
theorem sub_simpleRoot_positive {n : ℕ}
    {L : PDUnimodularLattice n} (f : L.carrier →+ ℤ)
    (hf : ∀ u : NormTwoRoot L, f u.1 ≠ 0)
    {r s t : NormTwoRoot L} (hr : 0 < f r.1)
    (hs : s ∈ simpleRootSet f)
    (ht : r.1 - s.1 = t.1) :
    0 < f t.1 := by
  have hspos : 0 < f s.1 :=
    (IsAddIndecomposable.baseOf_subset_pos normTwoRootVal f hs)
  have hft : f t.1 = f r.1 - f s.1 := by
    rw [← ht]
    exact map_sub f r.1 s.1
  rcases lt_or_gt_of_ne (hf t) with hneg | hpos
  · exfalso
    have hnegr : 0 < f (-t).1 := by simpa using neg_pos.mpr hneg
    have hsind := hs
    change IsAddIndecomposable normTwoRootVal
      {u | 0 < f (normTwoRootVal u)} s at hsind
    have hsum : s.1 = r.1 + (-t).1 := by
      rw [NormTwoRoot.coe_neg, ← ht]
      abel
    rcases hsind.2 r hr (-t) hnegr hsum with hzero | hzero
    · exact normTwoRootVal_ne_zero r hzero
    · exact normTwoRootVal_ne_zero (-t) hzero
  · exact hpos

/--
@isnad1 id=eq.2h4v.s11.25ffd41b23b2 from=translated src=- shape=0d666d63 vocab=c3dfc457
-/
theorem pairing_eq_one_of_simple_step {n : ℕ}
    {L : PDUnimodularLattice n} {r s : NormTwoRoot L}
    (hrs : r ≠ s) (hpair : 0 < L.pairing r.1 s.1) :
    L.pairing r.1 s.1 = 1 := by
  have hne : r.1 - s.1 ≠ 0 := by
    intro h
    exact hrs (Subtype.ext (sub_eq_zero.mp h))
  have hpos := L.positiveDefinite (r.1 - s.1) hne
  have hsym : L.pairing s.1 r.1 = L.pairing r.1 s.1 :=
    L.symmetric.eq _ _
  simp only [map_sub, LinearMap.sub_apply] at hpos
  rw [r.2, s.2, hsym] at hpos
  omega

/--
@isnad1 id=eq.2h5v.s11.e920b28f4b62 from=translated src=- shape=29e30361 vocab=b87bba6e
-/
theorem reflect_sub_simpleRoot {n : ℕ}
    {L : PDUnimodularLattice n} {r s t : NormTwoRoot L}
    (hpair : L.pairing r.1 s.1 = 1) (ht : r.1 - s.1 = t.1) :
    reflectNormTwoRoot L s t = r := by
  apply Subtype.ext
  simp only [reflectNormTwoRoot_val, ← ht, map_sub,
    LinearMap.sub_apply, hpair, s.2]
  norm_num

/--
@isnad1 id=var.1h8v.s9.e12df96a1729 from=translated src=- shape=382e3365 vocab=88c25e0a
-/
theorem normTwoRoot_reflection_induction {n : ℕ}
    {L : PDUnimodularLattice n} (f : L.carrier →+ ℤ)
    (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (P : NormTwoRoot L → Prop)
    (hneg : ∀ r, P r → P (-r))
    (hsimple : ∀ r, r ∈ simpleRootSet f → P r)
    (hreflect : ∀ r s, s ∈ simpleRootSet f →
      P r → P (reflectNormTwoRoot L s r)) :
    ∀ r, P r := by
  let rec positive (r : NormTwoRoot L) (hr : 0 < f r.1) : P r := by
    by_cases hrsimple : r ∈ simpleRootSet f
    · exact hsimple r hrsimple
    · obtain ⟨s, hs, hpair⟩ := exists_simpleRoot_pairing_pos f hr
      have hrs : r ≠ s := fun h => hrsimple (h ▸ hs)
      obtain ⟨t, ht⟩ := sub_mem_normTwoRoots_of_pairing_pos hrs hpair
      have htpos : 0 < f t.1 :=
        sub_simpleRoot_positive f hf hr hs ht
      have hspos : 0 < f s.1 :=
        IsAddIndecomposable.baseOf_subset_pos normTwoRootVal f hs
      have hdecrease : (f (normTwoRootVal t)).toNat <
          (f (normTwoRootVal r)).toNat := by
        have hr' : 0 < f (normTwoRootVal r) := by
          simpa only [normTwoRootVal] using hr
        have hspos' : 0 < f (normTwoRootVal s) := by
          simpa only [normTwoRootVal] using hspos
        have hft : f (normTwoRootVal t) =
            f (normTwoRootVal r) - f (normTwoRootVal s) := by
          have hmap := congrArg f ht
          simpa only [map_sub] using hmap.symm
        omega
      have hrec : P t := positive t htpos
      have hpone := pairing_eq_one_of_simple_step hrs hpair
      rw [← reflect_sub_simpleRoot hpone ht]
      exact hreflect t s hs hrec
    termination_by (f (normTwoRootVal r)).toNat
  intro r
  rcases lt_or_gt_of_ne (hf r) with hnegf | hposf
  · have hp : P (-r) := positive (-r) (by simpa using neg_pos.mpr hnegf)
    simpa using hneg (-r) hp
  · exact positive r hposf

end Lattice
end SRG266

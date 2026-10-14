/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.CommonNeighbourConjecture.Examples.EveryBase.AbstractSeed

/-!
# The odd affine Frobenius groups used by the every-base-size construction

For odd `d`, this file defines

* `Fq d = GF(3^d)`;
* the subgroup `Cq d` of nonzero squares; and
* `Hq d = Fq d ⋊ Cq d`, acting affinely on `Fq d`.

The deleted permutation module and its irreducibility are deliberately kept in
the later files of the construction.  Here we prove the elementary finite-field
facts and the two-point support calculation needed there.
-/

@[expose] public section

namespace SaxlCounterexamples.EveryBase

open scoped BigOperators

/-- The finite field of order `3 ^ d`. -/
abbrev Fq (d : Nat) := GaloisField 3 d

noncomputable instance fqFintype (d : Nat) : Fintype (Fq d) :=
  Fintype.ofFinite (Fq d)

/-- The subgroup of nonzero squares in `GF(3^d)`. -/
noncomputable abbrev Cq (d : Nat) := Subgroup.square (Fq d)ˣ

noncomputable instance cqFintype (d : Nat) : Fintype (Cq d) :=
  Fintype.ofFinite (Cq d)

/-- The affine Frobenius group `GF(3^d) ⋊ Cq`. -/
abbrev Hq (d : Nat) := Saxl.AffineGroup (Cq d) (Fq d)

/--
@isnad1 id=eq.1h1v.s5.fcda8a68901a from=translated src=- shape=dcde83a3 vocab=bb121176
-/
theorem three_pow_mod_four_of_odd (d : Nat) (hd : Odd d) :
    3 ^ d % 4 = 3 := by
  obtain ⟨k, rfl⟩ := hd
  rw [pow_add, pow_mul]
  have h9 : 9 ≡ 1 [MOD 4] := by norm_num [Nat.ModEq]
  have hk := h9.pow k |>.mul_right 3
  simpa [Nat.ModEq] using hk

/--
@isnad1 id=eq.1h1v.s4.4f4871ae6d1d from=translated src=- shape=a31ae772 vocab=0f7f5eb4
-/
theorem fq_card (d : Nat) (hd : Odd d) : Nat.card (Fq d) = 3 ^ d := by
  rw [GaloisField.card 3 d]
  intro h
  subst d
  norm_num at hd

/--
@isnad1 id=eq.1h1v.s4.cdf431012e45 from=translated src=- shape=16b167d3 vocab=1bc3d44c
-/
theorem fq_card_mod_four (d : Nat) (hd : Odd d) :
    Nat.card (Fq d) % 4 = 3 := by
  rw [fq_card d hd]
  exact three_pow_mod_four_of_odd d hd

/--
@isnad1 id=odd.1h1v.s3.3e480a4e24af from=translated src=- shape=d78201a6 vocab=d0f9d9d2
-/
theorem fq_odd_card (d : Nat) (hd : Odd d) : Odd (Nat.card (Fq d)) := by
  rw [fq_card d hd]
  exact (show Odd 3 from ⟨1, rfl⟩).pow

/--
@isnad1 id=eq.0h1v.s5.8dd4ee3dfd82 from=translated src=- shape=59ca8f69 vocab=2642bf5d
-/
theorem square_subgroup_eq_powRange (G : Type*) [CommGroup G] :
    Subgroup.square G = (powMonoidHom 2 : G →* G).range := by
  ext a
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    simpa [pow_two] using hr.symm
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    simpa [pow_two] using hr.symm

/--
@isnad1 id=eq.1h1v.s8.8eecf93f997b from=translated src=- shape=321c3493 vocab=943b884b
-/
theorem cq_card (d : Nat) (hd : Odd d) :
    Nat.card (Cq d) = (3 ^ d - 1) / 2 := by
  rw [show Cq d = (powMonoidHom 2 : (Fq d)ˣ →* (Fq d)ˣ).range by
    exact square_subgroup_eq_powRange (Fq d)ˣ]
  rw [IsCyclic.card_powMonoidHom_range, Nat.card_units, fq_card d hd]
  have hmod := three_pow_mod_four_of_odd d hd
  have hdiv : 2 ∣ 3 ^ d - 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  rw [Nat.gcd_eq_right_iff_dvd.mpr hdiv]

/--
@isnad1 id=odd.1h1v.s8.61ea7db148f4 from=translated src=- shape=7cc0c9ab vocab=3c7760a7
-/
theorem cq_odd_card (d : Nat) (hd : Odd d) : Odd (Nat.card (Cq d)) := by
  rw [cq_card d hd]
  refine ⟨3 ^ d / 4, ?_⟩
  have hmod := three_pow_mod_four_of_odd d hd
  have hdivmod := Nat.mod_add_div (3 ^ d) 4
  omega

/--
@isnad1 id=odd.1h1v.s3.c9e1f140f7e2 from=translated src=- shape=d78201a6 vocab=d67ec6ea
-/
theorem hq_odd_card (d : Nat) (hd : Odd d) : Odd (Nat.card (Hq d)) := by
  rw [SemidirectProduct.card, Nat.card_congr Multiplicative.toAdd,
    fq_card d hd]
  exact (show Odd (3 ^ d) from (show Odd 3 from ⟨1, rfl⟩).pow).mul
    (cq_odd_card d hd)

/--
@isnad1 id=not.1h1v.s6.21e56806cfb5 from=translated src=- shape=9f5af422 vocab=627b8f63
-/
theorem neg_one_not_square (d : Nat) (hd : Odd d) :
    ¬ IsSquare (-1 : Fq d) := by
  rw [FiniteField.isSquare_neg_one_iff]
  rw [Fintype.card_eq_nat_card, fq_card_mod_four d hd]
  simp

/--
@isnad1 id=issquare.3h2v.s7.76cfa1e4b87c from=translated src=- shape=4c1cc933 vocab=627b8f63
-/
theorem neg_isSquare_of_not_isSquare (d : Nat) (hd : Odd d)
    {z : Fq d} (hz0 : z ≠ 0) (hz : ¬ IsSquare z) : IsSquare (-z) := by
  classical
  have hcharz : quadraticChar (Fq d) z = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr hz
  have hcharm : quadraticChar (Fq d) (-1) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr (neg_one_not_square d hd)
  apply (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr hz0)).mp
  rw [show -z = (-1 : Fq d) * z by ring, map_mul, hcharm, hcharz]
  norm_num

/-- Package a nonzero square as an element of `Cq`. -/
noncomputable def squareUnit (d : Nat) {z : Fq d} (hz0 : z ≠ 0)
    (hz : IsSquare z) : Cq d := by
  classical
  refine ⟨Units.mk0 z hz0, ?_⟩
  obtain ⟨r, hr⟩ := hz
  have hr0 : r ≠ 0 := by
    intro h
    subst r
    simp only [mul_zero] at hr
    exact hz0 hr
  refine ⟨Units.mk0 r hr0, ?_⟩
  apply Units.ext
  simpa using hr

/--
@isnad1 id=issquare.0h2v.s9.1f72c119af75 from=translated src=- shape=1ea62889 vocab=d0678a49
-/
theorem cq_isSquare (d : Nat) (a : Cq d) : IsSquare (a.1.1 : Fq d) := by
  obtain ⟨r, hr⟩ := a.property
  refine ⟨(r : Fq d), ?_⟩
  have := congrArg (fun u : (Fq d)ˣ ↦ (u : Fq d)) hr
  simpa [pow_two] using this

/--
@isnad1 id=eq.0h3v.s11.27537584de43 from=translated src=- shape=b21b34de vocab=483a602f
-/
@[simp] theorem cq_smul_eq_mul (d : Nat) (a : Cq d) (x : Fq d) :
    a • x = (a.1.1 : Fq d) * x := by
  rfl

/-- The nonzero square field elements, represented without quotient choices as
the image of `Cq`. -/
noncomputable def cqValueFinset (d : Nat) : Finset (Fq d) :=
  by
    classical
    exact Finset.univ.image fun a : Cq d ↦ (a.1.1 : Fq d)

/--
@isnad1 id=iff.0h2v.s9.a4b869c0c64f from=translated src=- shape=77555d82 vocab=22bf7adf
-/
theorem mem_cqValueFinset_iff (d : Nat) (x : Fq d) :
    x ∈ cqValueFinset d ↔ ∃ a : Cq d, (a.1.1 : Fq d) = x := by
  classical
  constructor
  · rw [cqValueFinset, Finset.mem_image]
    rintro ⟨a, -, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [cqValueFinset, Finset.mem_image]
    exact ⟨a, Finset.mem_univ _, rfl⟩

/--
@isnad1 id=not.0h1v.s5.45a703478742 from=translated src=- shape=b3fc45e9 vocab=19a85e1e
-/
theorem zero_not_mem_cqValueFinset (d : Nat) :
    (0 : Fq d) ∉ cqValueFinset d := by
  rw [mem_cqValueFinset_iff]
  rintro ⟨a, ha⟩
  exact a.1.ne_zero ha

/--
@isnad1 id=eq.0h1v.s8.3aa99b3ca4ba from=translated src=- shape=e768ffb2 vocab=2c71836c
-/
theorem card_cqValueFinset (d : Nat) :
    (cqValueFinset d).card = Nat.card (Cq d) := by
  classical
  rw [cqValueFinset, Finset.card_image_of_injective]
  · exact Fintype.card_eq_nat_card
  · intro a b hab
    apply Subtype.ext
    apply Units.ext
    exact hab

/--
@isnad1 id=odd.1h1v.s3.0b8c0c7b59bb from=translated src=- shape=ed9fd762 vocab=c4bcfe76
-/
theorem odd_card_cqValueFinset (d : Nat) (hd : Odd d) :
    Odd (cqValueFinset d).card := by
  rw [card_cqValueFinset]
  exact cq_odd_card d hd

/-- The affine map `x ↦ b + z*x`, with square multiplier `z`. -/
noncomputable def affineOfSquare (d : Nat) (b z : Fq d) (hz0 : z ≠ 0)
    (hz : IsSquare z) : Hq d :=
  ⟨Multiplicative.ofAdd b, squareUnit d hz0 hz⟩

/--
@isnad1 id=eq.2h4v.s11.804c81137d68 from=translated src=- shape=08d51a3e vocab=9eaa04df
-/
theorem affineOfSquare_smul (d : Nat) (b z : Fq d)
    (hz0 : z ≠ 0) (hz : IsSquare z) (x : Fq d) :
    affineOfSquare d b z hz0 hz • x = b + z * x := by
  rfl

/-! ## The regular two-point support -/

/-- The characteristic function of the two-point set `{0,1}`. -/
noncomputable def twoPointVector (d : Nat) : Fq d → ZMod 2 :=
  by
    classical
    exact fun x ↦ if x = 0 ∨ x = 1 then 1 else 0

/--
@isnad1 id=eq.0h1v.s6.624bcc7e76f7 from=translated src=- shape=67494fe9 vocab=4f778e95
-/
@[simp] theorem twoPointVector_zero (d : Nat) : twoPointVector d 0 = 1 := by
  simp [twoPointVector]

/--
@isnad1 id=eq.0h1v.s6.b4519fd40779 from=translated src=- shape=67494fe9 vocab=4f778e95
-/
@[simp] theorem twoPointVector_one (d : Nat) : twoPointVector d 1 = 1 := by
  simp [twoPointVector]

/--
@isnad1 id=iff.0h2v.s7.9744ad6e755e from=translated src=- shape=4050963b vocab=4f778e95
-/
theorem twoPointVector_eq_one_iff (d : Nat) (x : Fq d) :
    twoPointVector d x = 1 ↔ x = 0 ∨ x = 1 := by
  classical
  simp only [twoPointVector]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by exact zero_ne_one) h

/--
@isnad1 id=eq.0h1v.s10.67fc76bc2724 from=translated src=- shape=bfb77a3e vocab=f37aff19
-/
theorem twoPointVector_eq_basisSum (d : Nat) :
    twoPointVector d =
      Pi.basisFun (ZMod 2) (Fq d) 0 + Pi.basisFun (ZMod 2) (Fq d) 1 := by
  classical
  funext x
  by_cases hx0 : x = 0
  · subst x
    simp [twoPointVector, Pi.basisFun_apply]
  · by_cases hx1 : x = 1
    · subst x
      simp [twoPointVector, Pi.basisFun_apply]
    · simp [twoPointVector, Pi.basisFun_apply, hx0, hx1]

/-- The two-point characteristic function belongs to the binary deleted
permutation module.
@isnad1 id=eq.0h1v.s6.1776c0d0d966 from=translated src=- shape=27d11345 vocab=630c4e84
-/
theorem twoPointVector_coordSum (d : Nat) :
    ∑ x : Fq d, twoPointVector d x = 0 := by
  classical
  rw [twoPointVector_eq_basisSum]
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  have hsum (a : Fq d) :
      ∑ x : Fq d, Pi.basisFun (ZMod 2) (Fq d) a x = 1 := by
    rw [Pi.basisFun_apply]
    simp [Pi.single_apply]
  rw [hsum, hsum]
  exact ZModModule.add_self 1

/-- An affine square map preserving `{0,1}` pointwise as a characteristic
function is the identity.  The only other possible setwise stabilizer would
have multiplier `-1`, which is not a square when `d` is odd.
@isnad1 id=eq.2h2v.s11.9c07401cf8d8 from=translated src=- shape=234d8c32 vocab=27ed119e
-/
theorem hq_eq_one_of_twoPointVector_comp_eq (d : Nat) (hd : Odd d)
    (g : Hq d)
    (hfix : ∀ x : Fq d, twoPointVector d (g • x) = twoPointVector d x) :
    g = 1 := by
  have hg0_mem : g • (0 : Fq d) = 0 ∨ g • (0 : Fq d) = 1 :=
    (twoPointVector_eq_one_iff d (g • (0 : Fq d))).mp (by
      rw [hfix, twoPointVector_zero])
  have hg1_mem : g • (1 : Fq d) = 0 ∨ g • (1 : Fq d) = 1 :=
    (twoPointVector_eq_one_iff d (g • (1 : Fq d))).mp (by
      rw [hfix, twoPointVector_one])
  have hg_ne : g • (0 : Fq d) ≠ g • (1 : Fq d) := by
    intro h
    have := congrArg (fun x : Fq d ↦ g⁻¹ • x) h
    have h01 : (0 : Fq d) = 1 := by
      simpa only [inv_smul_smul] using this
    exact zero_ne_one h01
  rcases hg0_mem with hg0 | hg0 <;> rcases hg1_mem with hg1 | hg1
  · exact (hg_ne (hg0.trans hg1.symm)).elim
  · apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      simpa [Saxl.affine_smul_def] using hg0
    · apply Subtype.ext
      apply Units.ext
      have hlin := hg1
      rw [Saxl.affine_smul_def] at hlin
      have htrans : g.left.toAdd = 0 := by
        simpa [Saxl.affine_smul_def] using hg0
      rw [htrans, zero_add] at hlin
      rw [cq_smul_eq_mul, mul_one] at hlin
      simpa using hlin
  · have htrans : g.left.toAdd = 1 := by
      simpa [Saxl.affine_smul_def] using hg0
    have hmult : (g.right.1.1 : Fq d) = -1 := by
      rw [Saxl.affine_smul_def, htrans] at hg1
      rw [cq_smul_eq_mul, mul_one] at hg1
      linear_combination hg1
    exfalso
    apply (neg_one_not_square d hd)
    rw [← hmult]
    exact cq_isSquare d g.right
  · exact (hg_ne (hg0.trans hg1.symm)).elim

/-! ## Odd cycles avoiding the distinguished point -/

/--
@isnad1 id=eq.0h2v.s6.7de490bf675e from=translated src=- shape=963fdb3e vocab=afb5301c
-/
theorem char_three_add_self (d : Nat) (x : Fq d) : x + x = -x := by
  have h3 : (3 : Fq d) = 0 := CharP.cast_eq_zero (Fq d) 3
  linear_combination h3 * x

/--
@isnad1 id=eq.0h2v.s6.0e43dfb61192 from=translated src=- shape=b44a125b vocab=f914f0c9
-/
theorem char_three_neg_sub_self (d : Nat) (x : Fq d) : -x - x = x := by
  have h := congrArg Neg.neg (char_three_add_self d x)
  simpa only [sub_eq_add_neg, neg_add_rev, neg_neg] using h

/-- The action of an element of `Hq d` whose translation part vanishes
preserves the odd set of nonzero square field elements.
@isnad1 id=iff.1h3v.s11.fe5b391a351d from=translated src=- shape=e6174714 vocab=cfefdf5c
-/
theorem cqValueFinset_invariant_of_left_eq_zero (d : Nat) (g : Hq d)
    (hgleft : g.left.toAdd = 0) (x : Fq d) :
    x ∈ cqValueFinset d ↔ g • x ∈ cqValueFinset d := by
  rw [mem_cqValueFinset_iff, mem_cqValueFinset_iff]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨g.right * c, ?_⟩
    simp [Saxl.affine_smul_def, hgleft, cq_smul_eq_mul]
  · rintro ⟨c, hc⟩
    refine ⟨g.right⁻¹ * c, ?_⟩
    have hc' : (c.1.1 : Fq d) =
        (g.right.1.1 : Fq d) * x := by
      simpa [Saxl.affine_smul_def, hgleft, cq_smul_eq_mul] using hc
    calc
      ((g.right⁻¹ * c).1.1 : Fq d) =
          ((g.right⁻¹).1.1 : Fq d) * (c.1.1 : Fq d) := by rfl
      _ = ((g.right⁻¹).1.1 : Fq d) *
          ((g.right.1.1 : Fq d) * x) := by rw [hc']
      _ = x := by
        simp

/-- Every affine element has an odd invariant cycle avoiding zero once
`d ≥ 3`.  This lower bound is necessary: a nonzero translation is transitive
on `GF(3)` when `d = 1`. -/
noncomputable def hqAvoidingCycle (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d)
    (g : Hq d) : AvoidingCycle (Hq d) (Fq d) g 0 := by
  classical
  by_cases hright : g.right = 1
  · by_cases hleft : g.left.toAdd = 0
    · refine {
        carrier := {1}
        avoids := by simp
        odd_card := by simp
        invariant := ?_ }
      intro x
      have hg_one : g = 1 := by
        apply SemidirectProduct.ext
        · apply Multiplicative.toAdd.injective
          simpa using hleft
        · simpa using hright
      simp [hg_one]
    · let b : Fq d := g.left.toAdd
      have hb0 : b ≠ 0 := hleft
      have hcardq : Fintype.card (Fq d) = 3 ^ d := by
        rw [Fintype.card_eq_nat_card, fq_card d hd]
      have hpow : 27 ≤ 3 ^ d := by
        have hp := Nat.pow_le_pow_right (n := 3) (by omega) hd3
        norm_num at hp ⊢
        exact hp
      let forbidden : Finset (Fq d) := {0, b, -b}
      have hforbidden : forbidden.card ≤ 3 := by
        dsimp [forbidden]
        calc
          ({0, b, -b} : Finset (Fq d)).card ≤
              ({b, -b} : Finset (Fq d)).card + 1 :=
            Finset.card_insert_le _ _
          _ ≤ ({-b} : Finset (Fq d)).card + 1 + 1 :=
            Nat.add_le_add_right (Finset.card_insert_le _ _) 1
          _ = 3 := by simp
      have hex : ∃ x : Fq d, x ∉ forbidden := by
        have hnotall : ¬ ∀ x : Fq d, x ∈ forbidden := by
          intro hall
          have hsub : (Finset.univ : Finset (Fq d)) ⊆ forbidden := by
            intro y _hy
            exact hall y
          have hc := Finset.card_le_card hsub
          rw [Finset.card_univ, hcardq] at hc
          omega
        exact not_forall.mp hnotall
      let x := Classical.choose hex
      have hx : x ∉ forbidden := Classical.choose_spec hex
      have hx0 : x ≠ 0 := by
        intro h
        apply hx
        simp [forbidden, h]
      have hxb : x ≠ b := by
        intro h
        apply hx
        simp [forbidden, h]
      have hxnb : x ≠ -b := by
        intro h
        apply hx
        simp [forbidden, h]
      have hbb : b + b = -b := char_three_add_self d b
      have gsmul (y : Fq d) : g • y = b + y := by
        simp [Saxl.affine_smul_def, b, hright]
      have hcycle0 : g • x = x + b := by
        rw [gsmul]
        ring
      have hcycle1 : g • (x + b) = x - b := by
        rw [gsmul]
        linear_combination hbb
      have hcycle2 : g • (x - b) = x := by
        rw [gsmul]
        ring
      have hx_add_ne_x : x + b ≠ x := by
        intro h
        apply hb0
        apply add_left_cancel (a := x)
        simpa using h
      have hx_sub_ne_x : x - b ≠ x := by
        intro h
        exact hb0 (sub_eq_self.mp h)
      have hx_add_ne_sub : x + b ≠ x - b := by
        intro h
        have hbeq : b = -b := by
          apply add_left_cancel (a := x)
          simpa [sub_eq_add_neg] using h
        have hbadd : b + b = b := hbb.trans hbeq.symm
        apply hb0
        apply add_right_cancel (b := b)
        simpa using hbadd
      refine {
        carrier := {x, x + b, x - b}
        avoids := ?_
        odd_card := ?_
        invariant := ?_ }
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨?_, ?_, ?_⟩
        · exact hx0.symm
        · intro h
          apply hxnb
          exact eq_neg_of_add_eq_zero_left h.symm
        · intro h
          apply hxb
          exact sub_eq_zero.mp h.symm
      · have hcard : ({x, x + b, x - b} : Finset (Fq d)).card = 3 := by
          rw [Finset.card_insert_of_notMem]
          · rw [Finset.card_insert_of_notMem]
            · simp
            · simpa using hx_add_ne_sub
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hx_add_ne_x.symm, hx_sub_ne_x.symm⟩
        rw [hcard]
        exact ⟨1, rfl⟩
      · intro y
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl | rfl)
          · exact Or.inr (Or.inl hcycle0)
          · exact Or.inr (Or.inr hcycle1)
          · exact Or.inl hcycle2
        · intro hy
          rw [gsmul] at hy
          rcases hy with hy | hy | hy
          · exact Or.inr (Or.inr (by
              calc
                y = -b + (b + y) := by abel
                _ = -b + x := by rw [hy]
                _ = x - b := by abel))
          · exact Or.inl (by
              calc
                y = -b + (b + y) := by abel
                _ = -b + (x + b) := by rw [hy]
                _ = x := by abel)
          · exact Or.inr (Or.inl (by
              calc
                y = -b + (b + y) := by abel
                _ = -b + (x - b) := by rw [hy]
                _ = x + (-b - b) := by abel
                _ = x + b := by rw [char_three_neg_sub_self]))
  · let a : Fq d := g.right.1.1
    let b : Fq d := g.left.toAdd
    have ha1 : a ≠ 1 := by
      intro ha
      apply hright
      apply Subtype.ext
      apply Units.ext
      exact ha
    let x0 : Fq d := b / (1 - a)
    have hden : 1 - a ≠ 0 := sub_ne_zero.mpr ha1.symm
    have hfixed : g • x0 = x0 := by
      rw [Saxl.affine_smul_def, cq_smul_eq_mul]
      change b + a * (b / (1 - a)) = b / (1 - a)
      field_simp
      ring
    by_cases hx0 : x0 = 0
    · have hb0 : b = 0 := by
        simpa [x0, hden] using hx0
      refine {
        carrier := cqValueFinset d
        avoids := zero_not_mem_cqValueFinset d
        odd_card := odd_card_cqValueFinset d hd
        invariant := ?_ }
      intro y
      apply cqValueFinset_invariant_of_left_eq_zero d g
      exact hb0
    · refine {
        carrier := {x0}
        avoids := by simpa [eq_comm] using hx0
        odd_card := by simp
        invariant := ?_ }
      intro y
      simp only [Finset.mem_singleton]
      constructor
      · rintro rfl
        exact hfixed
      · intro hy
        apply (smul_left_cancel_iff g).mp
        rw [hy, hfixed]

end SaxlCounterexamples.EveryBase

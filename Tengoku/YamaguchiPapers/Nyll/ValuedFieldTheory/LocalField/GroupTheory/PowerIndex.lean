/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.SetTheory.Cardinal.Finite
import Tengoku.Seed.Algebra.Group.Subgroup.Ker
import Tengoku.Seed.Algebra.Group.Hom.Basic
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.GroupTheory.IntegerMultipleSubgroup
import Tengoku.Seed.RingTheory.RootsOfUnity.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Power indices in commutative groups

Reusable kernel, quotient, product, and additive-transport formulas for
`n`-th powers in commutative groups.  The basic power map and its image and
kernel are mathlib's `powMonoidHom`, `MonoidHom.range`, and `MonoidHom.ker`.
-/

noncomputable section

namespace LocalFieldTheory

open LocalFieldTheory.DiscreteValuationField
open scoped Int

section NthPowers

universe uG uH uU

variable (G : Type uG) (H : Type uH) (U : Type uU)
variable [CommGroup G] [CommGroup H] [CommGroup U]

/-- The identity element is an `n`-th power and hence lies in the range of the power endomorphism.
The identity element is an `n`-th power and hence lies in the range of the power endomorphism.-/
@[simp]
theorem powMonoidHom_range_one_mem (n : ℕ) :
    (1 : G) ∈ (powMonoidHom n : G →* G).range := by
  rw [MonoidHom.mem_range]
  exact ⟨1, one_pow n⟩

/-- A multiplicative equivalence transports `n`-torsion kernels.-/
def nthPowerKernelEquivOfMulEquiv (n : ℕ) (e : G ≃* H) :
    (powMonoidHom n : G →* G).ker ≃* (powMonoidHom n : H →* H).ker where
  toFun x :=
    ⟨e (x : G), by
      have hx : (x : G) ^ n = 1 :=
        (MonoidHom.mem_ker (G := G)).1 x.property
      change (e (x : G)) ^ n = 1
      simpa [map_pow] using congrArg e hx⟩
  invFun y :=
    ⟨e.symm (y : H), by
      have hy : (y : H) ^ n = 1 :=
        (MonoidHom.mem_ker (G := H)).1 y.property
      change (e.symm (y : H)) ^ n = 1
      simpa [map_pow] using congrArg e.symm hy⟩
  left_inv x := Subtype.ext (e.symm_apply_apply (x : G))
  right_inv y := Subtype.ext (e.apply_symm_apply (y : H))
  map_mul' x y := Subtype.ext (map_mul e (x : G) (y : G))

/-- A multiplicative equivalence carries the range of the `n`-th power map onto the corresponding
range.-/
theorem powMonoidHom_range_map (n : ℕ) (e : G ≃* H) :
    ((powMonoidHom n : G →* G).range).map e.toMonoidHom = (powMonoidHom n : H →* H).range := by
  exact e.map_range_powMonoidHom n

/-- A multiplicative equivalence transports quotients by `n`-th powers.-/
def nthPowerQuotientEquivOfMulEquiv (n : ℕ) (e : G ≃* H) :
    G ⧸ (powMonoidHom n : G →* G).range ≃* H ⧸ (powMonoidHom n : H →* H).range :=
  QuotientGroup.congr ((powMonoidHom n : G →* G).range) ((powMonoidHom n : H →* H).range) e
    (powMonoidHom_range_map G H n e)

/-- The quotient equivalence induced by a multiplicative equivalence maps each power-class
representative to its image.-/
@[simp]
theorem nthPowerQuotientEquivOfMulEquiv_mk (n : ℕ) (e : G ≃* H) (x : G) :
    nthPowerQuotientEquivOfMulEquiv G H n e
        (QuotientGroup.mk' ((powMonoidHom n : G →* G).range) x) =
      QuotientGroup.mk' ((powMonoidHom n : H →* H).range) (e x) :=
  rfl

/-- The `n`-torsion kernel of a product is the product of the two
`n`-torsion kernels.-/
def nthPowerKernelProductEquiv (n : ℕ) :
    (powMonoidHom n : (G × H) →* (G × H)).ker ≃*
      (powMonoidHom n : G →* G).ker × (powMonoidHom n : H →* H).ker where
  toFun x :=
    (⟨(x : G × H).1, by
        have hx : (x : G × H) ^ n = 1 :=
          (MonoidHom.mem_ker (G := G × H)).1 x.property
        have hfst := congrArg Prod.fst hx
        simpa using hfst⟩,
      ⟨(x : G × H).2, by
        have hx : (x : G × H) ^ n = 1 :=
          (MonoidHom.mem_ker (G := G × H)).1 x.property
        have hsnd := congrArg Prod.snd hx
        simpa using hsnd⟩)
  invFun x :=
    ⟨((x.1 : G), (x.2 : H)), by
      have hx₁ : (x.1 : G) ^ n = 1 :=
        (MonoidHom.mem_ker (G := G)).1 x.1.property
      have hx₂ : (x.2 : H) ^ n = 1 :=
        (MonoidHom.mem_ker (G := H)).1 x.2.property
      change (((x.1 : G), (x.2 : H)) : G × H) ^ n = 1
      ext <;> simp [hx₁, hx₂]⟩
  left_inv x := by
    ext <;> rfl
  right_inv x := by
    ext <;> rfl
  map_mul' x y := by
    ext <;> rfl

/-- The product map from a product group to the product of its `n`-th-power
quotients.-/
def nthPowerProductQuotientHom (n : ℕ) :
    G × H →* (G ⧸ (powMonoidHom n : G →* G).range) × (H ⧸ (powMonoidHom n : H →* H).range) where
  toFun x :=
    (QuotientGroup.mk' ((powMonoidHom n : G →* G).range) x.1,
      QuotientGroup.mk' ((powMonoidHom n : H →* H).range) x.2)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Every pair of power classes is represented by a power class in the product group.-/
theorem nthPowerProductQuotientHom_surjective (n : ℕ) :
    Function.Surjective (nthPowerProductQuotientHom G H n) := by
  intro q
  rcases q with ⟨qG, qH⟩
  refine Quotient.inductionOn' qG ?_
  intro g
  refine Quotient.inductionOn' qH ?_
  intro h
  exact ⟨(g, h), rfl⟩

/-- The product power-class homomorphism has trivial kernel.-/
theorem nthPowerProductQuotientHom_ker (n : ℕ) :
    (nthPowerProductQuotientHom G H n).ker =
      (powMonoidHom n : (G × H) →* (G × H)).range := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    change
      (QuotientGroup.mk' ((powMonoidHom n : G →* G).range) x.1,
        QuotientGroup.mk' ((powMonoidHom n : H →* H).range) x.2) = 1 at hx
    have hxG :
        QuotientGroup.mk' ((powMonoidHom n : G →* G).range) x.1 = 1 :=
      congrArg Prod.fst hx
    have hxH :
        QuotientGroup.mk' ((powMonoidHom n : H →* H).range) x.2 = 1 :=
      congrArg Prod.snd hx
    have hxGmem : x.1 ∈ (powMonoidHom n : G →* G).range :=
      (QuotientGroup.eq_one_iff x.1).1 hxG
    have hxHmem : x.2 ∈ (powMonoidHom n : H →* H).range :=
      (QuotientGroup.eq_one_iff x.2).1 hxH
    rw [MonoidHom.mem_range] at hxGmem hxHmem ⊢
    rcases hxGmem with ⟨g, hg⟩
    rcases hxHmem with ⟨h, hh⟩
    refine ⟨(g, h), ?_⟩
    ext
    · change g ^ n = x.1
      simpa only [powMonoidHom_apply] using hg
    · change h ^ n = x.2
      simpa only [powMonoidHom_apply] using hh
  · intro hx
    rw [MonoidHom.mem_ker]
    rw [MonoidHom.mem_range] at hx
    rcases hx with ⟨y, rfl⟩
    apply Prod.ext
    · exact (QuotientGroup.eq_one_iff ((y.1) ^ n)).2
        ((MonoidHom.mem_range (G := G)).2 ⟨y.1, rfl⟩)
    · exact (QuotientGroup.eq_one_iff ((y.2) ^ n)).2
        ((MonoidHom.mem_range (G := H)).2 ⟨y.2, rfl⟩)

/-- Quotienting a product by `n`-th powers is the product of the two
`n`-th-power quotients.-/
def nthPowerProductQuotientEquiv (n : ℕ) :
    (G × H) ⧸ (powMonoidHom n : (G × H) →* (G × H)).range ≃*
      (G ⧸ (powMonoidHom n : G →* G).range) × (H ⧸ (powMonoidHom n : H →* H).range) :=
  (QuotientGroup.quotientMulEquivOfEq
      (nthPowerProductQuotientHom_ker G H n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (nthPowerProductQuotientHom G H n)
      (nthPowerProductQuotientHom_surjective G H n))

/-- For multiplicative integers, the range of the `n`-th power map is the subgroup of additive
multiples of `n`.-/
theorem powMonoidHom_range_multiplicativeInt_eq_integerMultipleSubgroup
    (n : ℕ) :
    (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range =
      integerMultipleSubgroup (n : ℤ) := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_range] at hx
    rcases hx with ⟨y, rfl⟩
    rw [mem_integerMultipleSubgroup_iff, powMonoidHom_apply, Int.toAdd_pow]
    exact ⟨y.toAdd, by ring⟩
  · intro hx
    rw [mem_integerMultipleSubgroup_iff] at hx
    rcases hx with ⟨k, hk⟩
    rw [MonoidHom.mem_range]
    refine ⟨Multiplicative.ofAdd k, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [powMonoidHom_apply, Int.toAdd_pow, toAdd_ofAdd, hk]
    ring

/-- For nonzero `n`, multiplicative integers modulo `n`-th powers form a finite quotient.-/
theorem finite_multiplicativeInt_nthPowerQuotient
    {n : ℕ} (hn : n ≠ 0) :
    Finite (Multiplicative ℤ ⧸ (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative
      ℤ)).range) := by
  rw [powMonoidHom_range_multiplicativeInt_eq_integerMultipleSubgroup]
  have hnabs : (n : ℤ).natAbs ≠ 0 := by simpa using hn
  let : NeZero (n : ℤ).natAbs := ⟨hnabs⟩
  exact Finite.of_equiv
    (Multiplicative (ZMod (n : ℤ).natAbs))
    (valueModIntegerMultipleSubgroupEquivZMod (n : ℤ)).symm.toEquiv

/-- For nonzero `n`, the multiplicative-integer power quotient has cardinality `n`.-/
theorem card_multiplicativeInt_nthPowerQuotient
    {n : ℕ} (hn : n ≠ 0)
    [Finite (Multiplicative ℤ ⧸ (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range)]
      :
    Nat.card
        (Multiplicative ℤ ⧸ (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range)
          = n := by
  rw [Nat.card_congr
    ((QuotientGroup.quotientMulEquivOfEq
      (powMonoidHom_range_multiplicativeInt_eq_integerMultipleSubgroup n)).trans
        (valueModIntegerMultipleSubgroupEquivZMod (n : ℤ))).toEquiv]
  rw [Nat.card_congr
    (Multiplicative.toAdd :
      Multiplicative (ZMod ((n : ℤ).natAbs)) ≃ ZMod ((n : ℤ).natAbs))]
  have hnabs : (n : ℤ).natAbs ≠ 0 := by simpa using hn
  let : NeZero (n : ℤ).natAbs := ⟨hnabs⟩
  have hcard : Nat.card (ZMod ((n : ℤ).natAbs)) = (n : ℤ).natAbs :=
    Nat.card_zmod ((n : ℤ).natAbs)
  simpa only [Int.natAbs_natCast] using hcard

end NthPowers

section AdditivePowers

universe uA uB uG

variable (A : Type uA) [AddCommGroup A]

/-- The additive homomorphism `x ↦ n • x`.-/
abbrev nsmulAddHom (n : ℕ) : A →+ A :=
  nsmulAddMonoidHom n

/-- The additive subgroup of `n`-fold multiples.-/
abbrev nsmulAddSubgroup (n : ℕ) : AddSubgroup A :=
  (nsmulAddMonoidHom n).range

/-- The additive subgroup killed by `x ↦ n • x`.-/
abbrev nsmulAddKernel (n : ℕ) : AddSubgroup A :=
  (nsmulAddMonoidHom n).ker

/-- Membership in the image of multiplication by `n` is equivalent to being an `n`-fold additive
multiple.-/
@[simp]
theorem mem_nsmulAddSubgroup_iff {n : ℕ} {x : A} :
    x ∈ nsmulAddSubgroup A n ↔ ∃ y : A, n • y = x := by
  simp [nsmulAddSubgroup, AddMonoidHom.mem_range]

/-- Membership in the kernel of multiplication by `n` is equivalent to being annihilated by `n`.-/
@[simp]
theorem mem_nsmulAddKernel_iff {n : ℕ} {x : A} :
    x ∈ nsmulAddKernel A n ↔ n • x = 0 := by
  simp [nsmulAddKernel, AddMonoidHom.mem_ker]

/-- Under the `Multiplicative` wrapper, `n`-th powers are exactly additive
`n`-fold multiples.-/
theorem powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup
    (n : ℕ) :
    (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range =
      AddSubgroup.toSubgroup (nsmulAddSubgroup A n) := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_range] at hx
    rcases hx with ⟨y, rfl⟩
    exact (mem_nsmulAddSubgroup_iff A).2 ⟨Multiplicative.toAdd y, rfl⟩
  · intro hx
    rw [MonoidHom.mem_range]
    have hxadd : Multiplicative.toAdd x ∈ nsmulAddSubgroup A n := by
      simpa using hx
    rw [mem_nsmulAddSubgroup_iff] at hxadd
    rcases hxadd with ⟨y, hy⟩
    refine ⟨Multiplicative.ofAdd y, ?_⟩
    apply Multiplicative.toAdd.injective
    simp [hy]

/-- The underlying quotient types in multiplicative and additive notation
are canonically equivalent.-/
def multiplicativeNthPowerQuotientEquivAdditive (n : ℕ) :
    (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range) ≃
      (A ⧸ nsmulAddSubgroup A n) := by
  rw [powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup]
  exact Equiv.refl _

/-- Cardinality/index form of
`powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup`.-/
theorem card_multiplicative_nthPowerQuotient_eq_nsmulAddSubgroup_index
    (n : ℕ)
    [Finite (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range)]
      :
    Nat.card (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range)
      =
      (nsmulAddSubgroup A n).index := by
  rw [← Subgroup.index_eq_card
    (H := (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range)]
  rw [powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup]
  exact AddSubgroup.index_toSubgroup _

/-- Under logarithmic/additive notation, the `n`-th-power quotient is the
additive quotient by `n`-fold multiples.-/
theorem card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient
    (n : ℕ)
    [Finite (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range)]
    [Finite (A ⧸ nsmulAddSubgroup A n)] :
    Nat.card (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range)
      =
      Nat.card (A ⧸ nsmulAddSubgroup A n) := by
  rw [card_multiplicative_nthPowerQuotient_eq_nsmulAddSubgroup_index]
  rw [AddSubgroup.index_eq_card]

/-- Under the `Multiplicative` wrapper, `n`-torsion is exactly the additive
kernel of `x ↦ n • x`.-/
theorem powMonoidHom_ker_multiplicative_eq_nsmulAddKernel_toSubgroup
    (n : ℕ) :
    (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker =
      AddSubgroup.toSubgroup (nsmulAddKernel A n) := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    change Multiplicative.toAdd x ∈ nsmulAddKernel A n
    rw [mem_nsmulAddKernel_iff]
    have h := congrArg Multiplicative.toAdd hx
    simpa using h
  · intro hx
    have hxadd : Multiplicative.toAdd x ∈ nsmulAddKernel A n := by
      simpa using hx
    rw [mem_nsmulAddKernel_iff] at hxadd
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    simpa using hxadd

/-- The multiplicative power kernel and additive scalar kernel have the same
underlying type.-/
def multiplicativeNthPowerKernelEquivAdditive (n : ℕ) :
    (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker ≃ nsmulAddKernel A n := by
  rw [powMonoidHom_ker_multiplicative_eq_nsmulAddKernel_toSubgroup]
  exact Equiv.refl _

section AdditiveProducts

variable (B : Type uB) [AddCommGroup B]

end AdditiveProducts

variable (G : Type uG) [CommGroup G]

end AdditivePowers

end LocalFieldTheory

end

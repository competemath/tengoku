/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.Units
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.GroupTheory.IntegerMultipleSubgroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integer-valued norm data

This file contains the norm-subgroup lemmas used in local CFT from an abstract
integer-valued multiplicative valuation and a norm homomorphism satisfying the
standard valuation formula.
-/

namespace LocalFieldTheory

noncomputable section

universe u v

namespace DiscreteValuationField

/-- A multiplicative group valuation with values in additive integers.-/
structure MultiplicativeIntegerValuation (G : Type u) [Group G] where
  /-- The integer valuation of a group element.-/
  val : G → ℤ
  /-- The identity has valuation zero.-/
  map_one : val 1 = 0
  /-- Valuation turns multiplication into integer addition.-/
  map_mul : ∀ x y : G, val (x * y) = val x + val y

namespace MultiplicativeIntegerValuation

variable {G : Type u} [Group G] (V : MultiplicativeIntegerValuation G)

/-- Establishes the identity `V.val (1 : G) = 0`.
@isnad1 id=eq.0h2v.s5.0deab9b79d19 from=translated src=- shape=0184ac47 vocab=5deb39d8
-/
@[simp] theorem val_one : V.val (1 : G) = 0 :=
  V.map_one

/-- `val` satisfies the multiplication formula `V.val (x * y) = V.val x + V.val y`.
@isnad1 id=eq.0h4v.s5.e8141ce61ae2 from=translated src=- shape=cf58db91 vocab=8139486c
-/
@[simp] theorem val_mul (x y : G) :
    V.val (x * y) = V.val x + V.val y :=
  V.map_mul x y

/-- The integer-valued valuation as a multiplicative homomorphism to the
additive group of integers written multiplicatively.-/
def valuationHom : G →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (V.val x)
  map_one' := by
    simp [V.val_one]
  map_mul' x y := by
    rw [V.val_mul, ofAdd_add]

/--
The defining evaluation formula for `valuationHom` is `V.valuationHom x = Multiplicative.ofAdd
(V.val x)`.
@isnad1 id=eq.0h3v.s6.eed8abef5eb7 from=translated src=- shape=4515eca9 vocab=58bd8d92
-/
@[simp] theorem valuationHom_apply (x : G) :
    V.valuationHom x = Multiplicative.ofAdd (V.val x) :=
  rfl

/-- Characterizes `x ∈ V.valuationHom.ker` by the equivalent condition `V.val x = 0`.
@isnad1 id=iff.0h3v.s5.381a360ef525 from=translated src=- shape=06ba1b8a vocab=980ddf38
-/
theorem mem_valuationHom_ker_iff (x : G) :
    x ∈ V.valuationHom.ker ↔ V.val x = 0 := by
  change V.valuationHom x = 1 ↔ V.val x = 0
  rw [V.valuationHom_apply]
  constructor
  · intro hx
    exact Multiplicative.ofAdd.injective (by simpa using hx)
  · intro hx
    exact congrArg Multiplicative.ofAdd hx

/-- `val` satisfies the inverse formula `V.val x⁻¹ = -V.val x`.
@isnad1 id=eq.0h3v.s5.e6b1d70b83c4 from=translated src=- shape=9145a8e7 vocab=fec99e65
-/
@[simp] theorem val_inv (x : G) :
    V.val x⁻¹ = -V.val x := by
  have h := V.map_mul x x⁻¹
  have h' : V.val x + V.val x⁻¹ = 0 := by
    simpa [V.map_one] using h.symm
  exact eq_neg_iff_add_eq_zero.2 (by simpa [add_comm] using h')

/-- `val` satisfies the division formula `V.val (x / y) = V.val x - V.val y`.
@isnad1 id=eq.0h4v.s5.4363e5ce6330 from=translated src=- shape=cf58db91 vocab=ded6f80f
-/
@[simp] theorem val_div (x y : G) :
    V.val (x / y) = V.val x - V.val y := by
  rw [div_eq_mul_inv, V.val_mul, V.val_inv, sub_eq_add_neg]

/-- `val` satisfies the natural-power formula `V.val (x ^ n) = (n : ℤ) * V.val x`.
@isnad1 id=eq.0h4v.s5.f3f3a53ab727 from=translated src=- shape=5ee40268 vocab=d46fad74
-/
@[simp] theorem val_pow (x : G) (n : ℕ) :
    V.val (x ^ n) = (n : ℤ) * V.val x := by
  induction n with
  | zero =>
      rw [pow_zero, V.val_one, Nat.cast_zero, zero_mul]
  | succ n ih =>
      calc
        V.val (x ^ Nat.succ n) = V.val (x ^ n * x) := by
            rw [pow_succ]
        _ = V.val (x ^ n) + V.val x := V.val_mul _ _
        _ = (n : ℤ) * V.val x + V.val x := by
            rw [ih]
        _ = ((n : ℤ) + 1) * V.val x := by
            rw [add_mul, one_mul]
        _ = (Nat.succ n : ℤ) * V.val x := by
            rw [Nat.cast_succ]

/-- `val` satisfies the integer-power formula `V.val (x ^ n) = n * V.val x`.
@isnad1 id=eq.0h4v.s5.c6c791e8447d from=translated src=- shape=bd8f9c47 vocab=f72688d5
-/
@[simp] theorem val_zpow (x : G) (n : ℤ) :
    V.val (x ^ n) = n * V.val x := by
  cases n with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, V.val_pow]
  | negSucc n =>
      rw [zpow_negSucc, V.val_inv, V.val_pow]
      change -(((n + 1 : ℕ) : ℤ) * V.val x) =
        -(((n + 1 : ℕ) : ℤ)) * V.val x
      rw [neg_mul]

/-- Establishes the identity `V.val x⁻¹ = 0`.
@isnad1 id=eq.1h3v.s5.a0672231b95b from=translated src=- shape=8a7656c5 vocab=525576fd
-/
theorem val_inv_eq_zero_of_val_eq_zero {x : G} (hx : V.val x = 0) :
    V.val x⁻¹ = 0 := by
  rw [V.val_inv, hx, neg_zero]

/-- Characterizes `V.val (x / y) = 0` by the equivalent condition `V.val x = V.val y`.
@isnad1 id=iff.0h4v.s5.caffb8b981e2 from=translated src=- shape=cf2f0fcf vocab=a7847dbf
-/
theorem val_div_eq_zero_iff (x y : G) :
    V.val (x / y) = 0 ↔ V.val x = V.val y := by
  rw [V.val_div]
  constructor
  · exact sub_eq_zero.mp
  · exact sub_eq_zero.mpr

/-- Elements of valuation zero.-/
def zeroSubgroup : Subgroup G where
  carrier := {x | V.val x = 0}
  one_mem' := by simp [V.map_one]
  mul_mem' := by
    intro x y hx hy
    change V.val (x * y) = 0
    rw [V.map_mul, hx, hy, add_zero]
  inv_mem' := by
    intro x hx
    exact V.val_inv_eq_zero_of_val_eq_zero hx

/-- Characterizes `x ∈ V.zeroSubgroup` by the equivalent condition `V.val x = 0`.
@isnad1 id=iff.0h3v.s5.a5a3a8f4663d from=translated src=- shape=70c60267 vocab=77a0970d
-/
@[simp] theorem mem_zeroSubgroup_iff (x : G) :
    x ∈ V.zeroSubgroup ↔ V.val x = 0 :=
  Iff.rfl

/-- Establishes the identity `V.valuationHom.ker = V.zeroSubgroup`.
@isnad1 id=eq.0h2v.s4.dfe0855da8a7 from=translated src=- shape=34a04414 vocab=4a0f6cd1
-/
theorem valuationHom_ker_eq_zeroSubgroup :
    V.valuationHom.ker = V.zeroSubgroup := by
  ext x
  rw [V.mem_valuationHom_ker_iff, V.mem_zeroSubgroup_iff]

/-- The subgroup appearing in `(V.zeroSubgroup).Normal` is normal.
@isnad1 id=normal.0h2v.s4.85909e8bd918 from=translated src=- shape=ed10201d vocab=38d780a1
-/
instance zeroSubgroup_normal : (V.zeroSubgroup).Normal := by
  rw [← V.valuationHom_ker_eq_zeroSubgroup]
  infer_instance

/-- The value subgroup of an integer-valued valuation.  It is the range of the
valuation homomorphism `valuationHom`.-/
def valueSubgroup : Subgroup (Multiplicative ℤ) :=
  V.valuationHom.range

/--
Characterizes `n ∈ V.valueSubgroup` by the equivalent condition `∃ x : G, V.valuationHom x = n`.
@isnad1 id=iff.0h3v.s6.2ae325cc5d5c from=translated src=- shape=6257bf56 vocab=162a9f83
-/
@[simp] theorem mem_valueSubgroup_iff (n : Multiplicative ℤ) :
    n ∈ V.valueSubgroup ↔ ∃ x : G, V.valuationHom x = n :=
  Iff.rfl

/-- Establishes the identity `V.valueSubgroup = ⊤`.
@isnad1 id=eq.1h2v.s5.c4132d04a63d from=translated src=- shape=9bfd8d36 vocab=caafed9c
-/
theorem valueSubgroup_eq_top_of_surjective (hV : Function.Surjective V.val) :
    V.valueSubgroup = ⊤ := by
  ext n
  constructor
  · intro hn
    trivial
  · intro hn
    rcases hV (Multiplicative.toAdd n) with ⟨x, hx⟩
    rw [V.mem_valueSubgroup_iff n]
    exact ⟨x, by rw [V.valuationHom_apply, hx, ofAdd_toAdd]⟩

/-- First-isomorphism-theorem form for an integer-valued valuation:
the quotient by valuation-zero elements is the value subgroup.-/
noncomputable def quotientZeroSubgroupEquivValueSubgroup :
    G ⧸ V.zeroSubgroup ≃* V.valueSubgroup :=
  (QuotientGroup.quotientMulEquivOfEq
      (V.valuationHom_ker_eq_zeroSubgroup).symm).trans
    (QuotientGroup.quotientKerEquivRange V.valuationHom)

/--
Establishes the identity `V.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk'
V.zeroSubgroup x) = V.valuationHom.rangeRestrict x`.
@isnad1 id=eq.0h3v.s10.671583efe1ad from=translated src=- shape=f8fda433 vocab=33f256f3
-/
@[simp] theorem quotientZeroSubgroupEquivValueSubgroup_mk (x : G) :
    V.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' V.zeroSubgroup x) =
      V.valuationHom.rangeRestrict x :=
  rfl

/--
Establishes the identity `((V.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk'
V.zeroSubgroup x) : V.valueSubgroup) : Multiplicative ℤ) = Multiplicative.ofAdd (V.val x)`.
@isnad1 id=eq.0h3v.s9.b3bc4986e37d from=translated src=- shape=9d4aca8b vocab=5e17c4f2
-/
@[simp] theorem coe_quotientZeroSubgroupEquivValueSubgroup_mk (x : G) :
    ((V.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' V.zeroSubgroup x) : V.valueSubgroup) :
      Multiplicative ℤ) =
      Multiplicative.ofAdd (V.val x) := by
  rw [V.quotientZeroSubgroupEquivValueSubgroup_mk]
  rfl

/--
Establishes the identity `Multiplicative.toAdd (((V.quotientZeroSubgroupEquivValueSubgroup
(QuotientGroup.mk' V.zeroSubgroup x) : V.valueSubgroup) : Multiplicative ℤ)) = V.val x`.
@isnad1 id=eq.0h3v.s9.e3dfc798e9d3 from=translated src=- shape=925e2bbb vocab=92b6dabb
-/
@[simp] theorem toAdd_quotientZeroSubgroupEquivValueSubgroup_mk (x : G) :
    Multiplicative.toAdd
      (((V.quotientZeroSubgroupEquivValueSubgroup
          (QuotientGroup.mk' V.zeroSubgroup x) : V.valueSubgroup) :
        Multiplicative ℤ)) = V.val x := by
  rw [V.coe_quotientZeroSubgroupEquivValueSubgroup_mk, toAdd_ofAdd]

/--
Establishes the identity `Multiplicative.toAdd (((V.quotientZeroSubgroupEquivValueSubgroup
(QuotientGroup.mk' V.zeroSubgroup (x / y)) : V.valueSubgroup) : Multiplicative ℤ)) = V.val x -
V.val y`.
@isnad1 id=eq.0h4v.s9.66467a7c4db6 from=translated src=- shape=75219523 vocab=10ff22b7
-/
@[simp] theorem toAdd_quotientZeroSubgroupEquivValueSubgroup_div_mk
    (x y : G) :
    Multiplicative.toAdd
      (((V.quotientZeroSubgroupEquivValueSubgroup
          (QuotientGroup.mk' V.zeroSubgroup (x / y)) : V.valueSubgroup) :
        Multiplicative ℤ)) = V.val x - V.val y := by
  rw [V.toAdd_quotientZeroSubgroupEquivValueSubgroup_mk, V.val_div]

/-- If the valuation is surjective, the quotient by valuation-zero elements is
the full multiplicative copy of `ℤ`.-/
noncomputable def quotientZeroSubgroupEquivMultiplicativeInt
    (hV : Function.Surjective V.val) :
    G ⧸ V.zeroSubgroup ≃* Multiplicative ℤ :=
  V.quotientZeroSubgroupEquivValueSubgroup.trans
    ((MulEquiv.subgroupCongr (V.valueSubgroup_eq_top_of_surjective hV)).trans
      Subgroup.topEquiv)

/-- A multiplicative element of valuation one.-/
def IsUniformizer (ϖ : G) : Prop :=
  V.val ϖ = 1

/-- Existence of a multiplicative element of valuation one.-/
def HasUniformizer : Prop :=
  ∃ ϖ : G, V.IsUniformizer ϖ

/-- `val_uniformizer` satisfies the integer-power formula `V.val (ϖ ^ n) = n`.
@isnad1 id=eq.1h4v.s5.30aabd64c75d from=translated src=- shape=b7cf707e vocab=0d761e0a
-/
@[simp] theorem val_uniformizer_zpow {ϖ : G} (hϖ : V.IsUniformizer ϖ)
    (n : ℤ) :
    V.val (ϖ ^ n) = n := by
  rw [V.val_zpow, hϖ, mul_one]

/-- `val_uniformizer` satisfies the natural-power formula `V.val (ϖ ^ n) = (n : ℤ)`.
@isnad1 id=eq.1h4v.s5.b330c600f9ec from=translated src=- shape=84d25537 vocab=b0ccc4ec
-/
@[simp] theorem val_uniformizer_pow {ϖ : G} (hϖ : V.IsUniformizer ϖ)
    (n : ℕ) :
    V.val (ϖ ^ n) = (n : ℤ) := by
  simpa using V.val_uniformizer_zpow hϖ (n : ℤ)

/-- The specified map is surjective: `Function.Surjective V.val`.
@isnad1 id=surjecti.1h3v.s4.20e1dc721882 from=translated src=- shape=c812eb1a vocab=afffb25d
-/
theorem val_surjective_of_uniformizer {ϖ : G} (hϖ : V.IsUniformizer ϖ) :
    Function.Surjective V.val := by
  intro n
  exact ⟨ϖ ^ n, V.val_uniformizer_zpow hϖ n⟩

/-- Uniformizer form of the quotient equivalence `G / G⁰ ≃ Multiplicative ℤ`.
The uniformizer proves that the value group is all of `ℤ`.-/
noncomputable def quotientZeroSubgroupEquivMultiplicativeIntOfUniformizer
    {ϖ : G} (hϖ : V.IsUniformizer ϖ) :
    G ⧸ V.zeroSubgroup ≃* Multiplicative ℤ :=
  V.quotientZeroSubgroupEquivMultiplicativeInt
    (V.val_surjective_of_uniformizer hϖ)

/--
`coe_quotientZeroSubgroupEquivValueSubgroup_uniformizer` satisfies the integer-power formula
`((V.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk' V.zeroSubgroup (ϖ ^ n)) :
V.valueSubgroup) : Multiplicative ℤ) = Multiplicative.ofAdd n`.
@isnad1 id=eq.1h4v.s9.cada0eeb6ef4 from=translated src=- shape=e2339f26 vocab=e8cf3bec
-/
@[simp] theorem coe_quotientZeroSubgroupEquivValueSubgroup_uniformizer_zpow
    {ϖ : G} (hϖ : V.IsUniformizer ϖ) (n : ℤ) :
    ((V.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' V.zeroSubgroup (ϖ ^ n)) : V.valueSubgroup) :
      Multiplicative ℤ) = Multiplicative.ofAdd n := by
  rw [V.coe_quotientZeroSubgroupEquivValueSubgroup_mk,
    V.val_uniformizer_zpow hϖ n]

/--
`toAdd_quotientZeroSubgroupEquivValueSubgroup_uniformizer` satisfies the integer-power formula
`Multiplicative.toAdd (((V.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk'
V.zeroSubgroup (ϖ ^ n)) : V.valueSubgroup) : Multiplicative ℤ)) = n`.
@isnad1 id=eq.1h4v.s9.bddabaf671b2 from=translated src=- shape=a9bfa497 vocab=b349183d
-/
@[simp] theorem toAdd_quotientZeroSubgroupEquivValueSubgroup_uniformizer_zpow
    {ϖ : G} (hϖ : V.IsUniformizer ϖ) (n : ℤ) :
    Multiplicative.toAdd
      (((V.quotientZeroSubgroupEquivValueSubgroup
          (QuotientGroup.mk' V.zeroSubgroup (ϖ ^ n)) : V.valueSubgroup) :
        Multiplicative ℤ)) = n := by
  rw [V.coe_quotientZeroSubgroupEquivValueSubgroup_uniformizer_zpow hϖ n,
    toAdd_ofAdd]

/-- A representative-level decomposition `x = u * ϖ^n`, with `u` of valuation
zero.  This is the abstract multiplicative form of `Kˣ = O_Kˣ · ϖ^ℤ`.-/
structure UnitUniformizerDecomposition (ϖ x : G) where
  /-- The valuation-zero factor.-/
  unitPart : G
  /-- The unit factor has valuation zero.-/
  unit_mem : unitPart ∈ V.zeroSubgroup
  /-- The exponent of the chosen uniformizer.-/
  exponent : ℤ
  /-- Reconstruction from the unit factor and uniformizer power.-/
  eq_unit_mul_zpow : x = unitPart * ϖ ^ exponent

/-- Every element admits a unit-uniformizer decomposition with respect to `ϖ`.-/
def HasUnitUniformizerDecomposition (ϖ : G) : Prop :=
  ∀ x : G, Nonempty (V.UnitUniformizerDecomposition ϖ x)

namespace UnitUniformizerDecomposition

variable {V : MultiplicativeIntegerValuation G} {ϖ x : G}

/-- Establishes the identity `V.val d.unitPart = 0`.
@isnad1 id=eq.0h5v.s5.e75de266a25e from=translated src=- shape=2e7bae24 vocab=28ab48ec
-/
@[simp] theorem unitPart_val_zero
    (d : V.UnitUniformizerDecomposition ϖ x) :
    V.val d.unitPart = 0 :=
  (V.mem_zeroSubgroup_iff d.unitPart).1 d.unit_mem

/-- A valuation-zero multiple of a uniformizer power has valuation equal to
the exponent.
@isnad1 id=eq.2h5v.s6.cab50f80a7af from=translated src=- shape=42c76315 vocab=98b1d44e
-/
theorem val_unit_mul_zpow (hϖ : V.IsUniformizer ϖ)
    {u : G} (hu : u ∈ V.zeroSubgroup) (n : ℤ) :
    V.val (u * ϖ ^ n) = n := by
  rw [V.val_mul, (V.mem_zeroSubgroup_iff u).1 hu,
    V.val_uniformizer_zpow hϖ n, zero_add]

/-- A uniformizer power has valuation equal to its exponent.
@isnad1 id=eq.1h4v.s5.30aabd64c75d from=translated src=- shape=b7cf707e vocab=0d761e0a
-/
theorem val_uniformizer_zpow (hϖ : V.IsUniformizer ϖ) (n : ℤ) :
    V.val (ϖ ^ n) = n :=
  V.val_uniformizer_zpow hϖ n

/-- A natural power of a uniformizer has valuation equal to the natural
exponent.
@isnad1 id=eq.1h4v.s5.b330c600f9ec from=translated src=- shape=84d25537 vocab=b0ccc4ec
-/
theorem val_uniformizer_pow (hϖ : V.IsUniformizer ϖ) (n : ℕ) :
    V.val (ϖ ^ n) = (n : ℤ) :=
  V.val_uniformizer_pow hϖ n

end UnitUniformizerDecomposition

/-- Establishes the identity `V.val (u * ϖ ^ n) = n`.
@isnad1 id=eq.2h5v.s6.15c2c7c8f69e from=translated src=- shape=98af8767 vocab=98b1d44e
-/
theorem valuation_uniformizer_normal_form {ϖ u : G}
    (hϖ : V.IsUniformizer ϖ) (hu : u ∈ V.zeroSubgroup) (n : ℤ) :
    V.val (u * ϖ ^ n) = n :=
  UnitUniformizerDecomposition.val_unit_mul_zpow hϖ hu n

/-- Characterizes `x / y ∈ V.zeroSubgroup` by the equivalent condition `V.val x = V.val y`.
@isnad1 id=iff.0h4v.s5.3f8cefe95beb from=translated src=- shape=047d9c60 vocab=8a5b73df
-/
theorem div_mem_zeroSubgroup_iff (x y : G) :
    x / y ∈ V.zeroSubgroup ↔ V.val x = V.val y := by
  rw [MultiplicativeIntegerValuation.mem_zeroSubgroup_iff V (x / y),
    V.val_div_eq_zero_iff]

/-- Two elements have quotient in the zero-valuation subgroup exactly when the
left element is the right element multiplied on the left by a zero-valuation
element.  This is the right-coset representative form used in
`Kˣ / O_Kˣ` calculations.
@isnad1 id=iff.0h4v.s6.ca90f8bdc737 from=translated src=- shape=52771f6a vocab=e42d4adc
-/
theorem div_mem_zeroSubgroup_iff_exists_zeroSubgroup_mul_eq (x y : G) :
    x / y ∈ V.zeroSubgroup ↔
      ∃ u : G, u ∈ V.zeroSubgroup ∧ u * y = x := by
  constructor
  · intro hxy
    exact ⟨x / y, hxy, by simp [div_eq_mul_inv, mul_assoc]⟩
  · rintro ⟨u, hu, hux⟩
    have hu_eq : u = x / y := by
      have h := congrArg (fun t : G => t * y⁻¹) hux
      simpa [div_eq_mul_inv, mul_assoc] using h
    simpa [← hu_eq] using hu

/--
Characterizes `V.val x = V.val y` by the equivalent condition `∃ u : G, u ∈ V.zeroSubgroup ∧ u * y
= x`.
@isnad1 id=iff.0h4v.s6.8eb323fd0388 from=translated src=- shape=d4337b4e vocab=72e61932
-/
theorem val_eq_iff_exists_zeroSubgroup_mul_eq (x y : G) :
    V.val x = V.val y ↔
      ∃ u : G, u ∈ V.zeroSubgroup ∧ u * y = x := by
  rw [← V.div_mem_zeroSubgroup_iff x y,
    V.div_mem_zeroSubgroup_iff_exists_zeroSubgroup_mul_eq x y]

/-- Establishes the identity `∃ u : G, u ∈ V.zeroSubgroup ∧ u * y = x`.
@isnad1 id=ex.1h4v.s6.8a6e1d7524cd from=translated src=- shape=9b85b115 vocab=72e61932
-/
theorem exists_zeroSubgroup_mul_eq_of_val_eq {x y : G}
    (hxy : V.val x = V.val y) :
    ∃ u : G, u ∈ V.zeroSubgroup ∧ u * y = x :=
  (V.val_eq_iff_exists_zeroSubgroup_mul_eq x y).1 hxy

end MultiplicativeIntegerValuation

/-- A norm-like homomorphism compatible with integer-valued valuations.

`residueDegree` is proof-attached data: it is the multiplier in
`valuation_formula`, not an independent field-extension invariant.  In the
usual discrete-valued application the source has a uniformizer, and evaluating
`valuation_formula` at that uniformizer uniquely determines this coefficient.
The generic group-level abstraction does not require a uniformizer, so it keeps
the coefficient together with the formula that certifies it.-/
structure ValuedNorm {G : Type u} {H : Type v} [Group G] [Group H]
    (vG : MultiplicativeIntegerValuation G)
    (vH : MultiplicativeIntegerValuation H) where
  /-- The multiplicative norm homomorphism.-/
  toHom : H →* G
  /-- The nonnegative scaling factor in the valuation formula.-/
  residueDegree : ℕ
  /-- Applying the norm scales valuation by the residue-degree factor.-/
  valuation_formula :
    ∀ x : H, vG.val (toHom x) = (residueDegree : ℤ) * vH.val x

end DiscreteValuationField

end

end LocalFieldTheory

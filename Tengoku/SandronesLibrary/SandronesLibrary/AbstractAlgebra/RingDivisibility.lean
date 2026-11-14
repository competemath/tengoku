/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/FurinaManifold/sandrones-library@6bce6404b264, `SandronesLibrary/AbstractAlgebra/RingDivisibility.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# 交换整环中的整除理论

本模块以显式乘子和本库 `UnitElement` 定义整除、相伴、不可约元、素元与最大公因子，
并证明素元必不可约以及最大公因子在相伴意义下唯一。

> **Entry**: abstract-algebra.ring.divisibility
-/

namespace SandronesLibrary.AbstractAlgebra.Ring


/-- `a ∣ b` 的教材定义：存在乘子 `c` 使 `b = a*c`。-/
def DividesElement {R : Type*} [Mul R] (a b : R) : Prop :=
  ∃ c : R, b = a * c

/-- 两元素相伴：相差一个单位因子。-/
def AssociateElements {R : Type*} [One R] [Mul R] (a b : R) : Prop :=
  ∃ u : R, UnitElement u ∧ b = a * u

/-- 不可约元：非零、非单位，且任何二因子分解必有一个单位因子。-/
def IrreducibleElement {R : Type*} [Zero R] [One R] [Mul R] (p : R) : Prop :=
  p ≠ 0 ∧ ¬ UnitElement p ∧
    ∀ a b : R, p = a * b → UnitElement a ∨ UnitElement b

/-- 素元：非零、非单位，并满足整除乘积判据。-/
def PrimeElement {R : Type*} [Zero R] [One R] [Mul R] (p : R) : Prop :=
  p ≠ 0 ∧ ¬ UnitElement p ∧
    ∀ a b : R, DividesElement p (a * b) →
      DividesElement p a ∨ DividesElement p b

/-- `d` 是 `a,b` 的最大公因子：它是公因子，且被每个公因子整除。-/
def GreatestCommonDivisor {R : Type*} [Mul R] (d a b : R) : Prop :=
  DividesElement d a ∧ DividesElement d b ∧
    ∀ c : R, DividesElement c a → DividesElement c b → DividesElement c d

/-- 本库显式整除定义与 Lean 基础整除记号的具名桥。
@isnad1 id=iff.0h3v.s4.0bf84f2040ab from=translated src=- shape=865b2251 vocab=907932db
-/
theorem dividesElement_iff_dvd {R : Type*} [Semigroup R] {a b : R} :
    DividesElement a b ↔ a ∣ b := by
  exact dvd_def.symm

/--
@isnad1 id=dividese.0h2v.s4.c22ded0d80c6 from=translated src=- shape=e6608552 vocab=a9fe658c
-/
theorem dividesElement_refl {R : Type*} [Monoid R] (a : R) :
    DividesElement a a := by
  exact ⟨1, (mul_one a).symm⟩

/--
@isnad1 id=dividese.2h4v.s5.babcf1dfcb3a from=translated src=- shape=ed0e08c7 vocab=8ae5b50c
-/
theorem dividesElement_trans {R : Type*} [Semigroup R] {a b c : R}
    (hab : DividesElement a b) (hbc : DividesElement b c) :
    DividesElement a c := by
  obtain ⟨x, rfl⟩ := hab
  obtain ⟨y, rfl⟩ := hbc
  exact ⟨x * y, mul_assoc a x y⟩

/--
@isnad1 id=dividese.1h3v.s5.604a92781fa7 from=translated src=- shape=5a9a4837 vocab=52892e9a
-/
theorem unitElement_divides {R : Type*} [Monoid R] {u : R}
    (hu : UnitElement u) (a : R) : DividesElement u a := by
  obtain ⟨v, huv, hvu⟩ := hu
  refine ⟨v * a, ?_⟩
  calc
    a = 1 * a := (one_mul a).symm
    _ = (u * v) * a := by rw [huv]
    _ = u * (v * a) := mul_assoc u v a

/--
@isnad1 id=associat.0h2v.s4.c05f94a27b10 from=translated src=- shape=e6608552 vocab=5199422b
-/
theorem associateElements_refl {R : Type*} [Monoid R] (a : R) :
    AssociateElements a a := by
  exact ⟨1, ⟨1, mul_one 1, mul_one 1⟩, (mul_one a).symm⟩

/--
@isnad1 id=associat.1h3v.s5.8c218f41417c from=translated src=- shape=2da0c23b vocab=df7d2e4f
-/
theorem associateElements_symm {R : Type*} [CommMonoid R] {a b : R}
    (hab : AssociateElements a b) : AssociateElements b a := by
  obtain ⟨u, ⟨v, huv, hvu⟩, rfl⟩ := hab
  refine ⟨v, ⟨u, hvu, huv⟩, ?_⟩
  rw [mul_assoc, huv, mul_one]

/--
@isnad1 id=associat.2h4v.s6.2eae9b567eb8 from=translated src=- shape=ed0e08c7 vocab=df7d2e4f
-/
theorem associateElements_trans {R : Type*} [CommMonoid R] {a b c : R}
    (hab : AssociateElements a b) (hbc : AssociateElements b c) :
    AssociateElements a c := by
  obtain ⟨u, hu, rfl⟩ := hab
  obtain ⟨v, hv, rfl⟩ := hbc
  refine ⟨u * v, ?_, mul_assoc a u v⟩
  exact (unitElement_iff_isUnit (u * v)).mpr
    (((unitElement_iff_isUnit u).mp hu).mul ((unitElement_iff_isUnit v).mp hv))

/--
@isnad1 id=and.1h3v.s5.0508a0f935a7 from=translated src=- shape=421f8bea vocab=5e0ab2d9
-/
theorem associateElements_implies_mutual_divisibility
    {R : Type*} [CommMonoid R] {a b : R} (h : AssociateElements a b) :
    DividesElement a b ∧ DividesElement b a := by
  obtain ⟨u, hu, hbu⟩ := h
  constructor
  · exact ⟨u, hbu⟩
  · have hs := associateElements_symm (show AssociateElements a b from ⟨u, hu, hbu⟩)
    obtain ⟨v, _hv, hav⟩ := hs
    exact ⟨v, hav⟩

/-- 交换整环中互相整除的元素相伴。
@isnad1 id=associat.3h3v.s6.31af9a74cdab from=translated src=- shape=fa17130a vocab=71f4c927
-/
theorem mutual_divisibility_implies_associateElements
    {R : Type*} [CommRing R] (hR : IntegralDomainAxioms R) {a b : R}
    (hab : DividesElement a b) (hba : DividesElement b a) :
    AssociateElements a b := by
  letI : IsDomain R := (integralDomainAxioms_iff_isDomain (R := R)).mp hR
  obtain ⟨x, hbx⟩ := hab
  obtain ⟨y, hay⟩ := hba
  by_cases ha0 : a = 0
  · have hb0 : b = 0 := by rw [hbx, ha0, zero_mul]
    rw [ha0, hb0]
    exact associateElements_refl (0 : R)
  · have hxy : x * y = 1 := by
      apply mul_left_cancel₀ ha0
      calc
        a * (x * y) = (a * x) * y := (mul_assoc _ _ _).symm
        _ = b * y := by rw [← hbx]
        _ = a := hay.symm
        _ = a * 1 := (mul_one a).symm
    exact ⟨x, ⟨y, hxy, by simpa [mul_comm] using hxy⟩, hbx⟩

/-- 本库相伴定义与 Mathlib `Associated` 的兼容桥。
@isnad1 id=iff.1h3v.s6.2357ae8d628e from=translated src=- shape=579c48f1 vocab=b96ff8df
-/
theorem associateElements_iff_associated
    {R : Type*} [CommRing R] (hR : IntegralDomainAxioms R) {a b : R} :
    AssociateElements a b ↔ Associated a b := by
  letI : IsDomain R := (integralDomainAxioms_iff_isDomain (R := R)).mp hR
  constructor
  · intro h
    obtain ⟨hab, hba⟩ := associateElements_implies_mutual_divisibility h
    exact associated_of_dvd_dvd
      (dividesElement_iff_dvd.mp hab) (dividesElement_iff_dvd.mp hba)
  · intro h
    have hm : a ∣ b ∧ b ∣ a := dvd_dvd_iff_associated.mpr h
    exact mutual_divisibility_implies_associateElements hR
      (dividesElement_iff_dvd.mpr hm.1) (dividesElement_iff_dvd.mpr hm.2)

/--
@isnad1 id=irreduci.2h2v.s6.644a3b40efe3 from=translated src=- shape=b0c8cbfb vocab=9d541429
-/
theorem primeElement_implies_irreducibleElement
    {R : Type*} [CommRing R] (hR : IntegralDomainAxioms R) {p : R}
    (hp : PrimeElement p) : IrreducibleElement p := by
  letI : IsDomain R := (integralDomainAxioms_iff_isDomain (R := R)).mp hR
  refine ⟨hp.1, hp.2.1, ?_⟩
  intro a b hab
  have hpab : DividesElement p (a * b) := ⟨1, by rw [← hab, mul_one]⟩
  rcases hp.2.2 a b hpab with hpa | hpb
  · obtain ⟨c, hac⟩ := hpa
    have hpc : p = p * (c * b) := by
      calc
        p = a * b := hab
        _ = (p * c) * b := by rw [← hac]
        _ = p * (c * b) := mul_assoc _ _ _
    have hcb : c * b = 1 := by
      apply mul_left_cancel₀ hp.1
      simpa using hpc.symm
    exact Or.inr ⟨c, by simpa [mul_comm] using hcb, hcb⟩
  · obtain ⟨c, hbc⟩ := hpb
    have hac : a * c = 1 := by
      apply mul_left_cancel₀ hp.1
      calc
        p * (a * c) = (a * (p * c)) := by ac_rfl
        _ = a * b := by rw [← hbc]
        _ = p := hab.symm
        _ = p * 1 := (mul_one p).symm
    exact Or.inl ⟨c, hac, by simpa [mul_comm] using hac⟩

/-- 本库不可约元定义与 Mathlib `Irreducible` 的兼容桥。
@isnad1 id=iff.1h2v.s6.2442363313d5 from=translated src=- shape=c7f12f28 vocab=df1281e1
-/
theorem irreducibleElement_iff_irreducible
    {R : Type*} [CommRing R] (hR : IntegralDomainAxioms R) {p : R} :
    IrreducibleElement p ↔ Irreducible p := by
  letI : IsDomain R := (integralDomainAxioms_iff_isDomain (R := R)).mp hR
  rw [irreducible_iff]
  constructor
  · rintro ⟨_hp0, hpunit, hfac⟩
    exact ⟨fun hp ↦ hpunit ((unitElement_iff_isUnit p).mpr hp), fun a b hab ↦
      (hfac a b hab).imp
        (fun ha ↦ (unitElement_iff_isUnit a).mp ha)
        (fun hb ↦ (unitElement_iff_isUnit b).mp hb)⟩
  · rintro ⟨hpunit, hfac⟩
    have hpIrr : Irreducible p := irreducible_iff.mpr ⟨hpunit, hfac⟩
    exact ⟨hpIrr.ne_zero, fun hp ↦ hpunit ((unitElement_iff_isUnit p).mp hp),
      fun a b hab ↦ (hfac hab).imp
        (fun ha ↦ (unitElement_iff_isUnit a).mpr ha)
        (fun hb ↦ (unitElement_iff_isUnit b).mpr hb)⟩

/-- 本库素元定义与 Mathlib `Prime` 的兼容桥。
@isnad1 id=iff.0h2v.s5.7beb1a89a84b from=translated src=- shape=bc057928 vocab=3b3234e6
-/
theorem primeElement_iff_prime
    {R : Type*} [CommRing R] {p : R} :
    PrimeElement p ↔ Prime p := by
  unfold PrimeElement Prime
  constructor
  · rintro ⟨hp0, hpunit, hp⟩
    exact ⟨hp0, fun h ↦ hpunit ((unitElement_iff_isUnit p).mpr h), fun a b hab ↦
      (hp a b (dividesElement_iff_dvd.mpr hab)).imp
        dividesElement_iff_dvd.mp dividesElement_iff_dvd.mp⟩
  · rintro ⟨hp0, hpunit, hp⟩
    exact ⟨hp0, fun h ↦ hpunit ((unitElement_iff_isUnit p).mp h), fun a b hab ↦
      (hp a b (dividesElement_iff_dvd.mp hab)).imp
        dividesElement_iff_dvd.mpr dividesElement_iff_dvd.mpr⟩

/--
@isnad1 id=associat.3h5v.s6.ffe14c52062e from=translated src=- shape=f0ab33c8 vocab=82dbef68
-/
theorem greatestCommonDivisor_unique_up_to_associates
    {R : Type*} [CommRing R] (hR : IntegralDomainAxioms R) {d e a b : R}
    (hd : GreatestCommonDivisor d a b) (he : GreatestCommonDivisor e a b) :
    AssociateElements d e := by
  letI : IsDomain R := (integralDomainAxioms_iff_isDomain (R := R)).mp hR
  have hde : DividesElement d e := he.2.2 d hd.1 hd.2.1
  have hed : DividesElement e d := hd.2.2 e he.1 he.2.1
  obtain ⟨x, hex⟩ := hde
  obtain ⟨y, hdy⟩ := hed
  by_cases hd0 : d = 0
  · have he0 : e = 0 := by rw [hex, hd0, zero_mul]
    rw [hd0, he0]
    exact associateElements_refl (0 : R)
  · have hxy : x * y = 1 := by
      apply mul_left_cancel₀ hd0
      calc
        d * (x * y) = (d * x) * y := (mul_assoc _ _ _).symm
        _ = e * y := by rw [← hex]
        _ = d := hdy.symm
        _ = d * 1 := (mul_one d).symm
    refine ⟨x, ⟨y, hxy, ?_⟩, hex⟩
    simpa [mul_comm] using hxy

end SandronesLibrary.AbstractAlgebra.Ring

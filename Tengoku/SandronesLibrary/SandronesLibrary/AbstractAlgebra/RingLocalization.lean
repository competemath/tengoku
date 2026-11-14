/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# AbstractAlgebra / RingLocalization —— 交换环的局部化与分式域

本模块从教材定义出发构造交换环在乘法集处的局部化。乘法集直接由底层集合、单位元封闭
和乘法封闭组成；分式对的等价关系使用
`∃ u ∈ S, u * (a*d - c*b) = 0`，因此即使原环含零因子也仍然正确。

随后把加法、乘法、取负、零元和单位元下降到自定义商类型，证明其组成交换环；构造规范
映射，证明分母像均为本库 `UnitElement`，并给出每个元素的分子/分母表示。最后证明局部化
对所有把 `S` 送到单位元的普通函数环同态具有存在唯一的泛性质。对整环取非零元乘法集时，
所得局部化满足本库 `FieldAxioms`，即得到分式域定理。

公开接口只使用本库教材概念、集合、普通函数与自定义商类型，不暴露 Mathlib 的
`Submonoid`、`Localization`、`IsLocalization`、`Algebra`、`Module` 或 `Submodule`。

> **Entry**: abstract-algebra.ring.localization
-/

namespace SandronesLibrary.AbstractAlgebra.Ring

/-- **乘法集**：包含 `1` 且对乘法封闭的环元素集合。
> **Entry**: abstract-algebra.ring.localization-/
structure MultiplicativeSet (R : Type*) [One R] [Mul R] where
  carrier : Set R
  one_mem : 1 ∈ carrier
  mul_mem : ∀ {a b : R}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier

/-- **分式对**：分子为任意环元素，分母必须属于给定乘法集 `S`。
> **Entry**: abstract-algebra.ring.localization-/
structure FractionPair {R : Type*} [One R] [Mul R] (S : MultiplicativeSet R) where
  numerator : R
  denominator : R
  denominator_mem : denominator ∈ S.carrier

/-- **分式对等价关系**：`a/b` 与 `c/d` 等价，当某个 `u ∈ S` 消去交叉乘积之差。
额外乘子 `u` 是含零因子交换环中不可省略的条件。
> **Entry**: abstract-algebra.ring.localization-/
def fractionPairEquivalent {R : Type*} [CommRing R] (S : MultiplicativeSet R)
    (p q : FractionPair S) : Prop :=
  ∃ u : R, u ∈ S.carrier ∧
    u * (p.numerator * q.denominator - q.numerator * p.denominator) = 0

/-- 分式对关系满足自反、对称和传递，因而确实是等价关系。
> **Entry**: abstract-algebra.ring.localization
@isnad1 id=equivale.0h2v.s5.b1a93b388aa6 from=translated src=- shape=18cb2c77 vocab=53da7940
-/
theorem fractionPairEquivalent_equivalence {R : Type*} [CommRing R]
    (S : MultiplicativeSet R) : Equivalence (fractionPairEquivalent S) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    exact ⟨1, S.one_mem, by simp⟩
  · intro p q
    rintro ⟨u, huS, hu⟩
    refine ⟨u, huS, ?_⟩
    calc
      u * (q.numerator * p.denominator - p.numerator * q.denominator) =
          -(u * (p.numerator * q.denominator - q.numerator * p.denominator)) := by ring
      _ = 0 := by rw [hu]; simp
  · intro p q r
    rintro ⟨u, huS, hu⟩ ⟨v, hvS, hv⟩
    refine ⟨u * v * q.denominator,
      S.mul_mem (S.mul_mem huS hvS) q.denominator_mem, ?_⟩
    calc
      (u * v * q.denominator) *
          (p.numerator * r.denominator - r.numerator * p.denominator) =
        v * r.denominator *
            (u * (p.numerator * q.denominator - q.numerator * p.denominator)) +
          u * p.denominator *
            (v * (q.numerator * r.denominator - r.numerator * q.denominator)) := by ring
      _ = 0 := by rw [hu, hv]; ring

/-- 将分式对等价关系打包为商类型所需的 `Setoid`。
> **Entry**: abstract-algebra.ring.localization-/
def fractionPairSetoid {R : Type*} [CommRing R] (S : MultiplicativeSet R) :
    Setoid (FractionPair S) :=
  ⟨fractionPairEquivalent S, fractionPairEquivalent_equivalence S⟩

/-- **局部化环的底层类型**：分式对按上述零因子安全关系所得的自定义商类型。
> **Entry**: abstract-algebra.ring.localization-/
def LocalizationRing {R : Type*} [CommRing R] (S : MultiplicativeSet R) :=
  Quotient (fractionPairSetoid S)

/-- 把满足 `b ∈ S` 的形式分式 `a/b` 送入局部化商类型。
> **Entry**: abstract-algebra.ring.localization-/
def localizationFraction {R : Type*} [CommRing R] (S : MultiplicativeSet R)
    (a b : R) (hb : b ∈ S.carrier) : LocalizationRing S :=
  Quotient.mk _ ⟨a, b, hb⟩

/-- 两个具体分式在局部化中相等，当且仅当存在乘法集中的额外乘子消去交叉乘积差。
> **Entry**: abstract-algebra.ring.localization
@isnad1 id=iff.2h6v.s7.19d95f34bfd5 from=translated src=- shape=c6b42e20 vocab=8d22dca9
-/
theorem localizationFraction_eq_iff {R : Type*} [CommRing R]
    (S : MultiplicativeSet R) (a b c d : R)
    (hb : b ∈ S.carrier) (hd : d ∈ S.carrier) :
    localizationFraction S a b hb = localizationFraction S c d hd ↔
      ∃ u : R, u ∈ S.carrier ∧ u * (a * d - c * b) = 0 := by
  exact Quotient.eq

private def fractionPairAdd {R : Type*} [CommRing R] (S : MultiplicativeSet R)
    (p q : FractionPair S) : FractionPair S :=
  ⟨p.numerator * q.denominator + q.numerator * p.denominator,
    p.denominator * q.denominator, S.mul_mem p.denominator_mem q.denominator_mem⟩

private def fractionPairMul {R : Type*} [CommRing R] (S : MultiplicativeSet R)
    (p q : FractionPair S) : FractionPair S :=
  ⟨p.numerator * q.numerator, p.denominator * q.denominator,
    S.mul_mem p.denominator_mem q.denominator_mem⟩

private def fractionPairNeg {R : Type*} [CommRing R] (S : MultiplicativeSet R)
    (p : FractionPair S) : FractionPair S :=
  ⟨-p.numerator, p.denominator, p.denominator_mem⟩

private theorem fractionPairEquivalent_add {R : Type*} [CommRing R]
    (S : MultiplicativeSet R) {p p' q q' : FractionPair S}
    (hp : fractionPairEquivalent S p p') (hq : fractionPairEquivalent S q q') :
    fractionPairEquivalent S (fractionPairAdd S p q) (fractionPairAdd S p' q') := by
  rcases hp with ⟨u, huS, hu⟩
  rcases hq with ⟨v, hvS, hv⟩
  refine ⟨u * v, S.mul_mem huS hvS, ?_⟩
  calc
    (u * v) *
        ((fractionPairAdd S p q).numerator * (fractionPairAdd S p' q').denominator -
          (fractionPairAdd S p' q').numerator * (fractionPairAdd S p q).denominator) =
      v * q.denominator * q'.denominator *
          (u * (p.numerator * p'.denominator - p'.numerator * p.denominator)) +
        u * p.denominator * p'.denominator *
          (v * (q.numerator * q'.denominator - q'.numerator * q.denominator)) := by
            simp only [fractionPairAdd]
            ring
    _ = 0 := by rw [hu, hv]; ring

private theorem fractionPairEquivalent_mul {R : Type*} [CommRing R]
    (S : MultiplicativeSet R) {p p' q q' : FractionPair S}
    (hp : fractionPairEquivalent S p p') (hq : fractionPairEquivalent S q q') :
    fractionPairEquivalent S (fractionPairMul S p q) (fractionPairMul S p' q') := by
  rcases hp with ⟨u, huS, hu⟩
  rcases hq with ⟨v, hvS, hv⟩
  refine ⟨u * v, S.mul_mem huS hvS, ?_⟩
  calc
    (u * v) *
        ((fractionPairMul S p q).numerator * (fractionPairMul S p' q').denominator -
          (fractionPairMul S p' q').numerator * (fractionPairMul S p q).denominator) =
      v * q.numerator * q'.denominator *
          (u * (p.numerator * p'.denominator - p'.numerator * p.denominator)) +
        u * p'.numerator * p.denominator *
          (v * (q.numerator * q'.denominator - q'.numerator * q.denominator)) := by
            simp only [fractionPairMul]
            ring
    _ = 0 := by rw [hu, hv]; ring

private theorem fractionPairEquivalent_neg {R : Type*} [CommRing R]
    (S : MultiplicativeSet R) {p q : FractionPair S}
    (hp : fractionPairEquivalent S p q) :
    fractionPairEquivalent S (fractionPairNeg S p) (fractionPairNeg S q) := by
  rcases hp with ⟨u, huS, hu⟩
  refine ⟨u, huS, ?_⟩
  calc
    u * ((fractionPairNeg S p).numerator * (fractionPairNeg S q).denominator -
      (fractionPairNeg S q).numerator * (fractionPairNeg S p).denominator) =
        -(u * (p.numerator * q.denominator - q.numerator * p.denominator)) := by
          simp only [fractionPairNeg]
          ring
    _ = 0 := by rw [hu]; simp

/-- 局部化加法：在代表元上使用通常的通分公式并下降到商类型。
> **Entry**: abstract-algebra.ring.localization-/
def localizationAdd {R : Type*} [CommRing R] (S : MultiplicativeSet R) :
    LocalizationRing S → LocalizationRing S → LocalizationRing S :=
  Quotient.map₂ (fractionPairAdd S) (by
    intro a a' ha b b' hb
    exact fractionPairEquivalent_add S ha hb)

/-- 局部化乘法：分别相乘分子与分母，并下降到商类型。
> **Entry**: abstract-algebra.ring.localization-/
def localizationMul {R : Type*} [CommRing R] (S : MultiplicativeSet R) :
    LocalizationRing S → LocalizationRing S → LocalizationRing S :=
  Quotient.map₂ (fractionPairMul S) (by
    intro a a' ha b b' hb
    exact fractionPairEquivalent_mul S ha hb)

/-- 局部化取负：只对分子取负，并下降到商类型。
> **Entry**: abstract-algebra.ring.localization-/
def localizationNeg {R : Type*} [CommRing R] (S : MultiplicativeSet R) :
    LocalizationRing S → LocalizationRing S :=
  Quotient.map (fractionPairNeg S) (by
    intro a b hab
    exact fractionPairEquivalent_neg S hab)

/-- 局部化零元，由分式 `0/1` 表示。
> **Entry**: abstract-algebra.ring.localization-/
def localizationZero {R : Type*} [CommRing R] (S : MultiplicativeSet R) : LocalizationRing S :=
  localizationFraction S 0 1 S.one_mem

/-- 局部化单位元，由分式 `1/1` 表示。
> **Entry**: abstract-algebra.ring.localization-/
def localizationOne {R : Type*} [CommRing R] (S : MultiplicativeSet R) : LocalizationRing S :=
  localizationFraction S 1 1 S.one_mem

instance {R : Type*} [CommRing R] (S : MultiplicativeSet R) : Add (LocalizationRing S) :=
  ⟨localizationAdd S⟩
instance {R : Type*} [CommRing R] (S : MultiplicativeSet R) : Mul (LocalizationRing S) :=
  ⟨localizationMul S⟩
instance {R : Type*} [CommRing R] (S : MultiplicativeSet R) : Neg (LocalizationRing S) :=
  ⟨localizationNeg S⟩
instance {R : Type*} [CommRing R] (S : MultiplicativeSet R) : Zero (LocalizationRing S) :=
  ⟨localizationZero S⟩
instance {R : Type*} [CommRing R] (S : MultiplicativeSet R) : One (LocalizationRing S) :=
  ⟨localizationOne S⟩

/-- 两个具体分式相加的通分计算公式。
> **Entry**: abstract-algebra.ring.localization
@isnad1 id=eq.2h6v.s7.85e3c8c5991a from=translated src=- shape=dec356cd vocab=8bcf39d3
-/
@[simp] theorem localizationFraction_add {R : Type*} [CommRing R]
    (S : MultiplicativeSet R) (a b c d : R)
    (hb : b ∈ S.carrier) (hd : d ∈ S.carrier) :
    localizationFraction S a b hb + localizationFraction S c d hd =
      localizationFraction S (a * d + c * b) (b * d) (S.mul_mem hb hd) := by
  rfl

/-- 两个具体分式相乘的计算公式。
> **Entry**: abstract-algebra.ring.localization
@isnad1 id=eq.2h6v.s7.a869a48faf44 from=translated src=- shape=24b5cdf5 vocab=b6f41463
-/
@[simp] theorem localizationFraction_mul {R : Type*} [CommRing R]
    (S : MultiplicativeSet R) (a b c d : R)
    (hb : b ∈ S.carrier) (hd : d ∈ S.carrier) :
    localizationFraction S a b hb * localizationFraction S c d hd =
      localizationFraction S (a * c) (b * d) (S.mul_mem hb hd) := by
  rfl

/-- 具体分式取负时只需对分子取负。
> **Entry**: abstract-algebra.ring.localization
@isnad1 id=eq.1h4v.s6.54844a0d27cb from=translated src=- shape=775e40c3 vocab=a778df01
-/
@[simp] theorem localizationFraction_neg {R : Type*} [CommRing R]
    (S : MultiplicativeSet R) (a b : R) (hb : b ∈ S.carrier) :
    -(localizationFraction S a b hb) = localizationFraction S (-a) b hb := by
  rfl

private theorem localizationFraction_eq_of_cross_mul {R : Type*} [CommRing R]
    (S : MultiplicativeSet R) (a b c d : R)
    (hb : b ∈ S.carrier) (hd : d ∈ S.carrier) (h : a * d = c * b) :
    localizationFraction S a b hb = localizationFraction S c d hd := by
  rw [localizationFraction_eq_iff]
  exact ⟨1, S.one_mem, by simp [h]⟩

/-- 下降后的五种运算满足本库逐条列出的全部环公理。
> **Entry**: abstract-algebra.ring.localization
@isnad1 id=ringaxio.0h2v.s5.4b8f1e8dd553 from=translated src=- shape=1fcfa16f vocab=98f4d15f
-/
theorem localizationRing_ringAxioms {R : Type*} [CommRing R] (S : MultiplicativeSet R) :
    RingAxioms (LocalizationRing S) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    rintro ⟨a, b, hb⟩ ⟨c, d, hd⟩ ⟨e, f, hf⟩
    apply localizationFraction_eq_of_cross_mul
    simp only [fractionPairAdd]
    ring
  · intro x
    refine Quotient.inductionOn x ?_
    rintro ⟨a, b, hb⟩
    apply localizationFraction_eq_of_cross_mul
    ring
  · intro x
    refine Quotient.inductionOn x ?_
    rintro ⟨a, b, hb⟩
    apply localizationFraction_eq_of_cross_mul
    ring
  · intro x
    refine Quotient.inductionOn x ?_
    rintro ⟨a, b, hb⟩
    apply localizationFraction_eq_of_cross_mul
    simp only [fractionPairNeg]
    ring
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    rintro ⟨a, b, hb⟩ ⟨c, d, hd⟩
    apply localizationFraction_eq_of_cross_mul
    ring
  · intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    rintro ⟨a, b, hb⟩ ⟨c, d, hd⟩ ⟨e, f, hf⟩
    apply localizationFraction_eq_of_cross_mul
    simp only [fractionPairMul]
    ring
  · intro x
    refine Quotient.inductionOn x ?_
    rintro ⟨a, b, hb⟩
    apply localizationFraction_eq_of_cross_mul
    ring
  · intro x
    refine Quotient.inductionOn x ?_
    rintro ⟨a, b, hb⟩
    apply localizationFraction_eq_of_cross_mul
    ring
  · intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    rintro ⟨a, b, hb⟩ ⟨c, d, hd⟩ ⟨e, f, hf⟩
    apply localizationFraction_eq_of_cross_mul
    simp only [fractionPairAdd, fractionPairMul]
    ring
  · intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    rintro ⟨a, b, hb⟩ ⟨c, d, hd⟩ ⟨e, f, hf⟩
    apply localizationFraction_eq_of_cross_mul
    simp only [fractionPairAdd, fractionPairMul]
    ring

private theorem localizationRing_mul_comm {R : Type*} [CommRing R]
    (S : MultiplicativeSet R) (x y : LocalizationRing S) : x * y = y * x := by
  refine Quotient.inductionOn₂ x y ?_
  rintro ⟨a, b, hb⟩ ⟨c, d, hd⟩
  apply localizationFraction_eq_of_cross_mul
  ring

/-- 局部化商类型上的交换环实例，由已经验证的教材环公理组装而成。
> **Entry**: abstract-algebra.ring.localization-/
instance {R : Type*} [CommRing R] (S : MultiplicativeSet R) : CommRing (LocalizationRing S) := by
  let A := localizationRing_ringAxioms S
  letI : AddCommGroup (LocalizationRing S) :=
    { add := (· + ·)
      add_assoc := A.add_assoc
      zero := 0
      zero_add := A.zero_add
      add_zero := A.add_zero
      neg := Neg.neg
      neg_add_cancel := A.add_left_neg
      add_comm := A.add_comm
      nsmul := nsmulRec
      zsmul := zsmulRec }
  letI : CommMonoid (LocalizationRing S) :=
    { mul := (· * ·)
      mul_assoc := A.mul_assoc
      one := 1
      one_mul := A.one_mul
      mul_one := A.mul_one
      mul_comm := localizationRing_mul_comm S }
  exact
    { zero_mul := by
        intro x
        apply add_left_cancel (a := 0 * x)
        simpa only [add_zero, zero_add] using (A.right_distrib 0 0 x).symm
      mul_zero := by
        intro x
        apply add_left_cancel (a := x * 0)
        simpa only [add_zero, zero_add] using (A.left_distrib x 0 0).symm
      left_distrib := A.left_distrib
      right_distrib := A.right_distrib }

/-- **规范映射**：把 `a : R` 送到分式 `a/1`。
> **Entry**: abstract-algebra.ring.localization-/
def localizationMap {R : Type*} [CommRing R] (S : MultiplicativeSet R) :
    R → LocalizationRing S :=
  fun a => localizationFraction S a 1 S.one_mem

/-- 规范映射保持零、单位、加法、乘法与取负，是本库意义下的环同态。
> **Entry**: abstract-algebra.ring.localization
@isnad1 id=ringhomo.0h2v.s6.e0eefdc998ea from=translated src=- shape=40e80979 vocab=163f99be
-/
theorem localizationMap_is_ringHomomorphism {R : Type*} [CommRing R]
    (S : MultiplicativeSet R) : RingHomomorphism (localizationMap S) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · intro a b
    apply localizationFraction_eq_of_cross_mul
    ring
  · intro a b
    apply localizationFraction_eq_of_cross_mul
    ring
  · intro a
    rfl

/-- 每个乘法集元素经规范映射后成为本库 `UnitElement`；其逆由分式 `1/s` 给出。
> **Entry**: abstract-algebra.ring.localization
@isnad1 id=unitelem.1h3v.s6.949c49ce42cb from=translated src=- shape=cae41a03 vocab=55b7661e
-/
theorem localizationMap_denominator_is_unit {R : Type*} [CommRing R]
    (S : MultiplicativeSet R) {s : R} (hs : s ∈ S.carrier) :
    UnitElement (localizationMap S s) := by
  refine ⟨localizationFraction S 1 s hs, ?_, ?_⟩
  · apply localizationFraction_eq_of_cross_mul
    ring
  · apply localizationFraction_eq_of_cross_mul
    ring

/-- 局部化中的每个元素都可写成一个分子除以一个来自 `S` 的分母：`x·ι(b)=ι(a)`。
> **Entry**: abstract-algebra.ring.localization
@isnad1 id=ex.0h3v.s7.b70309e07585 from=translated src=- shape=107de990 vocab=158310e6
-/
theorem localizationRing_every_element_is_fraction {R : Type*} [CommRing R]
    (S : MultiplicativeSet R) (x : LocalizationRing S) :
    ∃ a b : R, ∃ _hb : b ∈ S.carrier,
      x * localizationMap S b = localizationMap S a := by
  refine Quotient.inductionOn x ?_
  rintro ⟨a, b, hb⟩
  refine ⟨a, b, hb, ?_⟩
  apply localizationFraction_eq_of_cross_mul
  ring

private noncomputable def chosenUnitInverse {T : Type*} [CommRing T]
    {a : T} (ha : UnitElement a) : T := Classical.choose ha

private theorem chosenUnitInverse_right {T : Type*} [CommRing T]
    {a : T} (ha : UnitElement a) : a * chosenUnitInverse ha = 1 := by
  exact (Classical.choose_spec ha).1

private theorem chosenUnitInverse_left {T : Type*} [CommRing T]
    {a : T} (ha : UnitElement a) : chosenUnitInverse ha * a = 1 := by
  exact (Classical.choose_spec ha).2

private noncomputable def fractionPairEvaluate {R T : Type*} [CommRing R] [CommRing T]
    (S : MultiplicativeSet R) (f : R → T)
    (hunit : ∀ s : R, s ∈ S.carrier → UnitElement (f s)) (p : FractionPair S) : T :=
  f p.numerator * chosenUnitInverse (hunit p.denominator p.denominator_mem)

private theorem fractionPairEvaluate_eq {R T : Type*} [CommRing R] [CommRing T]
    (S : MultiplicativeSet R) (f : R → T) (hf : RingHomomorphism f)
    (hunit : ∀ s : R, s ∈ S.carrier → UnitElement (f s))
    {p q : FractionPair S} (hpq : fractionPairEquivalent S p q) :
    fractionPairEvaluate S f hunit p = fractionPairEvaluate S f hunit q := by
  obtain ⟨F, hF⟩ := ringHomomorphism_exists_ringHom f hf
  subst f
  rcases hpq with ⟨u, huS, hu⟩
  have hmapped := congrArg F hu
  simp only [map_mul, map_sub, map_zero] at hmapped
  have hcross :
      F p.numerator * F q.denominator - F q.numerator * F p.denominator = 0 := by
    calc
      F p.numerator * F q.denominator - F q.numerator * F p.denominator =
          1 * (F p.numerator * F q.denominator - F q.numerator * F p.denominator) := by
            rw [one_mul]
      _ = (chosenUnitInverse (hunit u huS) * F u) *
          (F p.numerator * F q.denominator - F q.numerator * F p.denominator) := by
            rw [chosenUnitInverse_left]
      _ = chosenUnitInverse (hunit u huS) *
          (F u * (F p.numerator * F q.denominator - F q.numerator * F p.denominator)) := by
            ring
      _ = 0 := by rw [hmapped]; ring
  have hcross' : F p.numerator * F q.denominator = F q.numerator * F p.denominator :=
    sub_eq_zero.mp hcross
  unfold fractionPairEvaluate
  calc
    F p.numerator * chosenUnitInverse (hunit p.denominator p.denominator_mem) =
        F p.numerator * chosenUnitInverse (hunit p.denominator p.denominator_mem) *
          (F q.denominator * chosenUnitInverse (hunit q.denominator q.denominator_mem)) := by
            rw [chosenUnitInverse_right, mul_one]
    _ = (F p.numerator * F q.denominator) *
          chosenUnitInverse (hunit p.denominator p.denominator_mem) *
          chosenUnitInverse (hunit q.denominator q.denominator_mem) := by ring
    _ = (F q.numerator * F p.denominator) *
          chosenUnitInverse (hunit p.denominator p.denominator_mem) *
          chosenUnitInverse (hunit q.denominator q.denominator_mem) := by rw [hcross']
    _ = F q.numerator * chosenUnitInverse (hunit q.denominator q.denominator_mem) *
          (F p.denominator * chosenUnitInverse (hunit p.denominator p.denominator_mem)) := by ring
    _ = F q.numerator * chosenUnitInverse (hunit q.denominator q.denominator_mem) := by
          rw [chosenUnitInverse_right, mul_one]

/-- **局部化提升**：若环同态 `f` 把 `S` 中元素送到单位元，则按 `a/b ↦ f(a)f(b)⁻¹`
定义从局部化到目标环的规范函数。逆元由单位元存在性作非计算选择。
> **Entry**: abstract-algebra.ring.localization-/
noncomputable def localizationLift {R T : Type*} [CommRing R] [CommRing T]
    (S : MultiplicativeSet R) (f : R → T) (hf : RingHomomorphism f)
    (hunit : ∀ s : R, s ∈ S.carrier → UnitElement (f s)) : LocalizationRing S → T :=
  Quotient.lift (fractionPairEvaluate S f hunit) (by
    intro p q hpq
    exact fractionPairEvaluate_eq S f hf hunit hpq)

/-- 提升在具体分式上的分母消去公式：提升值乘以 `f(b)` 等于 `f(a)`。
> **Entry**: abstract-algebra.ring.localization
@isnad1 id=eq.3h6v.s8.e01c4599b01c from=translated src=- shape=0a41bcf0 vocab=0591fc7c
-/
@[simp] theorem localizationLift_fraction {R T : Type*} [CommRing R] [CommRing T]
    (S : MultiplicativeSet R) (f : R → T) (hf : RingHomomorphism f)
    (hunit : ∀ s : R, s ∈ S.carrier → UnitElement (f s))
    (a b : R) (hb : b ∈ S.carrier) :
    localizationLift S f hf hunit (localizationFraction S a b hb) * f b = f a := by
  change (f a * chosenUnitInverse (hunit b hb)) * f b = f a
  rw [mul_assoc, chosenUnitInverse_left, mul_one]

private theorem eq_of_mul_eq_mul_of_unit {T : Type*} [CommRing T]
    {x y u : T} (hu : UnitElement u) (h : x * u = y * u) : x = y := by
  rcases hu with ⟨v, huv, _⟩
  calc
    x = x * 1 := (mul_one x).symm
    _ = x * (u * v) := by rw [huv]
    _ = (x * u) * v := by rw [mul_assoc]
    _ = (y * u) * v := by rw [h]
    _ = y * (u * v) := by rw [mul_assoc]
    _ = y := by rw [huv, mul_one]

/-- 局部化提升保持全部环运算，因而是本库意义下的环同态。
> **Entry**: abstract-algebra.ring.localization
@isnad1 id=ringhomo.2h4v.s8.32882ec6e735 from=translated src=- shape=c3a6928d vocab=03571467
-/
theorem localizationLift_is_ringHomomorphism {R T : Type*} [CommRing R] [CommRing T]
    (S : MultiplicativeSet R) (f : R → T) (hf : RingHomomorphism f)
    (hunit : ∀ s : R, s ∈ S.carrier → UnitElement (f s)) :
    RingHomomorphism (localizationLift S f hf hunit) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change localizationLift S f hf hunit (localizationFraction S 0 1 S.one_mem) = 0
    apply eq_of_mul_eq_mul_of_unit (hunit 1 S.one_mem)
    simpa [hf.1, hf.2.1] using localizationLift_fraction S f hf hunit 0 1 S.one_mem
  · change localizationLift S f hf hunit (localizationFraction S 1 1 S.one_mem) = 1
    apply eq_of_mul_eq_mul_of_unit (hunit 1 S.one_mem)
    simpa [hf.2.1] using localizationLift_fraction S f hf hunit 1 1 S.one_mem
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    rintro ⟨a, b, hb⟩ ⟨c, d, hd⟩
    change localizationLift S f hf hunit
        (localizationFraction S a b hb + localizationFraction S c d hd) =
      localizationLift S f hf hunit (localizationFraction S a b hb) +
        localizationLift S f hf hunit (localizationFraction S c d hd)
    apply eq_of_mul_eq_mul_of_unit (hunit (b * d) (S.mul_mem hb hd))
    rw [localizationFraction_add]
    rw [localizationLift_fraction]
    symm
    simp only [hf.2.2.1, hf.2.2.2.1]
    calc
      (localizationLift S f hf hunit (localizationFraction S a b hb) +
          localizationLift S f hf hunit (localizationFraction S c d hd)) *
          (f b * f d) =
        (localizationLift S f hf hunit (localizationFraction S a b hb) * f b) * f d +
          (localizationLift S f hf hunit (localizationFraction S c d hd) * f d) * f b := by ring
      _ = f a * f d + f c * f b := by rw [localizationLift_fraction, localizationLift_fraction]
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    rintro ⟨a, b, hb⟩ ⟨c, d, hd⟩
    change localizationLift S f hf hunit
        (localizationFraction S a b hb * localizationFraction S c d hd) =
      localizationLift S f hf hunit (localizationFraction S a b hb) *
        localizationLift S f hf hunit (localizationFraction S c d hd)
    apply eq_of_mul_eq_mul_of_unit (hunit (b * d) (S.mul_mem hb hd))
    rw [localizationFraction_mul]
    rw [localizationLift_fraction]
    symm
    simp only [hf.2.2.2.1]
    calc
      (localizationLift S f hf hunit (localizationFraction S a b hb) *
          localizationLift S f hf hunit (localizationFraction S c d hd)) *
          (f b * f d) =
        (localizationLift S f hf hunit (localizationFraction S a b hb) * f b) *
          (localizationLift S f hf hunit (localizationFraction S c d hd) * f d) := by ring
      _ = f a * f c := by rw [localizationLift_fraction, localizationLift_fraction]
  · intro x
    refine Quotient.inductionOn x ?_
    rintro ⟨a, b, hb⟩
    change localizationLift S f hf hunit (-(localizationFraction S a b hb)) =
      -localizationLift S f hf hunit (localizationFraction S a b hb)
    apply eq_of_mul_eq_mul_of_unit (hunit b hb)
    rw [localizationFraction_neg]
    rw [localizationLift_fraction]
    symm
    rw [hf.2.2.2.2]
    calc
      -localizationLift S f hf hunit (localizationFraction S a b hb) * f b =
          -(localizationLift S f hf hunit (localizationFraction S a b hb) * f b) := by ring
      _ = -f a := by rw [localizationLift_fraction]

/-- 提升与规范映射的复合等于原同态 `f`。
> **Entry**: abstract-algebra.ring.localization
@isnad1 id=eq.2h5v.s7.bb6d280f4866 from=translated src=- shape=53b968a1 vocab=494d571c
-/
@[simp] theorem localizationLift_map {R T : Type*} [CommRing R] [CommRing T]
    (S : MultiplicativeSet R) (f : R → T) (hf : RingHomomorphism f)
    (hunit : ∀ s : R, s ∈ S.carrier → UnitElement (f s)) (a : R) :
    localizationLift S f hf hunit (localizationMap S a) = f a := by
  change localizationLift S f hf hunit (localizationFraction S a 1 S.one_mem) = f a
  simpa [hf.2.1] using localizationLift_fraction S f hf hunit a 1 S.one_mem

/-- **提升唯一性**：任何在规范映射上与 `f` 相容的环同态都等于规范提升。
> **Entry**: abstract-algebra.ring.localization
@isnad1 id=eq.4h5v.s8.36446cd9d124 from=translated src=- shape=2c114210 vocab=483c6bb2
-/
theorem localizationLift_unique {R T : Type*} [CommRing R] [CommRing T]
    (S : MultiplicativeSet R) (f : R → T) (hf : RingHomomorphism f)
    (hunit : ∀ s : R, s ∈ S.carrier → UnitElement (f s))
    (g : LocalizationRing S → T) (hg : RingHomomorphism g)
    (htriangle : ∀ a : R, g (localizationMap S a) = f a) :
    g = localizationLift S f hf hunit := by
  funext x
  refine Quotient.inductionOn x ?_
  rintro ⟨a, b, hb⟩
  change g (localizationFraction S a b hb) =
    localizationLift S f hf hunit (localizationFraction S a b hb)
  apply eq_of_mul_eq_mul_of_unit (hunit b hb)
  calc
    g (localizationFraction S a b hb) * f b =
        g (localizationFraction S a b hb) * g (localizationMap S b) := by
          rw [htriangle]
    _ =
        g (localizationFraction S a b hb * localizationMap S b) :=
          (hg.2.2.2.1 _ _).symm
    _ = g (localizationMap S a) := by
      congr 1
      apply localizationFraction_eq_of_cross_mul
      ring
    _ = f a := htriangle a
    _ = localizationLift S f hf hunit (localizationFraction S a b hb) * f b :=
      (localizationLift_fraction S f hf hunit a b hb).symm

/-- **局部化泛性质**：把 `S` 送到单位元的环同态唯一地经局部化分解。
> **Entry**: abstract-algebra.ring.localization
@isnad1 id=existsun.2h4v.s8.22e30eddb63d from=translated src=- shape=a981879d vocab=48e1ecd1
-/
theorem localizationRing_universal_property {R T : Type*} [CommRing R] [CommRing T]
    (S : MultiplicativeSet R) (f : R → T) (hf : RingHomomorphism f)
    (hunit : ∀ s : R, s ∈ S.carrier → UnitElement (f s)) :
    ∃! g : LocalizationRing S → T,
      RingHomomorphism g ∧ ∀ a : R, g (localizationMap S a) = f a := by
  refine ⟨localizationLift S f hf hunit, ?_, ?_⟩
  · exact ⟨localizationLift_is_ringHomomorphism S f hf hunit,
      localizationLift_map S f hf hunit⟩
  · intro g hg
    exact localizationLift_unique S f hf hunit g hg.1 hg.2

/-- 整环的非零元素构成乘法集；封闭性来自本库无零因子公理。
> **Entry**: abstract-algebra.ring.localization-/
def nonzeroMultiplicativeSet {R : Type*} [CommRing R] (hR : IntegralDomainAxioms R) :
    MultiplicativeSet R where
  carrier := {x | x ≠ 0}
  one_mem := hR.zero_ne_one.symm
  mul_mem := fun ha hb => integralDomain_nonzero_mul_nonzero hR ha hb

/-- **分式域定理**：整环在全部非零元素处的局部化满足本库 `FieldAxioms`。
每个非零分式 `a/b` 的逆由 `b/a` 给出。
> **Entry**: abstract-algebra.ring.localization
@isnad1 id=fieldaxi.1h1v.s6.5c181b2e79ed from=translated src=- shape=939dd3e7 vocab=697936d4
-/
theorem fractionField_fieldAxioms {R : Type*} [CommRing R]
    (hR : IntegralDomainAxioms R) :
    FieldAxioms (LocalizationRing (nonzeroMultiplicativeSet hR)) := by
  let S := nonzeroMultiplicativeSet hR
  refine ⟨commRing_has_commutativeRingAxioms (LocalizationRing S), ?_, ?_⟩
  · intro h01
    have heq : localizationFraction S 0 1 S.one_mem =
        localizationFraction S 1 1 S.one_mem := h01
    obtain ⟨u, hu, hzero⟩ := (localizationFraction_eq_iff S 0 1 1 1
      S.one_mem S.one_mem).mp heq
    apply hu
    simpa using hzero
  · intro x hx
    refine Quotient.inductionOn x ?_ hx
    rintro ⟨a, b, hb⟩ hfrac
    have ha : a ≠ 0 := by
      intro ha0
      apply hfrac
      change localizationFraction S a b hb = localizationFraction S 0 1 S.one_mem
      apply localizationFraction_eq_of_cross_mul
      simp [ha0]
    refine ⟨localizationFraction S b a ha, ?_, ?_⟩
    · apply localizationFraction_eq_of_cross_mul
      ring
    · apply localizationFraction_eq_of_cross_mul
      ring

end SandronesLibrary.AbstractAlgebra.Ring

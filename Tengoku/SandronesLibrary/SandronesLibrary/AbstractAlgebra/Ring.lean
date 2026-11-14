/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/FurinaManifold/sandrones-library@6bce6404b264, `SandronesLibrary/AbstractAlgebra/Ring.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# AbstractAlgebra / Ring —— 环论基础（抽象代数第一学期 A2）

本文件当前条目（引理清单，§0 铁律4：一次一条，逐条编译）：

* **abstract-algebra.ring.def**（交换环/单位/零环判据、子环与生成子环、环同态保运算）✅。
* **abstract-algebra.ring.ideal**（理想判定/吸收乘法/含单位元理想全环/核值域）✅；
  商环的显式构造、投影与泛性质已移至 `RingQuotient` 模块。
* **abstract-algebra.ring.domain**（零因子、整环与域的本库公理层及 Mathlib 桥；
  素/极大理想与商环判据暂保留兼容接口）✅。
* **abstract-algebra.ring.iso**（环同态基本定理 R/ker≅im）✅。

> **语言说明**：Mathlib 的 `Ring`/`Subring`/`Ideal`/`RingHom` 可以作为实现承载，但不能
> 代替本库教材定义。核心概念必须先以公理、谓词或本库结构明确给出，再建立到 Mathlib
> 表示的桥；公开主定理优先使用本库概念。`Module` 仍不允许出现在本阶段公开签名中。
-/

namespace SandronesLibrary

namespace AbstractAlgebra.Ring

/-! ### 教材定义层 -/

/-- **环公理**：在给定 `0,1,+,*,−` 五种运算后，逐条列出加法交换群、乘法幺半群
和左右分配律。

这是本库的教材定义层；Mathlib 的 `[Ring R]` 只作为已经打包好这些运算与公理的实现。
> **Entry**: abstract-algebra.ring.def-/
structure RingAxioms (R : Type*) [Zero R] [One R] [Add R] [Mul R] [Neg R] : Prop where
  add_assoc : ∀ a b c : R, a + b + c = a + (b + c)
  zero_add : ∀ a : R, 0 + a = a
  add_zero : ∀ a : R, a + 0 = a
  add_left_neg : ∀ a : R, -a + a = 0
  add_comm : ∀ a b : R, a + b = b + a
  mul_assoc : ∀ a b c : R, a * b * c = a * (b * c)
  one_mul : ∀ a : R, 1 * a = a
  mul_one : ∀ a : R, a * 1 = a
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

/-- **交换环公理**：满足环公理，并且乘法交换。
> **Entry**: abstract-algebra.ring.def-/
def CommutativeRingAxioms (R : Type*) [Zero R] [One R] [Add R] [Mul R] [Neg R] : Prop :=
  RingAxioms R ∧ ∀ a b : R, a * b = b * a

/-- **单位元素**：`a` 有一个同时为左逆和右逆的元素。
> **Entry**: abstract-algebra.ring.def-/
def UnitElement {R : Type*} [One R] [Mul R] (a : R) : Prop :=
  ∃ b : R, a * b = 1 ∧ b * a = 1

/-- **子环集合判据**：集合含 `0,1`，并对加法、乘法和取负封闭。
> **Entry**: abstract-algebra.ring.def-/
def SubringSet {R : Type*} [Zero R] [One R] [Add R] [Mul R] [Neg R]
    (S : Set R) : Prop :=
  0 ∈ S ∧ 1 ∈ S ∧
    (∀ ⦃a b : R⦄, a ∈ S → b ∈ S → a + b ∈ S) ∧
    (∀ ⦃a b : R⦄, a ∈ S → b ∈ S → a * b ∈ S) ∧
    (∀ ⦃a : R⦄, a ∈ S → -a ∈ S)

/-- **环同态谓词**：函数保持 `0,1,+,*,−`。把它写成普通函数上的谓词，可先用教材
语言验证同态性，再在需要调用实现库时打包为 `RingHom`。
> **Entry**: abstract-algebra.ring.def-/
def RingHomomorphism {R S : Type*} [Zero R] [One R] [Add R] [Mul R] [Neg R]
    [Zero S] [One S] [Add S] [Mul S] [Neg S] (f : R → S) : Prop :=
  f 0 = 0 ∧ f 1 = 1 ∧
    (∀ a b, f (a + b) = f a + f b) ∧
    (∀ a b, f (a * b) = f a * f b) ∧
    (∀ a, f (-a) = -f a)

/-- 每个 Mathlib `Ring` 实例都满足本库逐条列出的环公理。
> **Entry**: abstract-algebra.ring.def
@isnad1 id=ringaxio.0h1v.s5.9ac88f563194 from=translated src=- shape=c6850a32 vocab=be959f37
-/
theorem ring_has_ringAxioms (R : Type*) [Ring R] : RingAxioms R := by
  exact ⟨add_assoc, zero_add, add_zero, neg_add_cancel, add_comm,
    mul_assoc, one_mul, mul_one, mul_add, add_mul⟩

/-- 每个 Mathlib `CommRing` 实例都满足本库交换环公理。
> **Entry**: abstract-algebra.ring.def
@isnad1 id=commutat.0h1v.s5.a03dd779ab76 from=translated src=- shape=c6850a32 vocab=4a783838
-/
theorem commRing_has_commutativeRingAxioms (R : Type*) [CommRing R] :
    CommutativeRingAxioms R := ⟨ring_has_ringAxioms R, mul_comm⟩

/-- **子环判定定理**（教材核心判据）：子集 S 含 0 与 1、对加减乘封闭 ⟹ S 是子环。 
> **Entry**: abstract-algebra.ring.def
@isnad1 id=ex.5h2v.s7.90fe9a97adb7 from=translated src=- shape=dbdf70fa vocab=c087cdf5
-/
theorem subring_of_closed {R : Type*} [Ring R] (S : Set R)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S)
    (hadd : ∀ {x y : R}, x ∈ S → y ∈ S → x + y ∈ S)
    (hmul : ∀ {x y : R}, x ∈ S → y ∈ S → x * y ∈ S)
    (hneg : ∀ {x : R}, x ∈ S → -x ∈ S) :
    ∃ T : Subring R, ∀ x : R, x ∈ T ↔ x ∈ S := by
  let ssg : Subsemigroup R := ⟨S, hmul⟩
  let sm : Submonoid R := ⟨ssg, h1⟩
  let ssr : Subsemiring R := ⟨sm, hadd, h0⟩
  let T : Subring R := ⟨ssr, hneg⟩
  refine ⟨T, ?_⟩
  intro x
  constructor <;> intro hx <;> exact hx

/-- 本库 `SubringSet` 判据与“存在一个底层集合恰为 `S` 的 Mathlib 子环”完全等价。
> **Entry**: abstract-algebra.ring.def
@isnad1 id=iff.0h2v.s6.74523798a0b8 from=translated src=- shape=98bf3d85 vocab=d8e85576
-/
theorem subringSet_iff_exists_subring {R : Type*} [Ring R] (S : Set R) :
    SubringSet S ↔ ∃ T : Subring R, (T : Set R) = S := by
  constructor
  · rintro ⟨h0, h1, hadd, hmul, hneg⟩
    obtain ⟨T, hT⟩ := subring_of_closed S h0 h1
      (fun ha hb => hadd ha hb) (fun ha hb => hmul ha hb) (fun ha => hneg ha)
    exact ⟨T, Set.ext hT⟩
  · rintro ⟨T, rfl⟩
    exact ⟨T.zero_mem, T.one_mem, fun _ _ => T.add_mem, fun _ _ => T.mul_mem,
      fun _ => T.neg_mem⟩

/-- **子环含单位元**：任何子环都包含乘法单位元 1。 
> **Entry**: abstract-algebra.ring.def
@isnad1 id=mem.0h2v.s5.fac843a29b49 from=translated src=- shape=5d14e585 vocab=17fdfe7b
-/
theorem subring_one_mem {R : Type*} [Ring R] (S : Subring R) : 1 ∈ S := by
  exact S.one_mem

/-- **子环含零元**：任何子环都包含加法零元 0。 
> **Entry**: abstract-algebra.ring.def
@isnad1 id=mem.0h2v.s5.fc12e1376954 from=translated src=- shape=5d14e585 vocab=17fdfe7b
-/
theorem subring_zero_mem {R : Type*} [Ring R] (S : Subring R) : 0 ∈ S := by
  exact S.zero_mem

/-- **子环外延性**：元素集相同的子环相等。 
> **Entry**: abstract-algebra.ring.def
@isnad1 id=eq.1h3v.s6.4d10d2cddadd from=translated src=- shape=b6dfcf64 vocab=17fdfe7b
-/
theorem subring_ext {R : Type*} [Ring R] {S T : Subring R}
    (h : ∀ x : R, x ∈ S ↔ x ∈ T) : S = T := by
  exact Subring.ext h

/-- **平凡子环**：`⊥`（由整数生成的子环，元素形如 n·1）。 
> **Entry**: abstract-algebra.ring.def
@isnad1 id=iff.0h2v.s5.756894d4a1e4 from=translated src=- shape=8d2f2316 vocab=0d4f64b2
-/
theorem subring_bot {R : Type*} [Ring R] (x : R) :
    x ∈ (⊥ : Subring R) ↔ ∃ n : ℤ, (n : R) = x := by
  exact Subring.mem_bot

/-- **全子环**：整个环自身是子环（最大子环）。 
> **Entry**: abstract-algebra.ring.def
@isnad1 id=eq.0h1v.s5.74ff84be21e5 from=translated src=- shape=2100d262 vocab=325c8b42
-/
theorem subring_top {R : Type*} [Ring R] :
    ((⊤ : Subring R) : Set R) = Set.univ := by
  ext x
  constructor
  · intro hx
    trivial
  · intro hx
    exact Subring.mem_top x

/-- **环同态保单位元**：f(1) = 1。 
> **Entry**: abstract-algebra.ring.def
@isnad1 id=eq.0h3v.s6.468103436c6b from=translated src=- shape=602c6a13 vocab=d994f282
-/
theorem ring_hom_map_one {R S : Type*} [Ring R] [Ring S] (f : R →+* S) : f 1 = 1 := by
  exact f.map_one

/-- **环同态保加法**：f(a+b) = f(a) + f(b)。 
> **Entry**: abstract-algebra.ring.def
@isnad1 id=eq.0h5v.s7.216e61db040d from=translated src=- shape=b55fae54 vocab=4f59604a
-/
theorem ring_hom_map_add {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a b : R) :
    f (a + b) = f a + f b := by
  exact f.map_add a b

/-- **环同态保乘法**：f(a·b) = f(a)·f(b)。 
> **Entry**: abstract-algebra.ring.def
@isnad1 id=eq.0h5v.s7.a02596fd540e from=translated src=- shape=b55fae54 vocab=9591956b
-/
theorem ring_hom_map_mul {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a b : R) :
    f (a * b) = f a * f b := by
  exact f.map_mul a b

/-- **交换环的乘法交换律**：交换环中因子的次序不影响乘积。

普通 `Ring` 只要求加法交换；`CommRing` 额外要求乘法交换。
> **Entry**: abstract-algebra.ring.def
@isnad1 id=eq.0h3v.s5.39302e268436 from=translated src=- shape=e8453877 vocab=5d1768bb
-/
theorem comm_ring_mul_comm {R : Type*} [CommRing R] (a b : R) : a * b = b * a :=
  mul_comm a b

/-- **单位判据**：幺半群元素 `a` 可逆，当且仅当存在同一个元素 `b` 同时满足
`a * b = 1` 与 `b * a = 1`。

在非交换乘法中，只有单侧逆通常不够，因此教材定义必须同时保留两个方向。
> **Entry**: abstract-algebra.ring.def
@isnad1 id=iff.0h2v.s6.f643af922b3f from=translated src=- shape=de0caa09 vocab=59633417
-/
theorem isUnit_iff_exists_two_sided_inverse {R : Type*} [Monoid R] (a : R) :
    IsUnit a ↔ ∃ b : R, a * b = 1 ∧ b * a = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨↑u⁻¹, Units.mul_inv u, Units.inv_mul u⟩
  · rintro ⟨b, hab, hba⟩
    exact ⟨⟨a, b, hab, hba⟩, rfl⟩

/-- 本库单位元素定义与 Mathlib `IsUnit` 等价；后者只作为单位群打包实现。
> **Entry**: abstract-algebra.ring.def
@isnad1 id=iff.0h2v.s4.40f30eedee98 from=translated src=- shape=bc057928 vocab=bef800b3
-/
theorem unitElement_iff_isUnit {R : Type*} [Monoid R] (a : R) :
    UnitElement a ↔ IsUnit a :=
  (isUnit_iff_exists_two_sided_inverse a).symm

/-- **零环判据**：环中 `0 = 1` 当且仅当该环只有一个元素。
> **Entry**: abstract-algebra.ring.def
@isnad1 id=iff.0h1v.s5.4de6b1080f85 from=translated src=- shape=6b3d47cf vocab=994bf35f
-/
theorem zero_eq_one_iff_subsingleton {R : Type*} [Ring R] :
    (0 : R) = 1 ↔ Subsingleton R := subsingleton_iff_zero_eq_one

/-- **由集合生成的子环**：`generatedSubring S` 是包含 `S` 的最小子环。
> **Entry**: abstract-algebra.ring.def-/
def generatedSubring {R : Type*} [Ring R] (S : Set R) : Subring R :=
  Subring.closure S

/-- 每个生成元都属于它们生成的子环，即 `S ⊆ generatedSubring S`。
> **Entry**: abstract-algebra.ring.def
@isnad1 id=le.0h2v.s4.712726a596af from=translated src=- shape=01bbfb71 vocab=58853b83
-/
theorem subset_generatedSubring {R : Type*} [Ring R] (S : Set R) :
    S ⊆ generatedSubring S := Subring.subset_closure

/-- **生成子环的最小性**：`generatedSubring S ≤ T` 当且仅当 `T` 包含 `S`。
> **Entry**: abstract-algebra.ring.def
@isnad1 id=iff.0h3v.s5.ad39afd39fea from=translated src=- shape=3d3cab5f vocab=58853b83
-/
theorem generatedSubring_le_iff {R : Type*} [Ring R] {S : Set R} {T : Subring R} :
    generatedSubring S ≤ T ↔ S ⊆ T := Subring.closure_le

/-- 扩大生成元集合只会扩大生成子环。
> **Entry**: abstract-algebra.ring.def
@isnad1 id=le.1h3v.s5.dc4dc9ed8198 from=translated src=- shape=e4a3c269 vocab=99938de4
-/
theorem generatedSubring_mono {R : Type*} [Ring R] {S T : Set R} (hST : S ⊆ T) :
    generatedSubring S ≤ generatedSubring T :=
  generatedSubring_le_iff.mpr (Set.Subset.trans hST (subset_generatedSubring T))

/-- 两个子环的交仍是子环；元素属于交，当且仅当它同时属于两个子环。
> **Entry**: abstract-algebra.ring.def
@isnad1 id=iff.0h4v.s6.aa1106c811ec from=translated src=- shape=11a26329 vocab=62b742bf
-/
theorem mem_subring_inf_iff {R : Type*} [Ring R] {S T : Subring R} {x : R} :
    x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := Subring.mem_inf

/-- 环同态把零元映到零元。
> **Entry**: abstract-algebra.ring.def
@isnad1 id=eq.0h3v.s6.39bcef5d530c from=translated src=- shape=602c6a13 vocab=d994f282
-/
theorem ring_hom_map_zero {R S : Type*} [Ring R] [Ring S] (f : R →+* S) : f 0 = 0 :=
  f.map_zero

/-- 环同态保持加法逆元。
> **Entry**: abstract-algebra.ring.def
@isnad1 id=eq.0h4v.s6.2d294b7d7692 from=translated src=- shape=603bf7ae vocab=1fff60b2
-/
theorem ring_hom_map_neg {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a : R) :
    f (-a) = -f a := f.map_neg a

/-- 环同态保持减法。
> **Entry**: abstract-algebra.ring.def
@isnad1 id=eq.0h5v.s7.c35b85071b41 from=translated src=- shape=b55fae54 vocab=f560abd6
-/
theorem ring_hom_map_sub {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a b : R) :
    f (a - b) = f a - f b := f.map_sub a b

/-- 环同态保持自然数次幂。
> **Entry**: abstract-algebra.ring.def
@isnad1 id=eq.0h5v.s7.640218e83f7c from=translated src=- shape=eadbd16b vocab=992a7999
-/
theorem ring_hom_map_pow {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a : R) (n : ℕ) :
    f (a ^ n) = (f a) ^ n := f.map_pow a n

/-- 环同态保持整数经单位元嵌入所得的元素：`f(n · 1_R) = n · 1_S`。
> **Entry**: abstract-algebra.ring.def
@isnad1 id=eq.0h4v.s6.266eb65f0f66 from=translated src=- shape=6185d9c1 vocab=03efc18b
-/
theorem ring_hom_map_intCast {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (n : ℤ) :
    f (n : R) = (n : S) := map_intCast f n

/-- 打包的 Mathlib 环同态满足本库的逐运算同态谓词。
> **Entry**: abstract-algebra.ring.def
@isnad1 id=ringhomo.0h3v.s7.639ee0453326 from=translated src=- shape=bb88c798 vocab=e24c5056
-/
theorem ringHom_is_RingHomomorphism {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    RingHomomorphism f :=
  ⟨f.map_zero, f.map_one, f.map_add, f.map_mul, f.map_neg⟩

/-- 反之，满足本库环同态谓词的普通函数可打包成 Mathlib `RingHom`，且底层函数不变。
> **Entry**: abstract-algebra.ring.def
@isnad1 id=ex.1h3v.s7.72043c16319c from=translated src=- shape=909581d3 vocab=e24c5056
-/
theorem ringHomomorphism_exists_ringHom {R S : Type*} [Ring R] [Ring S] (f : R → S)
    (hf : RingHomomorphism f) : ∃ F : R →+* S, ⇑F = f := by
  refine ⟨{
    toFun := f
    map_one' := hf.2.1
    map_mul' := hf.2.2.2.1
    map_zero' := hf.1
    map_add' := hf.2.2.1 }, rfl⟩

/-! ### 理想的本库定义与运算 -/

/-- **左理想**：加法子群 `I` 对环中任意元素的左乘封闭。这里把零元、加法、负元和
左吸收逐项写出，不以 Mathlib 的打包结构代替教材定义。
> **Entry**: abstract-algebra.ring.ideal-/
def LeftIdealSet {R : Type*} [Zero R] [Add R] [Neg R] [Mul R] (I : Set R) : Prop :=
  0 ∈ I ∧ (∀ ⦃x y : R⦄, x ∈ I → y ∈ I → x + y ∈ I) ∧
    (∀ ⦃x : R⦄, x ∈ I → -x ∈ I) ∧ (∀ (r : R) ⦃x : R⦄, x ∈ I → r * x ∈ I)

/-- **右理想**：加法子群 `I` 对环中任意元素的右乘封闭。
> **Entry**: abstract-algebra.ring.ideal-/
def RightIdealSet {R : Type*} [Zero R] [Add R] [Neg R] [Mul R] (I : Set R) : Prop :=
  0 ∈ I ∧ (∀ ⦃x y : R⦄, x ∈ I → y ∈ I → x + y ∈ I) ∧
    (∀ ⦃x : R⦄, x ∈ I → -x ∈ I) ∧ (∀ (r : R) ⦃x : R⦄, x ∈ I → x * r ∈ I)

/-- **双边理想**：同时是左理想和右理想。交换环中两侧吸收等价；非交换环中必须区分。
> **Entry**: abstract-algebra.ring.ideal-/
def TwoSidedIdealSet {R : Type*} [Zero R] [Add R] [Neg R] [Mul R] (I : Set R) : Prop :=
  LeftIdealSet I ∧ RightIdealSet I

/-- 集合 `S` 生成的双边理想：所有包含 `S` 的双边理想之交。这一定义直接表达“包含
`S` 的最小双边理想”，不预先依赖有限和的具体表示。
> **Entry**: abstract-algebra.ring.ideal-/
def generatedTwoSidedIdeal {R : Type*} [Zero R] [Add R] [Neg R] [Mul R]
    (S : Set R) : Set R :=
  {x | ∀ I : Set R, TwoSidedIdealSet I → S ⊆ I → x ∈ I}

/-- 两个理想集合的和：由一个 `I` 中元素与一个 `J` 中元素之和组成。
> **Entry**: abstract-algebra.ring.ideal-/
def idealSetSum {R : Type*} [Add R] (I J : Set R) : Set R :=
  {z | ∃ x ∈ I, ∃ y ∈ J, x + y = z}

/-- 两个双边理想集合的积：由所有 `x*y`（`x∈I, y∈J`）生成的双边理想。
生成闭包自动包含有限和及双侧环乘，因此该定义在非交换环中也正确。
> **Entry**: abstract-algebra.ring.ideal-/
def idealSetProduct {R : Type*} [Zero R] [Add R] [Neg R] [Mul R]
    (I J : Set R) : Set R :=
  generatedTwoSidedIdeal {z | ∃ x ∈ I, ∃ y ∈ J, x * y = z}

/--
@isnad1 id=twosided.0h2v.s6.0fa8a086bd03 from=translated src=- shape=ed10201d vocab=cb4ff803
-/
theorem generatedTwoSidedIdeal_is_ideal {R : Type*} [Ring R] (S : Set R) :
    TwoSidedIdealSet (generatedTwoSidedIdeal S) := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro I hI hSI; exact hI.1.1
    · intro x y hx hy I hI hSI; exact hI.1.2.1 (hx I hI hSI) (hy I hI hSI)
    · intro x hx I hI hSI; exact hI.1.2.2.1 (hx I hI hSI)
    · intro r x hx I hI hSI; exact hI.1.2.2.2 r (hx I hI hSI)
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro I hI hSI; exact hI.2.1
    · intro x y hx hy I hI hSI; exact hI.2.2.1 (hx I hI hSI) (hy I hI hSI)
    · intro x hx I hI hSI; exact hI.2.2.2.1 (hx I hI hSI)
    · intro r x hx I hI hSI; exact hI.2.2.2.2 r (hx I hI hSI)

/--
@isnad1 id=le.0h2v.s5.543abb0fcca9 from=translated src=- shape=1b31f6ab vocab=5ec7c10f
-/
theorem subset_generatedTwoSidedIdeal {R : Type*} [Ring R] (S : Set R) :
    S ⊆ generatedTwoSidedIdeal S := by
  intro x hx I hI hSI
  exact hSI hx

/--
@isnad1 id=le.2h3v.s6.f77676cca686 from=translated src=- shape=de7d2ea6 vocab=28ad082e
-/
theorem generatedTwoSidedIdeal_least {R : Type*} [Ring R] {S I : Set R}
    (hI : TwoSidedIdealSet I) (hSI : S ⊆ I) : generatedTwoSidedIdeal S ⊆ I := by
  intro x hx
  exact hx I hI hSI

/--
@isnad1 id=twosided.2h3v.s7.d0f9cc4cccb8 from=translated src=- shape=026a30af vocab=b24c4d4c
-/
theorem idealSetSum_is_ideal {R : Type*} [Ring R] {I J : Set R}
    (hI : TwoSidedIdealSet I) (hJ : TwoSidedIdealSet J) :
    TwoSidedIdealSet (idealSetSum I J) := by
  constructor
  · refine ⟨⟨0, hI.1.1, 0, hJ.1.1, add_zero 0⟩, ?_, ?_, ?_⟩
    · rintro a b ⟨x, hx, y, hy, rfl⟩ ⟨u, hu, v, hv, rfl⟩
      exact ⟨x + u, hI.1.2.1 hx hu, y + v, hJ.1.2.1 hy hv, by abel⟩
    · rintro a ⟨x, hx, y, hy, rfl⟩
      exact ⟨-x, hI.1.2.2.1 hx, -y, hJ.1.2.2.1 hy, by abel⟩
    · rintro r a ⟨x, hx, y, hy, rfl⟩
      exact ⟨r * x, hI.1.2.2.2 r hx, r * y, hJ.1.2.2.2 r hy, by noncomm_ring⟩
  · refine ⟨⟨0, hI.2.1, 0, hJ.2.1, add_zero 0⟩, ?_, ?_, ?_⟩
    · rintro a b ⟨x, hx, y, hy, rfl⟩ ⟨u, hu, v, hv, rfl⟩
      exact ⟨x + u, hI.2.2.1 hx hu, y + v, hJ.2.2.1 hy hv, by abel⟩
    · rintro a ⟨x, hx, y, hy, rfl⟩
      exact ⟨-x, hI.2.2.2.1 hx, -y, hJ.2.2.2.1 hy, by abel⟩
    · rintro r a ⟨x, hx, y, hy, rfl⟩
      exact ⟨x * r, hI.2.2.2.2 r hx, y * r, hJ.2.2.2.2 r hy, by noncomm_ring⟩

/-- 在交换环中，本库双边理想定义与 Mathlib `Ideal` 承载结构完全等价。
> **Entry**: abstract-algebra.ring.ideal
@isnad1 id=iff.0h2v.s6.865fa1c78895 from=translated src=- shape=98bf3d85 vocab=9a3c1cd8
-/
theorem twoSidedIdealSet_iff_exists_ideal {R : Type*} [CommRing R] (I : Set R) :
    TwoSidedIdealSet I ↔ ∃ J : Ideal R, (J : Set R) = I := by
  constructor
  · intro hI
    let asg : AddSubsemigroup R := ⟨I, fun hx hy => hI.1.2.1 hx hy⟩
    let asm : AddSubmonoid R := ⟨asg, hI.1.1⟩
    let J : Ideal R := ⟨asm, fun r x hx => hI.1.2.2.2 r hx⟩
    exact ⟨J, rfl⟩
  · rintro ⟨J, rfl⟩
    constructor
    · exact ⟨J.zero_mem, (fun {_ _} hx hy => J.add_mem hx hy),
        (fun {_} hx => J.neg_mem hx), fun r {_} hx => J.mul_mem_left r hx⟩
    · refine ⟨J.zero_mem, (fun {_ _} hx hy => J.add_mem hx hy),
        (fun {_} hx => J.neg_mem hx), ?_⟩
      intro r x hx
      rw [mul_comm]
      exact J.mul_mem_left r hx

/-- 本库理想和与 Mathlib 格结构中的上确界具有相同底层集合。
> **Entry**: abstract-algebra.ring.ideal
@isnad1 id=eq.0h3v.s7.db0ddbba6189 from=translated src=- shape=2cd80a4d vocab=99273453
-/
theorem idealSetSum_eq_mathlib_sup {R : Type*} [CommRing R] (I J : Ideal R) :
    idealSetSum (I : Set R) (J : Set R) = ((I ⊔ J : Ideal R) : Set R) := by
  ext z
  exact Submodule.mem_sup.symm

/-- 本库“由两两乘积生成”的定义与 Mathlib 理想乘积具有相同底层集合。
> **Entry**: abstract-algebra.ring.ideal
@isnad1 id=eq.0h3v.s7.ba36391cf10e from=translated src=- shape=10042877 vocab=340f7d8b
-/
theorem idealSetProduct_eq_mathlib_mul {R : Type*} [CommRing R] (I J : Ideal R) :
    idealSetProduct (I : Set R) (J : Set R) = ((I * J : Ideal R) : Set R) := by
  ext z
  constructor
  · intro hz
    apply hz (I * J : Ideal R)
    · exact (twoSidedIdealSet_iff_exists_ideal ((I * J : Ideal R) : Set R)).2 ⟨I * J, rfl⟩
    · rintro w ⟨x, hx, y, hy, rfl⟩
      exact Ideal.mul_mem_mul hx hy
  · intro hz
    obtain ⟨K, hK⟩ :=
      (twoSidedIdealSet_iff_exists_ideal (generatedTwoSidedIdeal
        {w | ∃ x ∈ (I : Set R), ∃ y ∈ (J : Set R), x * y = w})).1
        (generatedTwoSidedIdeal_is_ideal _)
    have hmul : I * J ≤ K := Ideal.mul_le.mpr (by
      intro x hx y hy
      change x * y ∈ (K : Set R)
      rw [hK]
      exact subset_generatedTwoSidedIdeal _ ⟨x, hx, y, hy, rfl⟩)
    change z ∈ generatedTwoSidedIdeal
      {w | ∃ x ∈ (I : Set R), ∃ y ∈ (J : Set R), x * y = w}
    rw [← hK]
    exact hmul hz

/-- **理想判定定理**（教材核心判据）：子集 I 含 0、对加法封闭、且被 R 乘法吸收（y ∈ I ⟹ x·y ∈ I）⟹ I 是理想。 
> **Entry**: abstract-algebra.ring.ideal
@isnad1 id=ex.3h2v.s7.ee82c8f7f5f1 from=translated src=- shape=3e7bc99a vocab=d47c2154
-/
theorem ideal_of_closed {R : Type*} [Ring R] (I : Set R)
    (h0 : 0 ∈ I)
    (hadd : ∀ {x y : R}, x ∈ I → y ∈ I → x + y ∈ I)
    (hmulr : ∀ {x y : R}, y ∈ I → x * y ∈ I) :
    ∃ J : Ideal R, ∀ x : R, x ∈ J ↔ x ∈ I := by
  let asg : AddSubsemigroup R := ⟨I, hadd⟩
  let asm : AddSubmonoid R := ⟨asg, h0⟩
  let J : Ideal R := ⟨asm, fun c x hx => hmulr (x := c) (y := x) hx⟩
  refine ⟨J, ?_⟩
  intro x
  constructor <;> intro hx <;> exact hx

/-- **理想左吸收**：x ∈ I ⟹ a·x ∈ I（理想对左乘封闭）。 
> **Entry**: abstract-algebra.ring.ideal
@isnad1 id=mem.1h4v.s6.acdfda438f21 from=translated src=- shape=3e6eb35d vocab=2092f625
-/
theorem ideal_mul_mem_left {R : Type*} [Ring R] (I : Ideal R) {x : R} (hx : x ∈ I) (a : R) :
    a * x ∈ I := by
  exact I.mul_mem_left a hx

/-- **理想右吸收**：x ∈ I ⟹ x·a ∈ I（双边理想对右乘封闭）。 
> **Entry**: abstract-algebra.ring.ideal
@isnad1 id=mem.1h4v.s6.3de8ef9e5ffa from=translated src=- shape=c65077e2 vocab=44e882f0
-/
theorem ideal_mul_mem_right {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided]
    {x : R} (hx : x ∈ I) (a : R) : x * a ∈ I := by
  exact I.mul_mem_right a hx

/-- **含单位元的理想是全环**：若理想含某个可逆元，则该理想是整个环。 
> **Entry**: abstract-algebra.ring.ideal
@isnad1 id=eq.2h3v.s6.49b0d2c82e8c from=translated src=- shape=290e3c80 vocab=a6ae73f1
-/
theorem ideal_eq_top_of_unit_mem {R : Type*} [Ring R] (I : Ideal R)
    {x : R} (hx : x ∈ I) (hunit : IsUnit x) : I = ⊤ := by
  exact Ideal.eq_top_of_isUnit_mem I hx hunit

/-- **商环判等准则**：mk x = mk y ⟺ x - y ∈ I（两个同余类相等当且仅当差落在理想中）。 
> **Entry**: abstract-algebra.ring.ideal
@isnad1 id=iff.0h4v.s8.955ded44dd69 from=translated src=- shape=72de1ec8 vocab=2bd94341
-/
theorem quotient_eq_iff_sub_mem {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided]
    (x y : R) : (Ideal.Quotient.mk I) x = (Ideal.Quotient.mk I) y ↔ x - y ∈ I := by
  exact Ideal.Quotient.eq (I := I) (x := x) (y := y)

/-- **环同态核是理想**：环同态 f 的核 `f.ker` 是理想（含 0、加封闭、吸收）。 
> **Entry**: abstract-algebra.ring.ideal
@isnad1 id=ex.0h3v.s6.fe5d2481373e from=translated src=- shape=46fcd563 vocab=63f78a53
-/
theorem ring_hom_ker_is_ideal {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    ∃ J : Ideal R, ∀ x : R, x ∈ J ↔ f x = 0 := by
  refine ⟨RingHom.ker f, ?_⟩
  intro x
  exact RingHom.mem_ker (f := f)

/-- **环同态值域元素刻画**：y 在值域中 ⟺ 存在 x 使 f(x) = y。 
> **Entry**: abstract-algebra.ring.ideal
@isnad1 id=iff.0h4v.s6.252108cc273a from=translated src=- shape=08667cdb vocab=95c26779
-/
theorem ring_hom_mem_range {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (y : S) :
    y ∈ f.range ↔ ∃ x : R, f x = y := by
  exact RingHom.mem_range (f := f)

/-- **环同态单射 ⟺ 核平凡**：环同态 f 是单射当且仅当其核只含零元。 
> **Entry**: abstract-algebra.ring.ideal
@isnad1 id=iff.0h3v.s6.20a06fd0516c from=translated src=- shape=eb2a7ab4 vocab=f166fa38
-/
theorem ring_hom_injective_iff_ker_bot {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    Function.Injective f ↔ RingHom.ker f = ⊥ := by
  exact RingHom.injective_iff_ker_eq_bot f

/-- **零因子元素**：非零元素 `a` 若能在右侧乘以某个非零元素得到零，则称 `a` 为零因子。
> **Entry**: abstract-algebra.ring.domain-/
def ZeroDivisorElement {R : Type*} [Zero R] [Mul R] (a : R) : Prop :=
  a ≠ 0 ∧ ∃ b : R, b ≠ 0 ∧ a * b = 0

/-- **无零因子公理**：乘积为零时，至少有一个因子为零。
> **Entry**: abstract-algebra.ring.domain-/
def NoZeroDivisorsAxiom (R : Type*) [Zero R] [Mul R] : Prop :=
  ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0

/-- **整环公理**：交换环、零不等于一，并且没有非零零因子。
> **Entry**: abstract-algebra.ring.domain-/
structure IntegralDomainAxioms (R : Type*) [Zero R] [One R] [Add R] [Mul R] [Neg R] : Prop where
  commutativeRing : CommutativeRingAxioms R
  zero_ne_one : (0 : R) ≠ 1
  noZeroDivisors : NoZeroDivisorsAxiom R

/-- **域公理**：交换环、零不等于一，并且每个非零元素都是单位元素。
> **Entry**: abstract-algebra.ring.domain-/
structure FieldAxioms (R : Type*) [Zero R] [One R] [Add R] [Mul R] [Neg R] : Prop where
  commutativeRing : CommutativeRingAxioms R
  zero_ne_one : (0 : R) ≠ 1
  nonzero_unit : ∀ a : R, a ≠ 0 → UnitElement a

/-- **无零因子等价刻画**：无零因子公理成立，当且仅当不存在零因子元素。
> **Entry**: abstract-algebra.ring.domain
@isnad1 id=iff.0h1v.s4.2053db41f5fd from=translated src=- shape=49021acd vocab=5eeec569
-/
theorem noZeroDivisorsAxiom_iff_no_zero_divisor {R : Type*} [Zero R] [Mul R] :
    NoZeroDivisorsAxiom R ↔ ∀ a : R, ¬ ZeroDivisorElement a := by
  constructor
  · intro h a ha
    obtain ⟨ha0, b, hb0, hab⟩ := ha
    exact (h a b hab).elim ha0 hb0
  · intro h a b hab
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr (by
        by_contra hb
        exact h a ⟨ha, b, hb, hab⟩)

/-- **整环乘积为零判据**：满足整环公理时，乘积为零蕴含至少一个因子为零。
> **Entry**: abstract-algebra.ring.domain
@isnad1 id=or.2h3v.s6.e13510114038 from=translated src=- shape=b8322d1c vocab=e269709f
-/
theorem integralDomain_mul_eq_zero {R : Type*} [Zero R] [One R] [Add R] [Mul R] [Neg R]
    (hR : IntegralDomainAxioms R) {a b : R} (hab : a * b = 0) :
    a = 0 ∨ b = 0 := by
  exact hR.noZeroDivisors a b hab

/-- **整环中非零乘积非零**：满足整环公理时，两个非零元素的乘积仍非零。
> **Entry**: abstract-algebra.ring.domain
@isnad1 id=ne.3h3v.s6.4fc28eb44ecb from=translated src=- shape=7bbf5cf8 vocab=e269709f
-/
theorem integralDomain_nonzero_mul_nonzero {R : Type*}
    [Zero R] [One R] [Add R] [Mul R] [Neg R]
    (hR : IntegralDomainAxioms R) {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := by
  intro hab
  exact (integralDomain_mul_eq_zero hR hab).elim ha hb

/-- **域中非零元素为单位**：满足域公理时，每个非零元素都有双侧乘法逆元。
> **Entry**: abstract-algebra.ring.domain
@isnad1 id=unitelem.2h2v.s5.1b8565885564 from=translated src=- shape=bb4f7c84 vocab=58d7a4b7
-/
theorem field_nonzero_unit {R : Type*} [Zero R] [One R] [Add R] [Mul R] [Neg R]
    (hR : FieldAxioms R) {a : R} (ha : a ≠ 0) : UnitElement a := by
  exact hR.nonzero_unit a ha

/-- **域公理蕴含整环公理**：满足教材域公理的结构必满足教材整环公理。
> **Entry**: abstract-algebra.ring.domain
@isnad1 id=integral.1h1v.s5.a55b5654ec4c from=translated src=- shape=4ff572b6 vocab=474f4d2c
-/
theorem fieldAxioms_implies_integralDomainAxioms {R : Type*}
    [Zero R] [One R] [Add R] [Mul R] [Neg R]
    (hR : FieldAxioms R) : IntegralDomainAxioms R := by
  refine ⟨hR.commutativeRing, hR.zero_ne_one, ?_⟩
  intro a b hab
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    obtain ⟨c, hac, hca⟩ := hR.nonzero_unit a ha
    let A := hR.commutativeRing.1
    have add_left_cancel : ∀ x y z : R, x + y = x + z → y = z := by
      intro x y z hxyz
      calc
        y = 0 + y := (A.zero_add y).symm
        _ = (-x + x) + y := by rw [A.add_left_neg x]
        _ = -x + (x + y) := A.add_assoc (-x) x y
        _ = -x + (x + z) := by rw [hxyz]
        _ = (-x + x) + z := (A.add_assoc (-x) x z).symm
        _ = 0 + z := by rw [A.add_left_neg x]
        _ = z := A.zero_add z
    have zero_mul (x : R) : 0 * x = 0 := by
      have h : 0 * x = 0 * x + 0 * x := by
        calc
          0 * x = (0 + 0) * x := by rw [A.zero_add 0]
          _ = 0 * x + 0 * x := A.right_distrib 0 0 x
      exact (add_left_cancel (0 * x) 0 (0 * x) (by
        rw [A.add_zero]
        exact h)).symm
    have mul_zero (x : R) : x * 0 = 0 := by
      have h : x * 0 = x * 0 + x * 0 := by
        calc
          x * 0 = x * (0 + 0) := by rw [A.zero_add 0]
          _ = x * 0 + x * 0 := A.left_distrib x 0 0
      exact (add_left_cancel (x * 0) 0 (x * 0) (by
        rw [A.add_zero]
        exact h)).symm
    have hcb : c * (a * b) = 0 := by rw [hab, mul_zero]
    calc
      b = 1 * b := (A.one_mul b).symm
      _ = (c * a) * b := by rw [hca]
      _ = c * (a * b) := A.mul_assoc c a b
      _ = 0 := hcb

/-- **无零因子公理与 Mathlib 的桥接**：教材公理等价于 Mathlib 的 `NoZeroDivisors`。
> **Entry**: abstract-algebra.ring.domain
@isnad1 id=iff.0h1v.s4.46f48ee3424a from=translated src=- shape=da9a72aa vocab=0671d1da
-/
theorem noZeroDivisorsAxiom_iff_mathlib {R : Type*} [Zero R] [Mul R] :
    NoZeroDivisorsAxiom R ↔ NoZeroDivisors R := by
  exact (noZeroDivisors_iff R).symm

/-- **整环公理与 Mathlib 的桥接**：在交换环上，教材整环公理等价于 `IsDomain`。
> **Entry**: abstract-algebra.ring.domain
@isnad1 id=iff.0h1v.s6.6335c827c6a6 from=translated src=- shape=aa7e0af4 vocab=11677b63
-/
theorem integralDomainAxioms_iff_isDomain {R : Type*} [CommRing R] :
    IntegralDomainAxioms R ↔ IsDomain R := by
  constructor
  · intro h
    letI : Nontrivial R := ⟨⟨0, 1, h.zero_ne_one⟩⟩
    letI : NoZeroDivisors R :=
      noZeroDivisorsAxiom_iff_mathlib.mp h.noZeroDivisors
    letI : IsCancelMulZero R := NoZeroDivisors.to_isCancelMulZero R
    exact ⟨⟩
  · intro h
    letI := h
    exact ⟨commRing_has_commutativeRingAxioms R, zero_ne_one,
      noZeroDivisorsAxiom_iff_mathlib.mpr (inferInstance : NoZeroDivisors R)⟩

/-- **域公理与 Mathlib 的桥接**：在交换环上，教材域公理等价于 `IsField`。
> **Entry**: abstract-algebra.ring.domain
@isnad1 id=iff.0h1v.s6.ce8cb595c552 from=translated src=- shape=aa7e0af4 vocab=7087db9d
-/
theorem fieldAxioms_iff_isField {R : Type*} [CommRing R] :
    FieldAxioms R ↔ IsField R := by
  constructor
  · intro h
    refine ⟨⟨0, 1, h.zero_ne_one⟩, mul_comm, ?_⟩
    intro a ha
    obtain ⟨b, hab, hba⟩ := h.nonzero_unit a ha
    exact ⟨b, hab⟩
  · intro h
    refine ⟨commRing_has_commutativeRingAxioms R, ?_, ?_⟩
    · rintro h01
      obtain ⟨x, y, hxy⟩ := h.exists_pair_ne
      exact hxy (by
        calc
          x = x * 1 := (mul_one x).symm
          _ = x * 0 := by rw [← h01]
          _ = 0 := mul_zero x
          _ = 0 * y := (zero_mul y).symm
          _ = 1 * y := by rw [h01]
          _ = y := one_mul y)
    · intro a ha
      obtain ⟨b, hab⟩ := h.mul_inv_cancel ha
      exact ⟨b, hab, by simpa [mul_comm] using hab⟩

/-- **Mathlib 整环兼容接口**：由 `[IsDomain R]` 得到乘积为零判据。教材主接口应使用
`integralDomain_mul_eq_zero` 与本库 `IntegralDomainAxioms`。
> **Entry**: abstract-algebra.ring.domain
@isnad1 id=or.1h3v.s6.2525d095290e from=translated src=- shape=a3883988 vocab=2f616f7b
-/
theorem is_domain_mul_eq_zero {R : Type*} [Ring R] [IsDomain R] {a b : R}
    (h : a * b = 0) : a = 0 ∨ b = 0 := by
  exact mul_eq_zero.mp h

/-- **Mathlib 域兼容接口**：由 `IsField R` 得到非零元的一个乘法逆元。教材主接口应使用
`field_nonzero_unit` 与本库 `FieldAxioms`。
> **Entry**: abstract-algebra.ring.domain
@isnad1 id=ex.2h2v.s5.1bbcbd337498 from=translated src=- shape=abf2220d vocab=6e783d02
-/
theorem is_field_inv_exists {R : Type*} [Ring R] (hF : IsField R) {a : R} (ha : a ≠ 0) :
    ∃ b : R, a * b = 1 := by
  exact IsField.mul_inv_cancel hF ha

/-- **Mathlib 素理想兼容接口**：展开 `Ideal.IsPrime` 的乘积判据。教材主接口见
`RingPrimeIdeal.lean` 中的 `PrimeIdealSet`。
> **Entry**: abstract-algebra.ring.domain
@isnad1 id=iff.0h2v.s7.91f031b26491 from=translated src=- shape=b944c594 vocab=b97e3f40
-/
theorem is_prime_iff {R : Type*} [CommRing R] (I : Ideal R) :
    I.IsPrime ↔ I ≠ ⊤ ∧ ∀ {x y : R}, x * y ∈ I → x ∈ I ∨ y ∈ I := by
  exact Ideal.isPrime_iff

/-- **Mathlib 极大理想兼容接口**：`Ideal.IsMaximal` 推出 `Ideal.IsPrime`。教材主接口见
`RingPrimeIdeal.lean` 中的 `maximalIdealSet_is_prime`。
> **Entry**: abstract-algebra.ring.domain
@isnad1 id=isprime.1h2v.s4.4a314db5a9df from=translated src=- shape=93e860ac vocab=ace53bc1
-/
theorem is_maximal_implies_is_prime {R : Type*} [CommRing R] (I : Ideal R)
    (hI : I.IsMaximal) : I.IsPrime := by
  exact hI.isPrime

/-- **Mathlib 商整环兼容接口**：Mathlib 素理想的商类型具有 `IsDomain`。教材双向判据见
`RingPrimeIdeal.lean` 中的 `primeIdealSet_iff_quotient_integralDomainAxioms`。
> **Entry**: abstract-algebra.ring.domain
@isnad1 id=isdomain.1h2v.s5.7e74a029fc68 from=translated src=- shape=698e674a vocab=8a521d40
-/
theorem quotient_is_domain_of_is_prime {R : Type*} [CommRing R] (I : Ideal R)
    (hI : I.IsPrime) : IsDomain (R ⧸ I) := by
  exact Ideal.Quotient.isDomain I

/-- **Mathlib 零理想兼容接口**：`IsField R` 等价于 Mathlib 零理想极大。
> **Entry**: abstract-algebra.ring.domain
@isnad1 id=iff.0h1v.s5.d8e9da0f2fbe from=translated src=- shape=e0b9ca5b vocab=3e5399e0
-/
theorem is_field_iff_bot_is_maximal {R : Type*} [CommRing R] [Nontrivial R] :
    IsField R ↔ (⊥ : Ideal R).IsMaximal := by
  exact Ring.isField_iff_maximal_bot

/-- **环同态基本定理（第一同构定理）**：R/ker(f) ≅ im(f)。
  商环 R/ker f 与 f 的值域（子环）同构。 
> **Entry**: abstract-algebra.ring.iso
@isnad1 id=nonempty.0h3v.s9.cebb9ede9a11 from=translated src=- shape=0eaf4809 vocab=41efb43b
-/
theorem ring_first_isomorphism {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    Nonempty (R ⧸ RingHom.ker f ≃+* ↥f.range) := by
  exact ⟨RingHom.quotientKerEquivRange f⟩

/-- **Mathlib 商域兼容接口**：Mathlib 商类型为域时，原理想极大。教材双向判据见
`RingPrimeIdeal.lean` 中的 `maximalIdealSet_iff_quotient_fieldAxioms`。
> **Entry**: abstract-algebra.ring.domain
@isnad1 id=ismaxima.1h2v.s5.593fa6f8d9bc from=translated src=- shape=844f6b0f vocab=62099b40
-/
theorem ideal_maximal_of_quotient_isField {R : Type*} [CommRing R] (I : Ideal R)
    (hqf : IsField (R ⧸ I)) : I.IsMaximal := by
  exact Ideal.Quotient.maximal_of_isField I hqf

end AbstractAlgebra.Ring

end SandronesLibrary

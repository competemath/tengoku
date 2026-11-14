/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.FieldExtension
import Tengoku.Seed.RingTheory.AlgebraTower
import Tengoku.Seed.LinearAlgebra.Dimension.Free
import Tengoku.Seed.LinearAlgebra.Basis.Basic
import Tengoku.Seed.LinearAlgebra.Basis.SMul
import Tengoku.Seed.RingTheory.Algebraic.Integral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/FurinaManifold/sandrones-library@6bce6404b264, `SandronesLibrary/AbstractAlgebra/FieldDegree.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# 抽象代数 / 域扩张次数与塔式公式

本模块在 A3.5 显式域嵌入的基础上，用有限和直接给出域扩张的线性组合、
线性无关、张成与基等教材定义。有限基以 `Fin n` 编号，由此把扩张次数
表述为存在长度为 `n` 的有限域基。本模块进一步证明坐标存在唯一性、
次数唯一性、恒等扩张次数为一、有限扩张必为代数扩张，以及扩张塔次数
的乘法公式。

公开 API 始终使用 `FieldEmbedding`、显式有限和和本模块的教材谓词，
不要求调用者提供 Mathlib 的隐式代数或模结构。Mathlib 的线性无关、
张成子模、基、有限维和标量塔仅在私有桥及证明后端出现，用来验证教材
定义与成熟线性代数接口具有相同语义。

> **Entry**: abstract-algebra.field.degree
-/

namespace SandronesLibrary.AbstractAlgebra.FieldDegree

open SandronesLibrary.AbstractAlgebra.FieldExtension


/-! ## 教材线性组合、线性无关、张成与基 -/

/-- 相对于显式域嵌入的有限线性组合。系数先由 `e` 送入目标域，
再与对应向量相乘；
有限指标集 `s` 明确记录真正参与求和的项。

> **Entry**: abstract-algebra.field.degree-/
def fieldLinearCombination {K L ι : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (s : Finset ι) (c : ι → K) (v : ι → L) : L :=
  ∑ i ∈ s, e (c i) * v i

/-- 教材线性无关：任意有限系数关系只能有平凡系数。
结论只要求 `s` 中出现的系数
为零，恰好对应任意有限子族不存在非平凡线性关系。

> **Entry**: abstract-algebra.field.degree-/
def FieldLinearlyIndependent {K L ι : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (v : ι → L) : Prop :=
  ∀ (s : Finset ι) (c : ι → K), fieldLinearCombination e s c v = 0 →
    ∀ i ∈ s, c i = 0

/-- 教材张成：每个目标域元素均为该族的某个有限线性组合。
有限指标集与系数函数
均可随目标元素选择，因此也适用于无限指标族。

> **Entry**: abstract-algebra.field.degree-/
def FieldSpans {K L ι : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (v : ι → L) : Prop :=
  ∀ x : L, ∃ (s : Finset ι) (c : ι → K), fieldLinearCombination e s c v = x

/-- 教材域扩张基：一个向量族同时线性无关并张成整个目标域。
该定义直接组合前两个
有限和谓词，不在公开接口中引入 Mathlib 的基结构。

> **Entry**: abstract-algebra.field.degree-/
def FieldBasis {K L ι : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (v : ι → L) : Prop :=
  FieldLinearlyIndependent e v ∧ FieldSpans e v

/-- `Fin n` 指标下的有限基，所有坐标关系均直接对 `Finset.univ` 求和。
第一部分给出
坐标无关性，第二部分断言每个目标域元素都有一组长度为 `n` 的坐标。

> **Entry**: abstract-algebra.field.degree-/
def FinFieldBasis {K L : Type*} [Field K] [Field L] {n : ℕ}
    (e : FieldEmbedding K L) (v : Fin n → L) : Prop :=
  (∀ c : Fin n → K, fieldLinearCombination e Finset.univ c v = 0 → ∀ i, c i = 0) ∧
  (∀ x : L, ∃ c : Fin n → K, fieldLinearCombination e Finset.univ c v = x)

/-- 扩张次数为 `n`，若存在一个由 `Fin n` 编号的有限域基。
这里把次数作为存在性
谓词，避免预先选择基或引入不可计算的维数函数。

> **Entry**: abstract-algebra.field.degree-/
def HasExtensionDegree {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (n : ℕ) : Prop :=
  ∃ b : Fin n → L, FinFieldBasis e b

/-- 有限域扩张是具有某个自然数次数的显式域扩张。
见证同时给出次数和相应有限域基，
后续可由次数唯一性证明该自然数不依赖选择。

> **Entry**: abstract-algebra.field.degree-/
def FiniteFieldExtension {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) : Prop :=
  ∃ n : ℕ, HasExtensionDegree e n

/-- 代数扩张要求目标域的每个元素都在显式嵌入上代数。
元素代数性沿用 A3.5 的显式
多项式求值定义，因此公开语义不依赖隐式代数实例。

> **Entry**: abstract-algebra.field.degree-/
def AlgebraicExtension {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) : Prop :=
  ∀ a : L, AlgebraicElement e a

/-! ## 私有 Mathlib 证明后端

以下私有桥局部安装由显式嵌入诱导的代数结构，并把有限和教材定义与
Mathlib 的线性代数接口相互转换。高级结构不会进入任何公开声明的签名。
-/

private theorem toAlgebra_algebraMap_eq {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) :
    @algebraMap K L _ _ e.toRingHom.toAlgebra = e.toRingHom := by
  exact RingHom.algebraMap_toAlgebra e.toRingHom

private theorem algebra_smul_eq_embedding_mul {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (c : K) (x : L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    c • x = e c * x := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  rw [Algebra.smul_def, toAlgebra_algebraMap_eq]
  rfl

private theorem fieldLinearCombination_eq_mathlib {K L ι : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L)
    (s : Finset ι) (c : ι → K) (v : ι → L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    fieldLinearCombination e s c v = ∑ i ∈ s, c i • v i := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  apply Finset.sum_congr rfl
  intro i hi
  exact algebra_smul_eq_embedding_mul e (c i) (v i) |>.symm

private theorem fieldLinearlyIndependent_iff_mathlib {K L ι : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) (v : ι → L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    FieldLinearlyIndependent e v ↔ LinearIndependent K v := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  rw [linearIndependent_iff']
  constructor
  · intro h s c hsum i hi
    apply h s c
    · rw [fieldLinearCombination_eq_mathlib e]
      exact hsum
    · exact hi
  · intro h s c hsum i hi
    apply h s c
    · rw [← fieldLinearCombination_eq_mathlib e]
      exact hsum
    · exact hi

private theorem fieldSpans_iff_mathlib {K L ι : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) (v : ι → L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    FieldSpans e v ↔ Submodule.span K (Set.range v) = ⊤ := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  constructor
  · intro hspan
    apply top_unique
    intro x hx
    obtain ⟨s, c, hc⟩ := hspan x
    rw [← hc, fieldLinearCombination_eq_mathlib e]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro hspan x
    have hx : x ∈ Submodule.span K (Set.range v) := by
      rw [hspan]
      trivial
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
    refine ⟨c.support, fun i => c i, ?_⟩
    rw [fieldLinearCombination_eq_mathlib e]
    exact hc

private theorem fieldBasis_iff_mathlib {K L ι : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) (v : ι → L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    FieldBasis e v ↔ ∃ b : Module.Basis ι K L, ⇑b = v := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  constructor
  · rintro ⟨hli, hspan⟩
    have hli' : LinearIndependent K v :=
      (fieldLinearlyIndependent_iff_mathlib e v).mp hli
    have hspan' : Submodule.span K (Set.range v) = ⊤ :=
      (fieldSpans_iff_mathlib e v).mp hspan
    let b : Module.Basis ι K L := Module.Basis.mk hli' hspan'.ge
    refine ⟨b, ?_⟩
    simp [b]
  · rintro ⟨b, rfl⟩
    exact ⟨(fieldLinearlyIndependent_iff_mathlib e _).mpr b.linearIndependent,
      (fieldSpans_iff_mathlib e _).mpr b.span_eq⟩

private theorem mathlibBasis_to_fieldBasis {K L ι : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    ∀ b : Module.Basis ι K L, FieldBasis e (fun i => b i) := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  intro b
  apply (fieldBasis_iff_mathlib e _).mpr
  exact ⟨b, rfl⟩

private theorem finFieldBasis_iff_fieldBasis_bridge {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) {n : ℕ} (v : Fin n → L) :
    FinFieldBasis e v ↔ FieldBasis e v := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  constructor
  · rintro ⟨hli, hspan⟩
    constructor
    · apply (fieldLinearlyIndependent_iff_mathlib e v).mpr
      apply Fintype.linearIndependent_iff.mpr
      intro c hc i
      apply hli c
      rw [fieldLinearCombination_eq_mathlib e]
      exact hc
    · intro x
      obtain ⟨c, hc⟩ := hspan x
      exact ⟨Finset.univ, c, hc⟩
  · rintro ⟨hli, hspan⟩
    constructor
    · have hli' : LinearIndependent K v :=
        (fieldLinearlyIndependent_iff_mathlib e v).mp hli
      intro c hc i
      apply Fintype.linearIndependent_iff.mp hli' c
      rw [← fieldLinearCombination_eq_mathlib e]
      exact hc
    · intro x
      have hx : x ∈ Submodule.span K (Set.range v) := by
        rw [(fieldSpans_iff_mathlib e v).mp hspan]
        trivial
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
      refine ⟨c, ?_⟩
      rw [fieldLinearCombination_eq_mathlib e]
      exact hc

private theorem finFieldBasis_coordinates_package {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) {n : ℕ} {b : Fin n → L}
    (hb : FinFieldBasis e b) :
    (∀ x : L, ∃ c : Fin n → K,
      fieldLinearCombination e Finset.univ c b = x) ∧
    (∀ x : L, ∀ c d : Fin n → K,
      fieldLinearCombination e Finset.univ c b = x →
      fieldLinearCombination e Finset.univ d b = x → c = d) := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  constructor
  · exact hb.2
  · intro x c d hc hd
    have hrel : fieldLinearCombination e Finset.univ (fun i => c i - d i) b = 0 := by
      rw [fieldLinearCombination_eq_mathlib e]
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib]
      have hc' : (∑ i, c i • b i) = x := by
        rw [← fieldLinearCombination_eq_mathlib e]
        exact hc
      have hd' : (∑ i, d i • b i) = x := by
        rw [← fieldLinearCombination_eq_mathlib e]
        exact hd
      rw [hc', hd', sub_self]
    have hz : ∀ i, c i - d i = 0 := hb.1 (fun i => c i - d i) hrel
    funext i
    exact sub_eq_zero.mp (hz i)

private theorem finFieldBasis_card_eq_bridge {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) {m n : ℕ} {b : Fin m → L} {c : Fin n → L}
    (hb : FinFieldBasis e b) (hc : FinFieldBasis e c) : m = n := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  obtain ⟨B, hB⟩ := (fieldBasis_iff_mathlib e b).mp
    ((finFieldBasis_iff_fieldBasis_bridge e b).mp hb)
  obtain ⟨C, hC⟩ := (fieldBasis_iff_mathlib e c).mp
    ((finFieldBasis_iff_fieldBasis_bridge e c).mp hc)
  have hm : Module.finrank K L = m := by
    simpa using Module.finrank_eq_card_basis B
  have hn : Module.finrank K L = n := by
    simpa using Module.finrank_eq_card_basis C
  exact hm.symm.trans hn

private theorem extensionDegree_basic_package {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) :
    ¬HasExtensionDegree e 0 ∧
      (∀ n, HasExtensionDegree e n → 0 < n) ∧
      (∀ m n, HasExtensionDegree e m → HasExtensionDegree e n → m = n) := by
  have hzero : ¬HasExtensionDegree e 0 := by
    rintro ⟨b, hb⟩
    obtain ⟨c, hc⟩ := hb.2 (1 : L)
    have hempty : fieldLinearCombination e Finset.univ c b = 0 := by
      simp [fieldLinearCombination]
    rw [hempty] at hc
    exact zero_ne_one hc
  refine ⟨hzero, ?_, ?_⟩
  · intro n hn
    exact Nat.pos_of_ne_zero (fun hn0 => hzero (hn0 ▸ hn))
  · intro m n hm hn
    obtain ⟨b, hb⟩ := hm
    obtain ⟨c, hc⟩ := hn
    exact finFieldBasis_card_eq_bridge e hb hc

private theorem identity_degree_package (K : Type*) [Field K] :
    FinFieldBasis (FieldEmbedding.id K) (fun _ : Fin 1 => (1 : K)) ∧
      HasExtensionDegree (FieldEmbedding.id K) 1 ∧
      (∀ n, HasExtensionDegree (FieldEmbedding.id K) n ↔ n = 1) := by
  let e := FieldEmbedding.id K
  let b : Fin 1 → K := fun _ => 1
  have hb : FinFieldBasis e b := by
    constructor
    · intro c hc i
      have hc0 : c 0 = 0 := by
        simpa [fieldLinearCombination, e, b, FieldEmbedding.id] using hc
      simpa [Fin.eq_zero i] using hc0
    · intro x
      refine ⟨fun _ => x, ?_⟩
      simp [fieldLinearCombination, e, b, FieldEmbedding.id]
  have hdegree : HasExtensionDegree e 1 := ⟨b, hb⟩
  refine ⟨hb, hdegree, ?_⟩
  intro n
  constructor
  · intro hn
    exact (extensionDegree_basic_package e).2.2 n 1 hn hdegree
  · intro hn
    subst n
    exact hdegree

private theorem mathlib_isAlgebraic_to_algebraicElement {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L) (a : L) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    IsAlgebraic K a → AlgebraicElement e a := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  rintro ⟨p, hp, hev⟩
  refine ⟨p, hp, ?_⟩
  rw [Polynomial.aeval_def, toAlgebra_algebraMap_eq] at hev
  exact hev

private theorem finite_extension_isAlgebraic_bridge {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L)
    (hfin : FiniteFieldExtension e) : AlgebraicExtension e := by
  obtain ⟨n, b, hb⟩ := hfin
  letI : Algebra K L := e.toRingHom.toAlgebra
  obtain ⟨B, hB⟩ := (fieldBasis_iff_mathlib e b).mp
    ((finFieldBasis_iff_fieldBasis_bridge e b).mp hb)
  letI : Module.Finite K L := Module.Finite.of_basis B
  intro a
  exact mathlib_isAlgebraic_to_algebraicElement e a (IsAlgebraic.of_finite K a)

private theorem embedding_scalarTower {K L M : Type*} [Field K] [Field L] [Field M]
    (e : FieldEmbedding K L) (f : FieldEmbedding L M) :
    letI : Algebra K L := e.toRingHom.toAlgebra
    letI : Algebra L M := f.toRingHom.toAlgebra
    letI : Algebra K M := (f.comp e).toRingHom.toAlgebra
    IsScalarTower K L M := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  letI : Algebra L M := f.toRingHom.toAlgebra
  letI : Algebra K M := (f.comp e).toRingHom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  rw [toAlgebra_algebraMap_eq, toAlgebra_algebraMap_eq,
    toAlgebra_algebraMap_eq]
  rfl

private theorem towerBasisFamily_fieldBasis_bridge {K L M : Type*}
    [Field K] [Field L] [Field M]
    (e : FieldEmbedding K L) (f : FieldEmbedding L M)
    {m n : ℕ} {b : Fin m → L} {c : Fin n → M}
    (hb : FinFieldBasis e b) (hc : FinFieldBasis f c) :
    FieldBasis (f.comp e) (fun ij : Fin m × Fin n => f (b ij.1) * c ij.2) := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  letI : Algebra L M := f.toRingHom.toAlgebra
  letI : Algebra K M := (f.comp e).toRingHom.toAlgebra
  letI : IsScalarTower K L M := embedding_scalarTower e f
  obtain ⟨bKL, hbKL⟩ := (fieldBasis_iff_mathlib e b).mp
    ((finFieldBasis_iff_fieldBasis_bridge e b).mp hb)
  obtain ⟨bLM, hbLM⟩ := (fieldBasis_iff_mathlib f c).mp
    ((finFieldBasis_iff_fieldBasis_bridge f c).mp hc)
  let B : Module.Basis (Fin m × Fin n) K M := bKL.smulTower bLM
  have hB : (fun ij => B ij) = (fun ij : Fin m × Fin n => f (b ij.1) * c ij.2) := by
    funext ij
    rw [show B ij = bKL ij.1 • bLM ij.2 by
      exact Module.Basis.smulTower_apply bKL bLM ij]
    rw [algebra_smul_eq_embedding_mul f, hbKL, hbLM]
  rw [← hB]
  exact mathlibBasis_to_fieldBasis (f.comp e) B

private theorem fieldBasis_reindex_bridge {K L ι κ : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L)
    (v : ι → L) (h : ι ≃ κ) (hv : FieldBasis e v) :
    FieldBasis e (fun j : κ => v (h.symm j)) := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  obtain ⟨b, hb⟩ := (fieldBasis_iff_mathlib e v).mp hv
  apply (fieldBasis_iff_mathlib e _).mpr
  refine ⟨b.reindex h, ?_⟩
  funext j
  rw [Module.Basis.reindex_apply, hb]

/-! ## 有限基与坐标 -/

/-- `Fin n` 全指标基与一般教材域基等价。
有限指标类型允许把任意有限支撑关系统一
扩张到 `Finset.univ`，反向则直接把全指标关系视为一般有限关系。

> **Entry**: abstract-algebra.field.degree
@isnad1 id=iff.0h5v.s5.7a7083c96404 from=translated src=- shape=a1a76dd6 vocab=38a42763
-/
theorem finFieldBasis_iff_fieldBasis {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) {n : ℕ} (v : Fin n → L) :
    FinFieldBasis e v ↔ FieldBasis e v := by
  exact finFieldBasis_iff_fieldBasis_bridge e v

/-- 有限域基下每个元素都存在坐标。
所得系数函数以 `Fin n → K` 表示，其显式有限
线性组合在嵌入 `e` 下恰好等于给定元素。

> **Entry**: abstract-algebra.field.degree
@isnad1 id=ex.1h6v.s5.c4688cb2a65f from=translated src=- shape=5a151e0e vocab=ee173f7f
-/
theorem finFieldBasis_coordinates_exists {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) {n : ℕ} {b : Fin n → L}
    (hb : FinFieldBasis e b) (x : L) :
    ∃ c : Fin n → K, fieldLinearCombination e Finset.univ c b = x := by
  exact (finFieldBasis_coordinates_package e hb).1 x

/-- 有限域基下表示同一元素的两组坐标相等。
证明把两组表示相减形成零线性关系，
再由有限基的线性无关部分逐坐标消去。

> **Entry**: abstract-algebra.field.degree
@isnad1 id=eq.3h8v.s6.a4cdf4714e7f from=translated src=- shape=2d7f067a vocab=ee173f7f
-/
theorem finFieldBasis_coordinates_unique {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) {n : ℕ} {b : Fin n → L}
    (hb : FinFieldBasis e b) (x : L) {c d : Fin n → K}
    (hc : fieldLinearCombination e Finset.univ c b = x)
    (hd : fieldLinearCombination e Finset.univ d b = x) : c = d := by
  exact (finFieldBasis_coordinates_package e hb).2 x c d hc hd

/-- 有限域基下每个元素存在唯一坐标函数。
该定理把前述坐标存在性和坐标唯一性
组装为教材常用的 `∃!` 形式。

> **Entry**: abstract-algebra.field.degree
@isnad1 id=existsun.1h6v.s5.06ea0ab69eb3 from=translated src=- shape=5a151e0e vocab=ad2e9eb4
-/
theorem finFieldBasis_coordinates_exists_unique {K L : Type*}
    [Field K] [Field L] (e : FieldEmbedding K L)
    {n : ℕ} {b : Fin n → L} (hb : FinFieldBasis e b) (x : L) :
    ∃! c : Fin n → K, fieldLinearCombination e Finset.univ c b = x := by
  obtain ⟨c, hc⟩ := (finFieldBasis_coordinates_package e hb).1 x
  exact ⟨c, hc, fun d hd => (finFieldBasis_coordinates_package e hb).2 x d c hd hc⟩

/-! ## 扩张次数及其基础性质 -/

/-- 同一显式扩张的两组有限基具有相同长度。
私有证明后端把它们转成 Mathlib 基并
比较有限维数，公开结论只保留两个自然数相等。

> **Entry**: abstract-algebra.field.degree
@isnad1 id=eq.2h7v.s5.86202bbc4fe6 from=translated src=- shape=a3a0ab72 vocab=44961fac
-/
theorem fieldExtensionBasis_card_eq {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) {m n : ℕ} {b : Fin m → L} {c : Fin n → L}
    (hb : FinFieldBasis e b) (hc : FinFieldBasis e c) : m = n := by
  exact finFieldBasis_card_eq_bridge e hb hc

/-- 显式扩张次数若存在则唯一。
任意两个 `HasExtensionDegree` 见证都给出有限基，
故由有限基长度不变性得到相同次数。

> **Entry**: abstract-algebra.field.degree
@isnad1 id=eq.2h5v.s5.9d7270736f72 from=translated src=- shape=cab1b648 vocab=347fc93e
-/
theorem extensionDegree_unique {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) {m n : ℕ}
    (hm : HasExtensionDegree e m) (hn : HasExtensionDegree e n) : m = n := by
  exact (extensionDegree_basic_package e).2.2 m n hm hn

/-- 域扩张不可能具有零维域基。
因为 `Fin 0` 上的线性组合恒为零，它无法表示目标域
中的单位元 `1`。

> **Entry**: abstract-algebra.field.degree
@isnad1 id=not.0h3v.s4.32f083f407bf from=translated src=- shape=67f0fbbb vocab=347fc93e
-/
theorem not_hasExtensionDegree_zero {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) : ¬HasExtensionDegree e 0 := by
  exact (extensionDegree_basic_package e).1

/-- 任意存在的扩张次数严格为正。
该结论由零维不可能性排除 `n = 0`，给出教材中
有限扩张次数总为正整数的表述。

> **Entry**: abstract-algebra.field.degree
@isnad1 id=lt.1h4v.s5.6a0fd54b94e8 from=translated src=- shape=dd36aeb2 vocab=baa47e80
-/
theorem extensionDegree_pos {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) {n : ℕ} (hn : HasExtensionDegree e n) : 0 < n := by
  exact (extensionDegree_basic_package e).2.1 n hn

/-! ## 恒等扩张 -/

/-- 恒等扩张以 `1` 为单个基向量。
任意元素就是自身乘以 `1`，而一项零线性关系
立即迫使唯一系数为零。

> **Entry**: abstract-algebra.field.degree
@isnad1 id=finfield.0h1v.s5.be127342122f from=translated src=- shape=63349176 vocab=14d7d937
-/
theorem finFieldBasis_id_one (K : Type*) [Field K] :
    FinFieldBasis (FieldEmbedding.id K) (fun _ : Fin 1 => (1 : K)) := by
  exact (identity_degree_package K).1

/-- 恒等扩张的次数为一。该结果以显式的一元基为见证，直接建立
`HasExtensionDegree (FieldEmbedding.id K) 1`。

> **Entry**: abstract-algebra.field.degree
@isnad1 id=hasexten.0h1v.s4.1222da994e23 from=translated src=- shape=f3cef437 vocab=680e6728
-/
theorem extensionDegree_id_one (K : Type*) [Field K] :
    HasExtensionDegree (FieldEmbedding.id K) 1 := by
  exact (identity_degree_package K).2.1

/-- 恒等扩张具有次数 `n` 当且仅当 `n = 1`。
正向由次数唯一性与已构造的一元基
得到，反向则把等式改写后复用次数为一的见证。

> **Entry**: abstract-algebra.field.degree
@isnad1 id=iff.0h2v.s4.48be59f9b9c8 from=translated src=- shape=a4406793 vocab=680e6728
-/
theorem extensionDegree_id_iff (K : Type*) [Field K] (n : ℕ) :
    HasExtensionDegree (FieldEmbedding.id K) n ↔ n = 1 := by
  exact (identity_degree_package K).2.2 n

/-! ## 有限扩张与代数性 -/

/-- 每个有限域扩张都是代数扩张。
证明后端由有限基安装有限生成结构，调用成熟的
有限扩张代数性定理，再桥回 A3.5 的显式 `AlgebraicElement`。

> **Entry**: abstract-algebra.field.degree
@isnad1 id=algebrai.1h3v.s4.3b1d3b7e81e1 from=translated src=- shape=f61ba1fe vocab=5a18151c
-/
theorem finiteFieldExtension_isAlgebraic {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (hfin : FiniteFieldExtension e) :
    AlgebraicExtension e := by
  exact finite_extension_isAlgebraic_bridge e hfin

/-! ## 扩张塔 -/

/-- 两层有限基的乘积族：先把下层基向量通过 `f` 嵌入顶层，
再乘以上层基向量。
指标对 `(i, j)` 因而对应乘积 `f (b i) * c j`。

> **Entry**: abstract-algebra.field.degree-/
def towerBasisFamily {L M : Type*} [Field L] [Field M]
    (f : FieldEmbedding L M) {m n : ℕ}
    (b : Fin m → L) (c : Fin n → M) : Fin m × Fin n → M :=
  fun ij => f (b ij.1) * c ij.2

/-- 两层有限基的乘积族构成复合扩张的一般教材基。
私有证明用标量塔上的基乘积
验证线性无关与张成，公开结论仍使用显式 `FieldBasis`。

> **Entry**: abstract-algebra.field.degree
@isnad1 id=fieldbas.2h9v.s6.b465456bdcd7 from=translated src=- shape=441a1837 vocab=bd90c840
-/
theorem towerBasisFamily_isBasis {K L M : Type*} [Field K] [Field L] [Field M]
    (e : FieldEmbedding K L) (f : FieldEmbedding L M)
    {m n : ℕ} {b : Fin m → L} {c : Fin n → M}
    (hb : FinFieldBasis e b) (hc : FinFieldBasis f c) :
    FieldBasis (f.comp e) (towerBasisFamily f b c) := by
  exact towerBasisFamily_fieldBasis_bridge e f hb hc

/-- 一般域基可沿指标等价重新编号。
新族在指标 `j` 处取原族的 `h.symm j` 项，
因此只改变编号而不改变向量集合、线性无关性或张成性。

> **Entry**: abstract-algebra.field.degree
@isnad1 id=fieldbas.1h7v.s6.fa29848ed1b1 from=translated src=- shape=1373fd67 vocab=b8053ec8
-/
theorem fieldBasis_reindex {K L ι κ : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) (v : ι → L) (h : ι ≃ κ)
    (hv : FieldBasis e v) : FieldBasis e (fun j : κ => v (h.symm j)) := by
  exact fieldBasis_reindex_bridge e v h hv

private theorem extensionDegree_tower_bridge {K L M : Type*}
    [Field K] [Field L] [Field M]
    (e : FieldEmbedding K L) (f : FieldEmbedding L M) {m n : ℕ}
    (he : HasExtensionDegree e m) (hf : HasExtensionDegree f n) :
    HasExtensionDegree (f.comp e) (m * n) := by
  obtain ⟨b, hb⟩ := he
  obtain ⟨c, hc⟩ := hf
  have hprod : FieldBasis (f.comp e) (towerBasisFamily f b c) :=
    towerBasisFamily_isBasis e f hb hc
  have hreindexed :
      FieldBasis (f.comp e)
        (fun k : Fin (m * n) => towerBasisFamily f b c (finProdFinEquiv.symm k)) :=
    fieldBasis_reindex (f.comp e) (towerBasisFamily f b c) finProdFinEquiv hprod
  refine ⟨fun k => towerBasisFamily f b c (finProdFinEquiv.symm k), ?_⟩
  exact (finFieldBasis_iff_fieldBasis (f.comp e) _).mpr hreindexed

/-- 有限扩张塔的复合次数等于两层次数之积。
乘积基先由 `Fin m × Fin n` 编号，
再通过标准等价重编号为 `Fin (m * n)`。

> **Entry**: abstract-algebra.field.degree
@isnad1 id=hasexten.2h7v.s6.2268ec51be72 from=translated src=- shape=f2c76f6a vocab=a7110e05
-/
theorem extensionDegree_tower {K L M : Type*} [Field K] [Field L] [Field M]
    (e : FieldEmbedding K L) (f : FieldEmbedding L M) {m n : ℕ}
    (he : HasExtensionDegree e m) (hf : HasExtensionDegree f n) :
    HasExtensionDegree (f.comp e) (m * n) := by
  exact extensionDegree_tower_bridge e f he hf

private theorem finiteFieldExtension_comp_bridge {K L M : Type*}
    [Field K] [Field L] [Field M]
    (e : FieldEmbedding K L) (f : FieldEmbedding L M)
    (he : FiniteFieldExtension e) (hf : FiniteFieldExtension f) :
    FiniteFieldExtension (f.comp e) := by
  obtain ⟨m, hm⟩ := he
  obtain ⟨n, hn⟩ := hf
  exact ⟨m * n, extensionDegree_tower_bridge e f hm hn⟩

/-- 两个有限域扩张的复合仍为有限域扩张。
分别取两层有限次数见证后，塔式乘法定理
给出复合嵌入的有限次数见证。

> **Entry**: abstract-algebra.field.degree
@isnad1 id=finitefi.2h5v.s5.38d1d15c684b from=translated src=- shape=0718caa8 vocab=42cef999
-/
theorem finiteFieldExtension_comp {K L M : Type*} [Field K] [Field L] [Field M]
    (e : FieldEmbedding K L) (f : FieldEmbedding L M)
    (he : FiniteFieldExtension e) (hf : FiniteFieldExtension f) :
    FiniteFieldExtension (f.comp e) := by
  exact finiteFieldExtension_comp_bridge e f he hf

end SandronesLibrary.AbstractAlgebra.FieldDegree

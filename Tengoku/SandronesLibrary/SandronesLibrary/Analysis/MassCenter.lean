/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.JordanRegion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 质量、重心与转动惯量

本模块给出华东师大《数学分析》多元积分应用中区域的质量、静矩（一阶矩）、重心
（质心）与转动惯量的教材接口。所有量都是带密度 `ρ` 的区域 `D` 上的
Lebesgue/Bochner 集积分；区域沿用 `JordanEuc n = Fin n → ℝ` 这一载体。

> **Entry**: analysis.coordinate-integrals.mass-center

物理与教材含义：

- `mass ρ D = ∫_D ρ`：区域质量；
- `firstMoment ρ D i = ∫_D xᵢ ρ`：关于坐标平面 `xᵢ = 0` 的一阶矩（静矩）；
- `centroid ρ D i = firstMoment ρ D i / mass ρ D`：重心的第 `i` 个坐标（在
  `mass ρ D ≠ 0` 时有意义）；
- `secondMoment ρ D i = ∫_D xᵢ² ρ`：关于坐标平面 `xᵢ = 0` 的转动惯量（二阶矩）；
- `momentOfInertia ρ D c = ∫_D euclideanNormSq (x - c) ρ`：关于点 `c` 的转动惯量。

关于范数的说明：载体 `JordanEuc n = Fin n → ℝ` 在 Mathlib 中默认带乘积（上确界）
范数，而不是欧氏范数；教材的转动惯量使用欧氏距离，因此本模块显式引入
`euclideanNormSq v = ∑ i, vᵢ²`，它与 `EuclideanSpace ℝ (Fin n)` 上的平方范数一致，
并在 `n = 2, 3` 时分别是 `x²+y²` 与 `x²+y²+z²`。

接口对区域和密度不作全局假设：需要可积性、可测性或非负性的定理都在假设中显式给出，
以便与库内 Jordan 可测区域和换元/矩形积分接口自由组合。
-/

noncomputable section

namespace SandronesLibrary.Analysis.MassCenter

open Set MeasureTheory
open SandronesLibrary.Analysis.Multivariable

/-- `JordanEuc n` 上显式的**欧氏范数平方**：`euclideanNormSq v = ∑ i, vᵢ²`。

之所以不使用 `‖v‖²`，是因为 `Fin n → ℝ` 在 Mathlib 中默认带乘积（上确界）范数；
见模块文档的范数说明。-/
def euclideanNormSq {n : ℕ} (v : JordanEuc n) : ℝ :=
  ∑ i, (v i) ^ 2

/-- 区域 `D` 关于密度 `ρ` 的**质量**：`mass ρ D = ∫_D ρ`。

> **Entry**: analysis.coordinate-integrals.mass-center-/
def mass {n : ℕ} (ρ : JordanEuc n → ℝ) (D : Set (JordanEuc n)) : ℝ :=
  ∫ x in D, ρ x

/-- 关于坐标平面 `xᵢ = 0` 的**一阶矩（静矩）**：`firstMoment ρ D i = ∫_D xᵢ ρ`。-/
def firstMoment {n : ℕ} (ρ : JordanEuc n → ℝ) (D : Set (JordanEuc n)) (i : Fin n) : ℝ :=
  ∫ x in D, x i * ρ x

/-- 区域 `D` 关于密度 `ρ` 的**重心（质心）**的第 `i` 个坐标：

`centroid ρ D i = (∫_D xᵢ ρ) / (∫_D ρ)`。

定义为全函数；当 `mass ρ D ≠ 0` 时它才是物理意义上的重心坐标。-/
def centroid {n : ℕ} (ρ : JordanEuc n → ℝ) (D : Set (JordanEuc n)) (i : Fin n) : ℝ :=
  firstMoment ρ D i / mass ρ D

/-- 关于点 `c` 的**转动惯量**：`momentOfInertia ρ D c = ∫_D euclideanNormSq (x - c) ρ`，
即按坐标展开的 `∫_D (∑ᵢ (xᵢ - cᵢ)²) ρ`。

当 `c = 0` 时即关于坐标原点的转动惯量。-/
def momentOfInertia {n : ℕ} (ρ : JordanEuc n → ℝ) (D : Set (JordanEuc n))
    (c : JordanEuc n) : ℝ :=
  ∫ x in D, euclideanNormSq (x - c) * ρ x

/-- 关于坐标平面 `xᵢ = 0` 的**二阶矩（转动惯量）**：`secondMoment ρ D i = ∫_D xᵢ² ρ`。-/
def secondMoment {n : ℕ} (ρ : JordanEuc n → ℝ) (D : Set (JordanEuc n)) (i : Fin n) : ℝ :=
  ∫ x in D, (x i) ^ 2 * ρ x

/-! ## 质量的基础性质 -/

/-- 非负密度在区域上的质量非负。
@isnad1 id=le.2h3v.s6.457eae4e49a1 from=translated src=- shape=8252bb17 vocab=0a350760
-/
theorem mass_nonneg {n : ℕ} {ρ : JordanEuc n → ℝ} {D : Set (JordanEuc n)}
    (hnull : NullMeasurableSet D volume) (hρ : ∀ x ∈ D, 0 ≤ ρ x) : 0 ≤ mass ρ D := by
  rw [mass]
  have h : ∀ᵐ x ∂volume.restrict D, 0 ≤ ρ x := by
    rw [ae_restrict_iff'₀ hnull]
    exact Filter.Eventually.of_forall fun x hx => hρ x hx
  exact setIntegral_nonneg_of_ae_restrict h

/-- Jordan 可测区域上非负密度的质量非负。
@isnad1 id=le.2h3v.s5.03d166b445e4 from=translated src=- shape=d9f4aba9 vocab=4b2a8bbd
-/
theorem isJordanMeasurable_mass_nonneg {n : ℕ} {ρ : JordanEuc n → ℝ}
    {D : Set (JordanEuc n)} (hD : IsJordanMeasurable D) (hρ : ∀ x ∈ D, 0 ≤ ρ x) :
    0 ≤ mass ρ D :=
  mass_nonneg hD.nullMeasurableSet hρ

/-- 质量在不相交的可测并上可加。
@isnad1 id=eq.4h4v.s7.4a097885e2ad from=translated src=- shape=ab017309 vocab=33c775a8
-/
theorem mass_add {n : ℕ} {ρ : JordanEuc n → ℝ} {D E : Set (JordanEuc n)}
    (hDE : Disjoint D E) (hE : MeasurableSet E) (hρD : IntegrableOn ρ D volume)
    (hρE : IntegrableOn ρ E volume) : mass ρ (D ∪ E) = mass ρ D + mass ρ E := by
  simp only [mass]
  exact setIntegral_union hDE hE hρD hρE

/-- 质量在不相交的零可测并上可加（只需一侧零可测）。
@isnad1 id=eq.4h4v.s7.4e7d40cc587a from=translated src=- shape=64eb5fd2 vocab=9631ad8d
-/
theorem mass_add_of_disjoint {n : ℕ} {ρ : JordanEuc n → ℝ} {D E : Set (JordanEuc n)}
    (hDE : Disjoint D E) (hE : NullMeasurableSet E volume) (hρD : IntegrableOn ρ D volume)
    (hρE : IntegrableOn ρ E volume) : mass ρ (D ∪ E) = mass ρ D + mass ρ E := by
  simp only [mass]
  exact setIntegral_union₀ hDE.aedisjoint hE hρD hρE

/-- 质量在差集上去掉可测部分时作差。
@isnad1 id=eq.3h4v.s6.0df1678eeb39 from=translated src=- shape=d213dfdb vocab=4756a603
-/
theorem mass_sub {n : ℕ} {ρ : JordanEuc n → ℝ} {D E : Set (JordanEuc n)}
    (hE : MeasurableSet E) (hED : E ⊆ D) (hρD : IntegrableOn ρ D volume) :
    mass ρ (D \ E) = mass ρ D - mass ρ E := by
  simp only [mass]
  exact setIntegral_sdiff hE hρD hED

/-- 密度乘以常数则质量乘以该常数（质量关于密度的线性性）。
@isnad1 id=eq.0h4v.s5.5cf48756edbd from=translated src=- shape=d3dd3b49 vocab=1bc3573f
-/
theorem mass_smul {n : ℕ} (ρ : JordanEuc n → ℝ) (D : Set (JordanEuc n)) (c : ℝ) :
    mass (fun x => c * ρ x) D = c * mass ρ D := by
  simp only [mass]
  rw [integral_const_mul]

/-- 常数密度 `c` 在区域上的质量等于 `c` 乘区域的实体积。
@isnad1 id=eq.0h3v.s5.3a20259b27e8 from=translated src=- shape=31721f35 vocab=f8d0bd24
-/
theorem mass_const {n : ℕ} (D : Set (JordanEuc n)) (c : ℝ) :
    mass (fun _ => c) D = c * volume.real D := by
  rw [mass, setIntegral_const, smul_eq_mul, mul_comm]

/-- 密度恒为 `1` 时质量就是区域的实体积：`mass 1 D = volume.real D`。

这是本模块与库内 Lebesgue 体积接口的直接联系。
@isnad1 id=eq.0h2v.s5.fa6b39a9ec0a from=translated src=- shape=1d2ba9bd vocab=5b306f28
-/
theorem mass_one_eq_measureReal {n : ℕ} (D : Set (JordanEuc n)) :
    mass (fun _ => (1 : ℝ)) D = volume.real D := by
  rw [mass_const, one_mul]

/-- 在可测区域上，质量只依赖于密度在区域上的点值。
@isnad1 id=eq.2h4v.s6.ccc5d17437d2 from=translated src=- shape=721f892b vocab=1bec7bbe
-/
theorem mass_congr {n : ℕ} {ρ σ : JordanEuc n → ℝ} {D : Set (JordanEuc n)}
    (hD : MeasurableSet D) (h : ∀ x ∈ D, ρ x = σ x) : mass ρ D = mass σ D := by
  simp only [mass]
  exact setIntegral_congr_fun hD h

/-! ## 一阶矩与重心的基础性质 -/

/-- 一阶矩关于密度线性。
@isnad1 id=eq.0h5v.s5.459161b8492d from=translated src=- shape=c97ad5f2 vocab=50b0652c
-/
theorem firstMoment_smul {n : ℕ} (ρ : JordanEuc n → ℝ) (D : Set (JordanEuc n))
    (i : Fin n) (c : ℝ) :
    firstMoment (fun x => c * ρ x) D i = c * firstMoment ρ D i := by
  simp only [firstMoment]
  have h : (fun x : JordanEuc n => x i * (c * ρ x)) = fun x => c * (x i * ρ x) := by
    funext x; ring
  rw [h, integral_const_mul]

/-- 缩放密度不改变重心（需要非零缩放因子与非零质量）。
@isnad1 id=eq.2h5v.s6.926573b521a5 from=translated src=- shape=cf8df1d6 vocab=58276201
-/
theorem centroid_smul {n : ℕ} {ρ : JordanEuc n → ℝ} {D : Set (JordanEuc n)} {i : Fin n}
    {c : ℝ} (hc : c ≠ 0) (hm : mass ρ D ≠ 0) :
    centroid (fun x => c * ρ x) D i = centroid ρ D i := by
  have hm' : mass (fun x => c * ρ x) D ≠ 0 := by
    rw [mass_smul]
    exact mul_ne_zero hc hm
  simp only [centroid, firstMoment_smul, mass_smul]
  rw [mul_div_mul_left _ _ hc]

/-! ## 二阶矩与转动惯量 -/

/-- 二阶矩关于密度线性。
@isnad1 id=eq.0h5v.s5.6365d6d5aa91 from=translated src=- shape=c97ad5f2 vocab=ef4e3888
-/
theorem secondMoment_smul {n : ℕ} (ρ : JordanEuc n → ℝ) (D : Set (JordanEuc n))
    (i : Fin n) (c : ℝ) :
    secondMoment (fun x => c * ρ x) D i = c * secondMoment ρ D i := by
  simp only [secondMoment]
  have h : (fun x : JordanEuc n => (x i) ^ 2 * (c * ρ x)) =
      fun x => c * ((x i) ^ 2 * ρ x) := by
    funext x; ring
  rw [h, integral_const_mul]

/-- 欧氏范数平方非负。
@isnad1 id=le.0h2v.s4.99681ca263ad from=translated src=- shape=9363a417 vocab=bcc8aaf2
-/
theorem euclideanNormSq_nonneg {n : ℕ} (v : JordanEuc n) : 0 ≤ euclideanNormSq v :=
  Finset.sum_nonneg fun i _ => sq_nonneg (v i)

/-- 欧氏范数平方的坐标展开：`euclideanNormSq (x - c) = ∑ i, (xᵢ - cᵢ)²`。
@isnad1 id=eq.0h3v.s6.71023294fe4a from=translated src=- shape=bf9d3e6b vocab=3c327987
-/
theorem euclideanNormSq_sub {n : ℕ} (x c : JordanEuc n) :
    euclideanNormSq (x - c) = ∑ i, (x i - c i) ^ 2 := by
  simp only [euclideanNormSq, Pi.sub_apply]

/-- 非负密度关于任意点的转动惯量非负。
@isnad1 id=le.2h4v.s6.fa7ee54ff04b from=translated src=- shape=b903318b vocab=4118f138
-/
theorem momentOfInertia_nonneg {n : ℕ} {ρ : JordanEuc n → ℝ} {D : Set (JordanEuc n)}
    {c : JordanEuc n} (hnull : NullMeasurableSet D volume) (hρ : ∀ x ∈ D, 0 ≤ ρ x) :
    0 ≤ momentOfInertia ρ D c := by
  rw [momentOfInertia]
  have h : ∀ᵐ x ∂volume.restrict D, 0 ≤ euclideanNormSq (x - c) * ρ x := by
    rw [ae_restrict_iff'₀ hnull]
    exact Filter.Eventually.of_forall fun x hx =>
      mul_nonneg (euclideanNormSq_nonneg _) (hρ x hx)
  exact setIntegral_nonneg_of_ae_restrict h

/-- Jordan 可测区域上非负密度的转动惯量非负。
@isnad1 id=le.2h4v.s5.40a163f9b1fc from=translated src=- shape=7036d108 vocab=9b5f54a5
-/
theorem isJordanMeasurable_momentOfInertia_nonneg {n : ℕ} {ρ : JordanEuc n → ℝ}
    {D : Set (JordanEuc n)} {c : JordanEuc n} (hD : IsJordanMeasurable D)
    (hρ : ∀ x ∈ D, 0 ≤ ρ x) : 0 ≤ momentOfInertia ρ D c :=
  momentOfInertia_nonneg hD.nullMeasurableSet hρ

/-- 转动惯量关于密度线性。
@isnad1 id=eq.0h5v.s5.33fb105cd494 from=translated src=- shape=7135b305 vocab=a1d2c6c9
-/
theorem momentOfInertia_smul {n : ℕ} (ρ : JordanEuc n → ℝ) (D : Set (JordanEuc n))
    (c : JordanEuc n) (k : ℝ) :
    momentOfInertia (fun x => k * ρ x) D c = k * momentOfInertia ρ D c := by
  simp only [momentOfInertia]
  have h : (fun x : JordanEuc n => euclideanNormSq (x - c) * (k * ρ x)) =
      fun x => k * (euclideanNormSq (x - c) * ρ x) := by
    funext x; ring
  rw [h, integral_const_mul]

/-- 关于原点的转动惯量：`momentOfInertia ρ D 0 = ∫_D euclideanNormSq x * ρ x`。
@isnad1 id=eq.0h3v.s6.2b80072563c6 from=translated src=- shape=918acf4a vocab=296fb48e
-/
theorem momentOfInertia_zero {n : ℕ} (ρ : JordanEuc n → ℝ) (D : Set (JordanEuc n)) :
    momentOfInertia ρ D 0 = ∫ x in D, euclideanNormSq x * ρ x := by
  simp only [momentOfInertia, sub_zero]

/-- **单坐标平行轴展开**：把 `(xᵢ - c)²` 展开后逐项积分，得到

`∫_D (xᵢ - c)² ρ = secondMoment ρ D i - 2 c firstMoment ρ D i + c² mass ρ D`。

这是经典平行轴恒等式的逐坐标版本，也是 `momentOfInertia_expansion` 的基础。
@isnad1 id=eq.3h5v.s8.71443361de29 from=translated src=- shape=71675ba4 vocab=6606b392
-/
theorem integral_sq_sub_center {n : ℕ} {ρ : JordanEuc n → ℝ} {D : Set (JordanEuc n)}
    {i : Fin n} {c : ℝ} (hρ : IntegrableOn ρ D volume)
    (h2 : IntegrableOn (fun x => (x i) ^ 2 * ρ x) D)
    (h1 : IntegrableOn (fun x => x i * ρ x) D) :
    (∫ x in D, (x i - c) ^ 2 * ρ x) =
      secondMoment ρ D i - 2 * c * firstMoment ρ D i + c ^ 2 * mass ρ D := by
  have hcross : IntegrableOn (fun x => (2 * c) * (x i * ρ x)) D := h1.const_mul (2 * c)
  have hconst : IntegrableOn (fun x => c ^ 2 * ρ x) D := hρ.const_mul (c ^ 2)
  have h2' : IntegrableOn (fun x => (x i) ^ 2 * ρ x - (2 * c) * (x i * ρ x)) D :=
    h2.sub hcross
  calc ∫ x in D, (x i - c) ^ 2 * ρ x
      = ∫ x in D, ((x i) ^ 2 * ρ x - (2 * c) * (x i * ρ x) + c ^ 2 * ρ x) := by
        apply integral_congr_ae
        filter_upwards with x
        ring
    _ = (∫ x in D, (x i) ^ 2 * ρ x) - (∫ x in D, (2 * c) * (x i * ρ x))
          + ∫ x in D, c ^ 2 * ρ x := by
        rw [integral_add h2' hconst, integral_sub h2 hcross]
    _ = secondMoment ρ D i - 2 * c * firstMoment ρ D i + c ^ 2 * mass ρ D := by
        rw [integral_const_mul, integral_const_mul]
        simp only [secondMoment, firstMoment, mass]

/-- 转动惯量的**平行轴展开**（平行轴定理的诚实弱形式）：把
`euclideanNormSq (x - c) ρ` 按坐标展开为 `∑ i, (xᵢ - cᵢ)² ρ`，逐坐标应用
`integral_sq_sub_center`，得到

`momentOfInertia ρ D c =
  ∑ i, (secondMoment ρ D i - 2 cᵢ firstMoment ρ D i + cᵢ² mass ρ D)`。

它不假设 `c` 是重心。取 `c := fun i => centroid ρ D i` 时，
`∑ᵢ cᵢ firstMoment ρ D i = mass ρ D · euclideanNormSq c`（=`m‖c‖²`），代入后得到
`momentOfInertia ρ D c = I₀ - m‖c‖²`，其中 `I₀ = ∑ i, secondMoment ρ D i` 是关于原点的转动惯量；
整理即经典平行轴定理 `I₀ = I_c + m‖c‖²`。**本定理只证明到展开恒等式这一层**，上述代入重心的
化简未在此证明。
@isnad1 id=eq.3h4v.s8.2049a7bab410 from=translated src=- shape=4a726241 vocab=87c1347f
-/
theorem momentOfInertia_expansion {n : ℕ} {ρ : JordanEuc n → ℝ} {D : Set (JordanEuc n)}
    {c : JordanEuc n} (hρ : IntegrableOn ρ D volume)
    (h2 : ∀ i, IntegrableOn (fun x => (x i) ^ 2 * ρ x) D)
    (h1 : ∀ i, IntegrableOn (fun x => x i * ρ x) D) :
    momentOfInertia ρ D c =
      ∑ i, (secondMoment ρ D i - 2 * (c i) * firstMoment ρ D i
        + (c i) ^ 2 * mass ρ D) := by
  have hterm : ∀ i, IntegrableOn (fun x => (x i - c i) ^ 2 * ρ x) D := by
    intro i
    have hcross : IntegrableOn (fun x => (2 * c i) * (x i * ρ x)) D :=
      (h1 i).const_mul (2 * c i)
    have hconst : IntegrableOn (fun x => (c i) ^ 2 * ρ x) D := hρ.const_mul ((c i) ^ 2)
    have hfun : (fun x : JordanEuc n => (x i - c i) ^ 2 * ρ x) =
        fun x => ((x i) ^ 2 * ρ x - (2 * c i) * (x i * ρ x) + (c i) ^ 2 * ρ x) := by
      funext x; ring
    rw [hfun]
    exact (h2 i).sub hcross |>.add hconst
  have hpt : (fun x : JordanEuc n => euclideanNormSq (x - c) * ρ x) =
      fun x => ∑ i, (x i - c i) ^ 2 * ρ x := by
    funext x
    rw [euclideanNormSq_sub, Finset.sum_mul]
  rw [momentOfInertia, hpt]
  rw [integral_finsetSum Finset.univ (fun i _ => hterm i)]
  exact Finset.sum_congr rfl fun i _ => integral_sq_sub_center hρ (h2 i) (h1 i)

/-- 平行轴展开的重排形式：把 `momentOfInertia_expansion` 中的有限和线性整理为

`momentOfInertia ρ D c =
  (∑ i, secondMoment ρ D i) - 2 (∑ i, cᵢ firstMoment ρ D i) + euclideanNormSq c · mass ρ D`。

取 `c := fun i => centroid ρ D i` 时第二项并不消失，而是
`2 (∑ i, cᵢ firstMoment ρ D i) = 2 m‖c‖²`（`m = mass ρ D`），故右端化为
`I₀ - m‖c‖²`，对应经典平行轴定理 `I₀ = I_c + m‖c‖²`。本定理本身只是展开恒等式的线性重排，
不含代入重心的化简。
@isnad1 id=eq.3h4v.s8.fa31e1a3d01e from=translated src=- shape=db696973 vocab=24fd287b
-/
theorem momentOfInertia_parallel_axis {n : ℕ} {ρ : JordanEuc n → ℝ}
    {D : Set (JordanEuc n)} {c : JordanEuc n} (hρ : IntegrableOn ρ D volume)
    (h2 : ∀ i, IntegrableOn (fun x => (x i) ^ 2 * ρ x) D)
    (h1 : ∀ i, IntegrableOn (fun x => x i * ρ x) D) :
    momentOfInertia ρ D c =
      (∑ i, secondMoment ρ D i) - 2 * (∑ i, c i * firstMoment ρ D i)
        + euclideanNormSq c * mass ρ D := by
  have hB : (∑ i, (2 * c i) * firstMoment ρ D i) =
      2 * ∑ i, c i * firstMoment ρ D i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hC : (∑ i, (c i) ^ 2 * mass ρ D) = (∑ i, (c i) ^ 2) * mass ρ D := by
    rw [Finset.sum_mul]
  rw [momentOfInertia_expansion hρ h2 h1, euclideanNormSq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hB, hC]

end SandronesLibrary.Analysis.MassCenter

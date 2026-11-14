/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.PiecewiseC1HomotopyInvariance
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.AdmissiblePathConnectivity
import Tengoku.Seed.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 同伦形式的 Cauchy 定理与单连通域原函数

本文件收口 C2 的同伦部分。已集成的
`complex-analysis.path-integral.piecewise-c1-homotopy-invariance` 给出「连续相对同伦加分段 C1 边界
蕴含积分不变」，但它以「已经给定同伦」为假设。教材的一般形式还要求另一半：在单连通开域中，
同端点道路之间的同伦由拓扑假设**自动提供**。补上这一半之后可以推出

* 可积正则道路的积分只依赖端点（`PathIntegralIndependentOn`）；
* 全纯函数在单连通开域上存在原函数（C2 的同伦部分收口点）；
* 闭分段 C1 道路的积分为零（教材形式的 Cauchy 定理）。

拓扑侧复用 Mathlib 的 `SimplyConnectedSpace` 子类型载体与其 `paths_homotopic`，并把子类型同伦
沿 `Subtype.val` 搬回复平面、逐点控制像集；分析侧消费本库已经验收的正则化桥、分段 C1 逼近与
端点控制链（dyadic alignment、indexed open-cover subdivision、raw grid 边界组装），不重新证明
它们，也不引入新的证明后端。

当前条目：

* `complex-analysis.cauchy.homotopy`。
-/

open Set Metric MeasureTheory
open scoped unitInterval Topology

namespace SandronesLibrary.ComplexAnalysis

open SandronesLibrary.Topology

noncomputable section

/-- 两条同端点道路在 `U` 内相对端点同伦：存在一个固定端点的连续道路同伦，其参数方形的像整体
落在 `U` 中。这是教材「`gamma` 与 `delta` 在 `U` 内同伦」的精确量词形式；与
`C2HomotopicWithin` 的区别是本定义不要求方形延拓的二阶连续可微性。

> **Entry**: complex-analysis.cauchy.homotopy-/
def HomotopicWithin (U : Set ℂ) {a b : ℂ} (gamma delta : Path a b) : Prop :=
  ∃ F : gamma.Homotopy delta, ∀ z : unitInterval × unitInterval, pathHomotopySquare F z ∈ U

/-- `HomotopicWithin` 的逐点展开：教材写法的 `∀ s t, F (s,t) ∈ U` 与方形载体
`pathHomotopySquare` 的写法等价。

> **Entry**: complex-analysis.cauchy.homotopy
@isnad1 id=iff.0h5v.s8.7abc0f279bd1 from=translated src=- shape=8959eafc vocab=4d2e913f
-/
theorem homotopicWithin_iff {U : Set ℂ} {a b : ℂ} (gamma delta : Path a b) :
    HomotopicWithin U gamma delta ↔
      ∃ F : gamma.Homotopy delta, ∀ s t : unitInterval, F (s, t) ∈ U := by
  constructor
  · rintro ⟨F, hF⟩
    exact ⟨F, fun s t => hF (s, t)⟩
  · rintro ⟨F, hF⟩
    exact ⟨F, fun z => hF z.1 z.2⟩

/-- 可积正则道路是分段 C1 道路：把原函数构造所用的 `AdmissiblePath` 承载接到同伦不变性所需的
`Path.PiecewiseC1` 承载上。归纳结构逐条对应，`PathIntegrable` 与像集信息在本条中不使用。

> **Entry**: complex-analysis.cauchy.homotopy
@isnad1 id=piecewis.1h5v.s5.736c626d6fe0 from=translated src=- shape=6b78d7af vocab=30888bf3
-/
theorem AdmissiblePath.piecewiseC1 {f : ℂ → ℂ} {U : Set ℂ} {a b : ℂ} {gamma : Path a b}
    (h : AdmissiblePath f U gamma) : Path.PiecewiseC1 gamma := by
  induction h with
  | of_contDiffOn gamma _ _ hregular => exact .of_contDiffOn gamma hregular
  | trans _ _ ihgamma ihdelta => exact .trans _ _ ihgamma ihdelta

/-- 单连通集合内的拓扑桥：任意两条同端点、像落在 `U` 内的连续道路都相对端点同伦，且同伦像留在
`U` 内。证明把两条道路提升为子类型 `U` 上的道路，用单连通性给出的子类型同伦，再沿
`Subtype.val` 搬回复平面；像集控制由子类型第二分量直接读出。道路本身无需分段 C1。

> **Entry**: complex-analysis.cauchy.homotopy
@isnad1 id=homotopi.5h5v.s7.fcdde2c7d881 from=translated src=- shape=fc6d1fb0 vocab=3e6bbb3c
-/
theorem homotopicWithin_of_isSimplyConnected {U : Set ℂ} (hU : IsSimplyConnected U)
    {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) (gamma delta : Path a b)
    (hgamma : ∀ t, gamma t ∈ U) (hdelta : ∀ t, delta t ∈ U) :
    HomotopicWithin U gamma delta := by
  classical
  let lift : (p : Path a b) → (∀ t, p t ∈ U) → Path (⟨a, ha⟩ : U) (⟨b, hb⟩ : U) :=
    fun p hp =>
      { toFun := fun t => ⟨p t, hp t⟩
        continuous_toFun := p.continuous.subtype_mk hp
        source' := Subtype.ext p.source
        target' := Subtype.ext p.target }
  have hsc : SimplyConnectedSpace U := hU
  obtain ⟨F'⟩ := SimplyConnectedSpace.paths_homotopic (lift gamma hgamma) (lift delta hdelta)
  refine ⟨F'.map ⟨Subtype.val, continuous_subtype_val⟩, ?_⟩
  intro z
  exact (F' z).2

/-- 教材形式的同伦不变性：全纯函数沿在 `U` 内相对端点同伦的两条分段 C1 道路积分相等。本条把已
集成的 `pathIntegral_eq_of_piecewiseC1_homotopyWithin` 的原始同伦假设包装成课程谓词
`HomotopicWithin`，正则化与消内部边的证明仍由该已验收条目承担。

> **Entry**: complex-analysis.cauchy.homotopy
@isnad1 id=eq.5h6v.s6.1ce388201001 from=translated src=- shape=f3d7b146 vocab=9aac8daa
-/
theorem pathIntegral_eq_of_homotopicWithin {U : Set ℂ} {f : ℂ → ℂ} {a b : ℂ}
    {gamma delta : Path a b} (hU : IsOpen U) (hf : HolomorphicOnTextbook f U)
    (hgamma : Path.PiecewiseC1 gamma) (hdelta : Path.PiecewiseC1 delta)
    (hhom : HomotopicWithin U gamma delta) :
    pathIntegral f gamma = pathIntegral f delta := by
  obtain ⟨F, hF⟩ := hhom
  exact pathIntegral_eq_of_piecewiseC1_homotopyWithin hU hf hgamma hdelta F hF

/-- 单连通开域上的一般同伦形式：两条同端点分段 C1 道路（像在 `U` 内）的路径积分相等。同伦本身
由 `homotopicWithin_of_isSimplyConnected` 提供，不需要使用者给出。

> **Entry**: complex-analysis.cauchy.homotopy
@isnad1 id=eq.7h6v.s7.8313414220d6 from=translated src=- shape=8884742e vocab=949cbfde
-/
theorem pathIntegral_eq_of_isSimplyConnected {U : Set ℂ} {f : ℂ → ℂ} {a b : ℂ}
    {gamma delta : Path a b} (hU : IsOpen U) (hf : HolomorphicOnTextbook f U)
    (hconn : IsSimplyConnected U) (hgamma : Path.PiecewiseC1 gamma)
    (hdelta : Path.PiecewiseC1 delta) (himg : ∀ t, gamma t ∈ U)
    (hdimg : ∀ t, delta t ∈ U) :
    pathIntegral f gamma = pathIntegral f delta := by
  have ha : a ∈ U := gamma.source ▸ himg 0
  have hb : b ∈ U := delta.target ▸ hdimg 1
  exact pathIntegral_eq_of_homotopicWithin hU hf hgamma hdelta
    (homotopicWithin_of_isSimplyConnected hconn ha hb gamma delta himg hdimg)

/-- 单连通开域上的路径无关性：可积正则道路的积分只依赖端点。这是原函数构造所缺的那一步。

> **Entry**: complex-analysis.cauchy.homotopy
@isnad1 id=pathinte.3h2v.s5.d33f360e68f0 from=translated src=- shape=9ecc0254 vocab=57ef1864
-/
theorem pathIntegralIndependentOn_of_isSimplyConnected {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : HolomorphicOnTextbook f U) (hconn : IsSimplyConnected U) :
    PathIntegralIndependentOn f U := by
  intro a b gamma delta hgamma hdelta
  have hrg : range gamma ⊆ U := hgamma.range_subset
  have hrd : range delta ⊆ U := hdelta.range_subset
  have ha : a ∈ U := hrg ⟨0, gamma.source⟩
  have hb : b ∈ U := hrd ⟨1, delta.target⟩
  exact pathIntegral_eq_of_homotopicWithin hU hf hgamma.piecewiseC1 hdelta.piecewiseC1
    (homotopicWithin_of_isSimplyConnected hconn ha hb gamma delta
      (fun t => hrg ⟨t, rfl⟩) (fun t => hrd ⟨t, rfl⟩))

/-- 单连通开域上的原函数存在性：C2 同伦部分的收口点。全纯函数在单连通开域上有原函数，于是其沿
可积正则道路的积分等于原函数在端点的差。证明把新证的路径无关性喂给
`exists_primitive_of_isSimplyConnected_of_pathIntegralIndependentOn`；后者只负责从基点的积分构造。

> **Entry**: complex-analysis.cauchy.homotopy
@isnad1 id=ex.3h2v.s6.4ae1830c6231 from=translated src=- shape=7df0f8c6 vocab=d2beaadc
-/
theorem exists_primitive_of_isSimplyConnected {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : HolomorphicOnTextbook f U) (hconn : IsSimplyConnected U) :
    ∃ g : ℂ → ℂ, ∀ z ∈ U, HasDerivAt g (f z) z :=
  exists_primitive_of_isSimplyConnected_of_pathIntegralIndependentOn hU hf hconn
    (pathIntegralIndependentOn_of_isSimplyConnected hU hf hconn)

/-- 单连通开域上的 Cauchy 定理：闭分段 C1 道路的积分为零。把闭路与常值道路比较，常值道路积分
为零。

> **Entry**: complex-analysis.cauchy.homotopy
@isnad1 id=eq.5h4v.s7.48e2cbe83ce9 from=translated src=- shape=60820a1e vocab=949cbfde
-/
theorem pathIntegral_eq_zero_of_isSimplyConnected {f : ℂ → ℂ} {U : Set ℂ} {a : ℂ}
    {gamma : Path a a} (hU : IsOpen U) (hf : HolomorphicOnTextbook f U)
    (hconn : IsSimplyConnected U) (hgamma : Path.PiecewiseC1 gamma)
    (himg : ∀ t, gamma t ∈ U) :
    pathIntegral f gamma = 0 := by
  have ha : a ∈ U := gamma.source ▸ himg 0
  rw [pathIntegral_eq_of_isSimplyConnected hU hf hconn hgamma (Path.piecewiseC1_refl a) himg
    (fun _ => ha)]
  simp [pathIntegral]

end

end SandronesLibrary.ComplexAnalysis

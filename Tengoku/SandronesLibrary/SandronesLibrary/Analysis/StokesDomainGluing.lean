/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.GreenGaussStokes

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 分段光滑区域的拼接与积分公式装配

本模块把 `GreenGaussStokes` 中已有的有限分片拼接层整理为“分段光滑区域”的教材概念。
一个分段光滑区域由有限个参数片组成：每个片有自己的参数域与拉回密度，公共边（二维）
或公共面（三维）由整数关联数记录方向和重数。只要整体外边界的每条边恰好是各片局部
边界关联数之和，内部公共边上的 `+1` 与 `-1` 就自动抵消，整体外边界积分等于各片内部
积分之和。

模块给出四类装配定理：

* `stokes_piecewiseSmoothRegion`：一般参数分片的外边界积分等于拉回密度在有限图册上的
  积分和；
* `stokes_closed_piecewiseSmoothRegion`：闭区域（外边界关联数全零）的内部总积分为零；
* `green_piecewiseSmoothRegion`：二维平面分片经 Green 公式装配到有限并区域；
* `gauss_piecewiseSmoothRegion`：三维体元分片经 Gauss 公式装配。

此外给出两片共享一条边、局部关联数相反时的显式抵消结果，以及一个用 `Finset` 索引
两个矩形参数片的可 inhabited 实例。

> **Entry**: analysis.stokes.domain-gluing
-/

noncomputable section

namespace SandronesLibrary.Analysis.StokesDomainGluing

open Set Finset MeasureTheory
open SandronesLibrary.Analysis.GreenGaussStokes

/-- **分段光滑区域的分析数据。**

`patches` 是有限个参数片，`edges` 是有限的边标签集合（三维时读作面标签）。
每个片 `i` 带有参数域 `parameterDomain i` 及其上的拉回密度 `pulledBackDensity i`；
`localIncidence i e` 记录边 `e` 在第 `i` 片局部边界中的方向与重数，
`externalIncidence e` 记录同一条边在整体外边界中的方向与重数。

结构与 `GreenFiniteDecomposition` 一样要求各片参数域可测、两两不交、密度可积；
额外的 `gluing` 字段是纯代数的拼接条件：整体外边界的每条边关联数等于各片局部关联数
之和。三维情形不共用本结构，而由 `gauss_piecewiseSmoothRegion` 直接接收
`GaussFiniteDecomposition`。-/
structure PiecewiseSmoothRegion {ι ε : Type*} (patches : Finset ι) (edges : Finset ε)
    (parameterDomain : ι → Set (ℝ × ℝ)) (pulledBackDensity : ι → ℝ × ℝ → ℝ)
    (localIncidence : ι → ε → ℤ) (externalIncidence : ε → ℤ) : Prop where
  measurable : ∀ i ∈ patches, MeasurableSet (parameterDomain i)
  pairwiseDisjoint : Set.Pairwise (↑patches) (Function.onFun Disjoint parameterDomain)
  integrable : ∀ i ∈ patches,
    IntegrableOn (pulledBackDensity i) (parameterDomain i) (volume.prod volume)
  gluing : ∀ e ∈ edges, externalIncidence e = ∑ i ∈ patches, localIncidence i e

/-- 当所有参数片共用同一个拉回密度 `curlDensity` 时，分段光滑区域的测度数据就是一
个 `GreenFiniteDecomposition`；这给出二维 Green 装配所需的桥。
@isnad1 id=greenfin.2h9v.s6.f1dfb24b58d3 from=translated src=- shape=6a653c7f vocab=28b7398f
-/
theorem PiecewiseSmoothRegion.toGreenFiniteDecomposition
    {ι ε : Type*} {patches : Finset ι} {edges : Finset ε}
    {parameterDomain : ι → Set (ℝ × ℝ)} {pulledBackDensity : ι → ℝ × ℝ → ℝ}
    {localIncidence : ι → ε → ℤ} {externalIncidence : ε → ℤ}
    (h : PiecewiseSmoothRegion patches edges parameterDomain pulledBackDensity
      localIncidence externalIncidence)
    (curlDensity : ℝ × ℝ → ℝ)
    (hdensity : ∀ i, pulledBackDensity i = curlDensity) :
    GreenFiniteDecomposition patches parameterDomain curlDensity where
  measurable := h.measurable
  pairwiseDisjoint := h.pairwiseDisjoint
  integrable := by
    intro i hi
    rw [← hdensity i]
    exact h.integrable i hi

/-- **分段光滑区域上的 Stokes 拼接定理。**

若分段光滑区域的分析数据成立，并且每个参数片上的局部 Stokes 公式把该片的有向边界
值表示为参数域上拉回外微分密度的积分，则整体外边界值等于所有参数片拉回密度积分之和
`finiteAtlasSurfaceIntegral`。

这是教材“把区域分成有限多个参数片、在每片上分别用 Stokes 公式、公共边相消”的代数
装配层：分析内容全部由假设 `hlocal` 提供，几何抵消由 `gluing` 保证。
@isnad1 id=eq.2h9v.s7.3f2cd20216cf from=translated src=- shape=907b2409 vocab=6aa4bdca
-/
theorem stokes_piecewiseSmoothRegion
    {ι ε : Type*} (patches : Finset ι) (edges : Finset ε)
    (parameterDomain : ι → Set (ℝ × ℝ)) (pulledBackDensity : ι → ℝ × ℝ → ℝ)
    (localIncidence : ι → ε → ℤ) (externalIncidence : ε → ℤ)
    (edgeIntegral : ε → ℝ)
    (hregion : PiecewiseSmoothRegion patches edges parameterDomain pulledBackDensity
      localIncidence externalIncidence)
    (hlocal : ∀ i ∈ patches,
      orientedBoundaryValue edges (localIncidence i) edgeIntegral =
        ∫ p in parameterDomain i, pulledBackDensity i p ∂(volume.prod volume)) :
    orientedBoundaryValue edges externalIncidence edgeIntegral =
      finiteAtlasSurfaceIntegral patches parameterDomain pulledBackDensity :=
  stokes_finite_atlas_of_edge_incidence patches edges parameterDomain pulledBackDensity
    localIncidence externalIncidence edgeIntegral hlocal hregion.gluing

/-- **闭分段光滑区域上的 Stokes 推论。**

若整体外边界的每条边关联数都为零，则所有参数片上拉回外微分密度的积分之和为零。
这是“闭曲面（无边界区域）上外微分积分消失”的装配版本。
@isnad1 id=eq.3h9v.s7.f4c4973adcca from=translated src=- shape=0bfbaedb vocab=6aa4bdca
-/
theorem stokes_closed_piecewiseSmoothRegion
    {ι ε : Type*} (patches : Finset ι) (edges : Finset ε)
    (parameterDomain : ι → Set (ℝ × ℝ)) (pulledBackDensity : ι → ℝ × ℝ → ℝ)
    (localIncidence : ι → ε → ℤ) (externalIncidence : ε → ℤ)
    (edgeIntegral : ε → ℝ)
    (hregion : PiecewiseSmoothRegion patches edges parameterDomain pulledBackDensity
      localIncidence externalIncidence)
    (hlocal : ∀ i ∈ patches,
      orientedBoundaryValue edges (localIncidence i) edgeIntegral =
        ∫ p in parameterDomain i, pulledBackDensity i p ∂(volume.prod volume))
    (hclosed : ∀ e ∈ edges, externalIncidence e = 0) :
    finiteAtlasSurfaceIntegral patches parameterDomain pulledBackDensity = 0 :=
  stokes_closed_finite_atlas patches edges parameterDomain pulledBackDensity
    localIncidence externalIncidence edgeIntegral hlocal hregion.gluing hclosed

/-- **二维分段光滑区域的 Green 装配定理。**

把分段光滑区域直接读作平面有限分片：每片参数域就是平面区域单元 `cell`，各片共用一个
旋度密度 `curlDensity`（由 `hdensity` 保证逐片密度与之一致）。在每片上用局部 Green 公式
（由 `hlocal` 提供），公共边关联数相消后得到整体并区域的旋度积分。
@isnad1 id=eq.3h10v.s8.4f1a909696b0 from=translated src=- shape=ce59f4c0 vocab=d1713b04
-/
theorem green_piecewiseSmoothRegion
    {ι ε : Type*} (pieces : Finset ι) (edges : Finset ε)
    (cell : ι → Set (ℝ × ℝ)) (pulledBackDensity : ι → ℝ × ℝ → ℝ)
    (curlDensity : ℝ × ℝ → ℝ)
    (localIncidence : ι → ε → ℤ) (externalIncidence : ε → ℤ)
    (edgeIntegral : ε → ℝ)
    (hregion : PiecewiseSmoothRegion pieces edges cell pulledBackDensity
      localIncidence externalIncidence)
    (hdensity : ∀ i, pulledBackDensity i = curlDensity)
    (hlocal : ∀ i ∈ pieces,
      orientedBoundaryValue edges (localIncidence i) edgeIntegral =
        ∫ z in cell i, curlDensity z ∂(volume.prod volume)) :
    orientedBoundaryValue edges externalIncidence edgeIntegral =
      ∫ z in ⋃ i ∈ pieces, cell i, curlDensity z ∂(volume.prod volume) :=
  green_finite_decomposition_of_edge_incidence pieces edges cell curlDensity
    localIncidence externalIncidence edgeIntegral
    (hregion.toGreenFiniteDecomposition curlDensity hdensity) hlocal hregion.gluing

/-- **三维分段光滑体元区域的 Gauss 装配定理。**

每个体元带自己的散度密度；局部外向通量由 `hlocal` 给出为体元上的散度积分，公共面上
两个相反的外法向关联数相消，剩下整体外边界通量。三维情形无法复用二维的
`PiecewiseSmoothRegion`，故这里直接接收 `GaussFiniteDecomposition`。
@isnad1 id=eq.3h9v.s8.73b9997bb485 from=translated src=- shape=a30e27c6 vocab=a603a710
-/
theorem gauss_piecewiseSmoothRegion
    {ι φ : Type*} (pieces : Finset ι) (faces : Finset φ)
    (cell : ι → Set (Fin 3 → ℝ)) (divDensity : (Fin 3 → ℝ) → ℝ)
    (localIncidence : ι → φ → ℤ) (externalIncidence : φ → ℤ)
    (faceFlux : φ → ℝ)
    (hdecomp : GaussFiniteDecomposition pieces cell divDensity)
    (hlocal : ∀ i ∈ pieces,
      orientedBoundaryValue faces (localIncidence i) faceFlux =
        ∫ x in cell i, divDensity x)
    (hincidence : ∀ f ∈ faces, externalIncidence f = ∑ i ∈ pieces, localIncidence i f) :
    orientedBoundaryValue faces externalIncidence faceFlux =
      ∫ x in ⋃ i ∈ pieces, cell i, divDensity x :=
  gauss_finite_decomposition_of_face_incidence pieces faces cell divDensity
    localIncidence externalIncidence faceFlux hdecomp hlocal hincidence

/-! ## 两片共享边的显式抵消 -/

/-- 两片共享一条边且局部关联数相反时，整体外边界在该共享边上的关联数为零。
@isnad1 id=eq.3h5v.s7.d5229acaf7ae from=translated src=- shape=e1622e5e vocab=44b54098
-/
theorem twoPatch_sharedEdge_externalIncidence_zero
    {ε : Type*} (edges : Finset ε) (localIncidence : Fin 2 → ε → ℤ)
    (externalIncidence : ε → ℤ) (shared : ε)
    (hshared_mem : shared ∈ edges)
    (hshared : localIncidence 0 shared + localIncidence 1 shared = 0)
    (hincidence : ∀ e ∈ edges, externalIncidence e = ∑ i : Fin 2, localIncidence i e) :
    externalIncidence shared = 0 := by
  rw [hincidence shared hshared_mem, Fin.sum_univ_two, hshared]

/-- 共享边的局部关联数相反时，从整体外边界值中删去这条边不改变结果。

这是“公共边贡献相消”的显式版本：外部关联数在共享边上的值为零，所以该边在
`orientedBoundaryValue` 中的单项贡献为零，可以整条删去。
@isnad1 id=and.3h6v.s7.02f883964abc from=translated src=- shape=450fbf80 vocab=749cf7a2
-/
theorem twoPatch_sharedEdge_cancellation
    {ε : Type*} [DecidableEq ε] (edges : Finset ε) (localIncidence : Fin 2 → ε → ℤ)
    (externalIncidence : ε → ℤ) (edgeIntegral : ε → ℝ) (shared : ε)
    (hshared_mem : shared ∈ edges)
    (hshared : localIncidence 0 shared + localIncidence 1 shared = 0)
    (hincidence : ∀ e ∈ edges, externalIncidence e = localIncidence 0 e + localIncidence 1 e) :
    externalIncidence shared = 0 ∧
      orientedBoundaryValue edges externalIncidence edgeIntegral =
        orientedBoundaryValue (edges.erase shared) externalIncidence edgeIntegral := by
  have hzero : externalIncidence shared = 0 := by
    rw [hincidence shared hshared_mem, hshared]
  refine ⟨hzero, ?_⟩
  have hsum : Finset.sum (edges.erase shared)
        (fun e => externalIncidence e • edgeIntegral e) =
      Finset.sum edges (fun e => externalIncidence e • edgeIntegral e) := by
    apply Finset.sum_subset (Finset.erase_subset _ _)
    intro e he henot
    have heq : e = shared := by
      by_contra h
      exact henot (Finset.mem_erase.mpr ⟨h, he⟩)
    rw [heq, hzero, zero_smul]
  calc
    orientedBoundaryValue edges externalIncidence edgeIntegral =
        Finset.sum (edges.erase shared)
          (fun e => externalIncidence e • edgeIntegral e) := hsum.symm
    _ = orientedBoundaryValue (edges.erase shared) externalIncidence edgeIntegral := rfl

/-- **两片共享边的 Stokes 装配。**

两个参数片索引为 `Fin 2`。若它们在共享边 `shared` 上取相反的局部关联数，且整体外边界
关联数等于两片局部关联数之和，则整体外边界值等于两片参数域上拉回密度积分之和；
等价地，共享边的贡献在两片之间抵消。

证明先由 `gluing` 把整体关联数换成两片之和，再用 `orientedBoundaryValue_sum` 把
关联数之和的边界值拆成两片边界值之和，最后代入每片的局部积分公式。
@isnad1 id=and.4h8v.s8.4bf361a13d66 from=translated src=- shape=bf177c85 vocab=534736c7
-/
theorem stokes_twoPatch_sharedEdge
    {ε : Type*} (edges : Finset ε)
    (parameterDomain : Fin 2 → Set (ℝ × ℝ))
    (pulledBackDensity : Fin 2 → ℝ × ℝ → ℝ)
    (localIncidence : Fin 2 → ε → ℤ) (externalIncidence : ε → ℤ)
    (edgeIntegral : ε → ℝ) (shared : ε)
    (hshared_mem : shared ∈ edges)
    (hshared : localIncidence 0 shared + localIncidence 1 shared = 0)
    (hregion : PiecewiseSmoothRegion Finset.univ edges parameterDomain
      pulledBackDensity localIncidence externalIncidence)
    (hlocal : ∀ i : Fin 2,
      orientedBoundaryValue edges (localIncidence i) edgeIntegral =
        ∫ p in parameterDomain i, pulledBackDensity i p ∂(volume.prod volume)) :
    (orientedBoundaryValue edges externalIncidence edgeIntegral =
      (∫ p in parameterDomain 0, pulledBackDensity 0 p ∂(volume.prod volume)) +
        ∫ p in parameterDomain 1, pulledBackDensity 1 p ∂(volume.prod volume)) ∧
      externalIncidence shared = 0 := by
  have hgluing : ∀ e ∈ edges,
      externalIncidence e = localIncidence 0 e + localIncidence 1 e := by
    intro e he
    rw [hregion.gluing e he, Fin.sum_univ_two]
  refine ⟨?_, ?_⟩
  · have hfun : (fun e => localIncidence 0 e + localIncidence 1 e) =
        (fun e => ∑ i ∈ (Finset.univ : Finset (Fin 2)), localIncidence i e) := by
      funext e
      rw [Fin.sum_univ_two]
    calc
      orientedBoundaryValue edges externalIncidence edgeIntegral =
          orientedBoundaryValue edges
            (fun e => localIncidence 0 e + localIncidence 1 e) edgeIntegral := by
        apply Finset.sum_congr rfl
        intro e he
        rw [hgluing e he]
      _ = ∑ i : Fin 2, orientedBoundaryValue edges (localIncidence i) edgeIntegral := by
        rw [hfun, orientedBoundaryValue_sum]
      _ = ∑ i : Fin 2,
          ∫ p in parameterDomain i, pulledBackDensity i p ∂(volume.prod volume) :=
        Finset.sum_congr rfl (fun i _ => hlocal i)
      _ = (∫ p in parameterDomain 0, pulledBackDensity 0 p ∂(volume.prod volume)) +
          ∫ p in parameterDomain 1, pulledBackDensity 1 p ∂(volume.prod volume) := by
        rw [Fin.sum_univ_two]
  · rw [hgluing shared hshared_mem, hshared]

/-! ## 一个具体的两矩形参数片实例 -/

/-- 两个矩形参数片的显式参数域：以竖直线 `x=0` 为公共边，左片取 `x<0`，右片取 `x≥0`。-/
private def twoPatchParameterDomain (i : Fin 2) : Set (ℝ × ℝ) :=
  if i = 0 then Set.Iio (0 : ℝ) ×ˢ Set.univ else Set.Ici (0 : ℝ) ×ˢ Set.univ

/-- 两个矩形参数片的局部边关联数：公共边在两片中方向相反。-/
private def twoPatchLocalIncidence (i : Fin 2) (_ : Fin 1) : ℤ :=
  if i = 0 then 1 else -1

/-- 显式证明两个矩形参数片构成一个分段光滑区域。
@isnad1 id=piecewis.0h0v.s6.d4c51d5fd6d7 from=translated src=- shape=735a71d2 vocab=88bb6307
-/
theorem twoPatchRegion_example :
    PiecewiseSmoothRegion (Finset.univ : Finset (Fin 2)) (Finset.univ : Finset (Fin 1))
      twoPatchParameterDomain (fun _ _ => 0) twoPatchLocalIncidence (fun _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i _
    by_cases hi : i = 0
    · rw [twoPatchParameterDomain, ite_eq_left hi]
      exact measurableSet_Iio.prod MeasurableSet.univ
    · rw [twoPatchParameterDomain, ite_eq_right hi]
      exact measurableSet_Ici.prod MeasurableSet.univ
  · intro a _ b _ hab
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · change Disjoint (twoPatchParameterDomain 0) (twoPatchParameterDomain 1)
      rw [show twoPatchParameterDomain 0 = Set.Iio (0 : ℝ) ×ˢ Set.univ by
            simp [twoPatchParameterDomain],
          show twoPatchParameterDomain 1 = Set.Ici (0 : ℝ) ×ˢ Set.univ by
            simp [twoPatchParameterDomain]]
      rw [Set.disjoint_left]
      intro p hp hp'
      simp only [Set.mem_prod, Set.mem_Iio, Set.mem_Ici, Set.mem_univ, and_true] at hp hp'
      linarith
    · change Disjoint (twoPatchParameterDomain 1) (twoPatchParameterDomain 0)
      rw [show twoPatchParameterDomain 1 = Set.Ici (0 : ℝ) ×ˢ Set.univ by
            simp [twoPatchParameterDomain],
          show twoPatchParameterDomain 0 = Set.Iio (0 : ℝ) ×ˢ Set.univ by
            simp [twoPatchParameterDomain]]
      rw [Set.disjoint_left]
      intro p hp hp'
      simp only [Set.mem_prod, Set.mem_Iio, Set.mem_Ici, Set.mem_univ, and_true] at hp hp'
      linarith
    · exact absurd rfl hab
  · intro i _
    exact integrableOn_zero
  · intro e _
    simp [twoPatchLocalIncidence, Fin.sum_univ_two]

/-- 显式实例上的 Stokes 装配：外边界值等于两个参数片上拉回密度（恒为零）积分之和。
@isnad1 id=eq.0h0v.s6.408ada9159ab from=translated src=- shape=3abd50f3 vocab=cd7ef119
-/
theorem twoPatchRegion_stokes_example :
    orientedBoundaryValue (Finset.univ : Finset (Fin 1)) (fun _ => 0) (fun _ => 0) =
      finiteAtlasSurfaceIntegral (Finset.univ : Finset (Fin 2))
        twoPatchParameterDomain (fun _ _ => 0) :=
  stokes_piecewiseSmoothRegion _ _ _ _ _ _ _ twoPatchRegion_example (by
    intro i _
    simp [orientedBoundaryValue])

end SandronesLibrary.Analysis.StokesDomainGluing

/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.ChangeOfVariables
import Tengoku.Seed.Analysis.SpecialFunctions.PolarCoord
import Tengoku.Seed.MeasureTheory.Constructions.Pi
import Tengoku.Seed.MeasureTheory.Integral.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 坐标积分：二维极坐标

本模块开始建立多重积分的坐标计算层。第一批定义二维极坐标映射，计算其 Jacobian，
并把全平面 Lebesgue 积分改写成带权累次积分。角度采用 `(-π,π)`，半径采用 `(0,∞)`；
缺少的负实轴和原点是零测集，故不改变积分值。
-/

noncomputable section

namespace SandronesLibrary.Analysis.Multivariable

open Set MeasureTheory Real

/-- 教材中的二维极坐标映射 `(r,θ) ↦ (r cos θ,r sin θ)`。

> **Entry**: analysis.multivariable.coordinate-integrals-/
def polarMap (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 * cos p.2, p.1 * sin p.2)

/-- 本库极坐标映射就是 Mathlib 极坐标局部同胚的逆向映射。
@isnad1 id=eq.0h0v.s6.b516cb66c634 from=translated src=- shape=ad82fb7f vocab=d5dca6d2
-/
theorem polarMap_eq_polarCoord_symm : polarMap = polarCoord.symm := by
  rfl

/-- **极坐标 Jacobian**：极坐标映射的导数行列式为半径 `r`。因此在 `r>0`
的标准坐标区域上，换元权重的绝对值就是 `r`。
@isnad1 id=eq.0h1v.s7.040ab985e7af from=translated src=- shape=a899a184 vocab=f082148f
-/
theorem det_fderiv_polarMap (p : ℝ × ℝ) :
    (fderiv ℝ polarMap p).det = p.1 := by
  rw [polarMap_eq_polarCoord_symm,
    (hasFDerivAt_polarCoord_symm p).fderiv]
  exact det_fderivPolarCoordSymm p

/-- **全平面极坐标公式**：

`∫_{ℝ²} f(x,y) dxdy = ∫_{r>0,-π<θ<π} r f(r cos θ,r sin θ) drdθ`。

负实轴和原点构成零测集，因此标准极坐标目标区域已经覆盖全平面积分。
@isnad1 id=eq.0h1v.s7.ad6beaf7937d from=translated src=- shape=9bc84633 vocab=fde5e838
-/
theorem integral_plane_eq_polar (f : ℝ × ℝ → ℝ) :
    (∫ z, f z) =
      ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, p.1 * f (polarMap p) := by
  simpa [polarMap, smul_eq_mul, polarCoord_target] using
    (integral_comp_polarCoord_symm f).symm

/-- 若极坐标拉回后的函数可积，则全平面积分可进一步写成先对角度、再对半径的
累次积分。显式的可积性假设保证 Fubini 换序合法。
@isnad1 id=eq.1h1v.s7.1d83ff383ba0 from=translated src=- shape=1549df6f vocab=e7603b32
-/
theorem integral_plane_eq_iterated_polar (f : ℝ × ℝ → ℝ)
    (hf : IntegrableOn (fun p ↦ p.1 * f (polarMap p))
      (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) (volume.prod volume)) :
    (∫ z, f z) =
      ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-π) π,
        r * f (r * cos θ, r * sin θ) := by
  rw [integral_plane_eq_polar]
  change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
      p.1 * f (polarMap p) ∂(volume.prod volume)) = _
  simpa [polarMap] using MeasureTheory.setIntegral_prod
    (fun p : ℝ × ℝ ↦ p.1 * f (polarMap p)) hf

/-! ## 三维柱坐标 -/

/-- 柱坐标映射 `((r,θ),z) ↦ ((r cos θ,r sin θ),z)`。三维空间在本模块中写成
`(ℝ × ℝ) × ℝ`，前两个分量构成水平平面。-/
def cylindricalMap (p : (ℝ × ℝ) × ℝ) : (ℝ × ℝ) × ℝ :=
  (polarMap p.1, p.2)

/-- **全空间柱坐标公式**：若原函数及其柱坐标拉回可积，则

`∫_{ℝ³} f = ∫₀^∞ ∫_{-π}^π ∫_{-∞}^∞ r f(r cosθ,r sinθ,z) dz dθ dr`。

证明把柱坐标视为“二维极坐标 × 恒等坐标”：先用 Fubini 分离竖直坐标，再应用
二维极坐标公式，最后再次使用 Fubini 展开成三重累次积分。
@isnad1 id=eq.2h1v.s8.401c395fc2c2 from=translated src=- shape=7ce0db35 vocab=39ec6586
-/
theorem integral_space_eq_iterated_cylindrical (f : (ℝ × ℝ) × ℝ → ℝ)
    (hf : Integrable f ((volume.prod volume).prod volume))
    (hcyl : IntegrableOn (fun p ↦ p.1.1 * f (cylindricalMap p))
      ((Ioi (0 : ℝ) ×ˢ Ioo (-π) π) ×ˢ (univ : Set ℝ))
      ((volume.prod volume).prod volume)) :
    (∫ q, f q ∂((volume.prod volume).prod volume)) =
      ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-π) π, ∫ z : ℝ,
        r * f ((r * cos θ, r * sin θ), z) := by
  have hfull :
      (∫ q, f q ∂((volume.prod volume).prod volume)) =
        ∫ p : ℝ × ℝ, ∫ z : ℝ, f (p, z) :=
    integral_prod f hf
  rw [hfull, integral_plane_eq_polar]
  have htarget : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  have hcylIndicator : Integrable
      (((Ioi (0 : ℝ) ×ˢ Ioo (-π) π) ×ˢ (univ : Set ℝ)).indicator
        (fun p ↦ p.1.1 * f (cylindricalMap p)))
      ((volume.prod volume).prod volume) :=
    hcyl.integrable_indicator (htarget.prod MeasurableSet.univ)
  have houter : IntegrableOn
      (fun p : ℝ × ℝ ↦ ∫ z : ℝ, p.1 * f (cylindricalMap (p, z)))
      (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) (volume.prod volume) := by
    rw [← integrable_indicator_iff htarget]
    refine hcylIndicator.integral_prod_left.congr (Filter.Eventually.of_forall fun p ↦ ?_)
    by_cases hp : p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π <;> simp [hp]
  calc
    (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
        p.1 * ∫ z : ℝ, f (polarMap p, z)) =
      ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
        ∫ z : ℝ, p.1 * f (cylindricalMap (p, z)) := by
          apply setIntegral_congr_fun htarget
          intro p _
          dsimp
          rw [integral_const_mul]
          rfl
    _ = ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-π) π, ∫ z : ℝ,
        r * f ((r * cos θ, r * sin θ), z) := by
      change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
        (∫ z : ℝ, p.1 * f (cylindricalMap (p, z))) ∂(volume.prod volume)) = _
      simpa [cylindricalMap, polarMap] using
        MeasureTheory.setIntegral_prod
          (fun p : ℝ × ℝ ↦ ∫ z : ℝ, p.1 * f (cylindricalMap (p, z))) houter

/-! ## 三维球坐标 -/

/-- 三维欧氏坐标的函数空间表示。-/
abbrev Euclidean3 := Fin 3 → ℝ

/-- 球坐标映射，输入坐标依次为 `(ρ, θ, φ)`：径向距离、方位角和极角。

`(ρ,θ,φ) ↦ (ρ sinφ cosθ, ρ sinφ sinθ, ρ cosφ)`。-/
def sphericalMap (p : Euclidean3) : Euclidean3 :=
  ![p 0 * sin (p 2) * cos (p 1),
    p 0 * sin (p 2) * sin (p 1),
    p 0 * cos (p 2)]

attribute [local instance 10000] NormedAlgebra.toNormedSpace

/-- 球坐标映射的教材 Jacobian 矩阵。列依次对应 `ρ,θ,φ`，行依次对应
直角坐标 `x,y,z`。-/
def sphericalDerivativeMatrix (p : Euclidean3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![sin (p 2) * cos (p 1), -(p 0 * sin (p 2) * sin (p 1)),
      p 0 * cos (p 2) * cos (p 1);
    sin (p 2) * sin (p 1), p 0 * sin (p 2) * cos (p 1),
      p 0 * cos (p 2) * sin (p 1);
    cos (p 2), 0, -(p 0 * sin (p 2))]

/-- 球坐标 Jacobian 矩阵所表示的连续线性映射。-/
def sphericalDerivative (p : Euclidean3) : Euclidean3 →L[ℝ] Euclidean3 :=
  (Matrix.toLin' (sphericalDerivativeMatrix p)).toContinuousLinearMap

/-- 球坐标映射的 Fréchet 导数就是显式 Jacobian 矩阵对应的线性映射。

证明逐坐标调用一维的 `sin`、`cos` 导数，再用乘积法则组装三个坐标函数；
最后将三个标量导数拼成向量值导数，并核对它与教材矩阵逐项一致。
@isnad1 id=hasfderi.0h1v.s7.18232e120b6c from=translated src=- shape=fb308d54 vocab=66049993
-/
theorem hasFDerivAt_sphericalMap (p : Euclidean3) :
    HasFDerivAt sphericalMap (sphericalDerivative p) p := by
  have hρ : HasFDerivAt (fun q : Euclidean3 ↦ q 0)
      (ContinuousLinearMap.proj (R := ℝ) 0) p := by fun_prop
  have hθ : HasFDerivAt (fun q : Euclidean3 ↦ q 1)
      (ContinuousLinearMap.proj (R := ℝ) 1) p := by fun_prop
  have hφ : HasFDerivAt (fun q : Euclidean3 ↦ q 2)
      (ContinuousLinearMap.proj (R := ℝ) 2) p := by fun_prop
  have hsθ := (Real.hasDerivAt_sin (p 1)).hasFDerivAt.comp p hθ
  have hcθ := (Real.hasDerivAt_cos (p 1)).hasFDerivAt.comp p hθ
  have hsφ := (Real.hasDerivAt_sin (p 2)).hasFDerivAt.comp p hφ
  have hcφ := (Real.hasDerivAt_cos (p 2)).hasFDerivAt.comp p hφ
  let e0 : Euclidean3 →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let e1 : Euclidean3 →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  let e2 : Euclidean3 →L[ℝ] ℝ := ContinuousLinearMap.proj 2
  let d0 := (p 0 * sin (p 2)) •
      (ContinuousLinearMap.toSpanSingleton ℝ (-sin (p 1)) ∘SL e1) +
    cos (p 1) • (p 0 •
      (ContinuousLinearMap.toSpanSingleton ℝ (cos (p 2)) ∘SL e2) +
      sin (p 2) • e0)
  let d1 := (p 0 * sin (p 2)) •
      (ContinuousLinearMap.toSpanSingleton ℝ (cos (p 1)) ∘SL e1) +
    sin (p 1) • (p 0 •
      (ContinuousLinearMap.toSpanSingleton ℝ (cos (p 2)) ∘SL e2) +
      sin (p 2) • e0)
  let d2 := p 0 •
      (ContinuousLinearMap.toSpanSingleton ℝ (-sin (p 2)) ∘SL e2) +
    cos (p 2) • e0
  have h0 := (hρ.mul hsφ).mul hcθ
  have h1 := (hρ.mul hsφ).mul hsθ
  have h2 := hρ.mul hcφ
  let D : Fin 3 → (Euclidean3 →L[ℝ] ℝ) := ![d0, d1, d2]
  have hD : HasFDerivAt sphericalMap (ContinuousLinearMap.pi D) p := by
    rw [hasFDerivAt_pi]
    intro i
    fin_cases i
    · change HasFDerivAt
        (((fun q : Euclidean3 ↦ q 0) * (fun q ↦ sin (q 2))) *
          (fun q ↦ cos (q 1))) _ p
      simpa [D, d0, e0, e1, e2, Function.comp_def] using h0
    · change HasFDerivAt
        (((fun q : Euclidean3 ↦ q 0) * (fun q ↦ sin (q 2))) *
          (fun q ↦ sin (q 1))) _ p
      simpa [D, d1, e0, e1, e2, Function.comp_def] using h1
    · change HasFDerivAt
        ((fun q : Euclidean3 ↦ q 0) * (fun q ↦ cos (q 2))) _ p
      simpa [D, d2, e0, e1, e2, Function.comp_def] using h2
  have heq : sphericalDerivative p = ContinuousLinearMap.pi D := by
    apply ContinuousLinearMap.ext
    intro v
    funext i
    fin_cases i <;>
      simp [sphericalDerivative, sphericalDerivativeMatrix, Matrix.toLin'_apply,
        Matrix.vecHead, Matrix.vecTail, D, d0, d1, d2, e0, e1, e2] <;> ring
  rw [heq]
  exact hD

/-- 球坐标 Jacobian 矩阵的行列式。负号来自本库采用的坐标顺序
`(ρ,θ,φ)`；教材常用的 `(ρ,φ,θ)` 交换了后两列。
@isnad1 id=eq.0h1v.s6.d87be6224511 from=translated src=- shape=9a299e13 vocab=51108d41
-/
theorem det_sphericalDerivativeMatrix (p : Euclidean3) :
    (sphericalDerivativeMatrix p).det = -((p 0) ^ 2 * sin (p 2)) := by
  rw [Matrix.det_fin_three]
  simp [sphericalDerivativeMatrix]
  have hθ := sin_sq_add_cos_sq (p 1)
  have hφ := sin_sq_add_cos_sq (p 2)
  calc
    _ = -((p 0) ^ 2 * sin (p 2) *
        ((sin (p 1)) ^ 2 + (cos (p 1)) ^ 2) *
        ((sin (p 2)) ^ 2 + (cos (p 2)) ^ 2)) := by ring
    _ = _ := by rw [hθ, hφ]; ring

/-- 球坐标映射的导数行列式为 `-ρ² sin φ`。因此在标准区域
`ρ > 0, 0 < φ < π` 上，换元公式中的绝对 Jacobian 是 `ρ² sin φ`。
@isnad1 id=eq.0h1v.s8.feedc2bde2f1 from=translated src=- shape=aac1a437 vocab=490e2e2f
-/
theorem det_fderiv_sphericalMap (p : Euclidean3) :
    (fderiv ℝ sphericalMap p).det = -((p 0) ^ 2 * sin (p 2)) := by
  rw [(hasFDerivAt_sphericalMap p).fderiv]
  simpa [sphericalDerivative, ContinuousLinearMap.det,
    LinearMap.det_toMatrix'] using det_sphericalDerivativeMatrix p

/-- 球坐标映射在全空间上 Fréchet 可微。
@isnad1 id=differen.0h0v.s7.cb1dca549d82 from=translated src=- shape=07be6169 vocab=0d172409
-/
theorem differentiable_sphericalMap : Differentiable ℝ sphericalMap := by
  rw [differentiable_pi]
  intro i
  fin_cases i <;> simp [sphericalMap] <;> fun_prop

/-- 球坐标映射的第一坐标。
@isnad1 id=eq.0h1v.s6.f60859134471 from=translated src=- shape=289d08c2 vocab=f8ac05b9
-/
theorem sphericalMap_apply_zero (p : Euclidean3) :
    sphericalMap p 0 = p 0 * sin (p 2) * cos (p 1) := by rfl

/-- 球坐标映射的第二坐标。
@isnad1 id=eq.0h1v.s6.3bfe7c84f754 from=translated src=- shape=289d08c2 vocab=c131bffe
-/
theorem sphericalMap_apply_one (p : Euclidean3) :
    sphericalMap p 1 = p 0 * sin (p 2) * sin (p 1) := by rfl

/-- 球坐标映射的第三坐标。
@isnad1 id=eq.0h1v.s6.09a23907c5a7 from=translated src=- shape=62e6ae7d vocab=5591df97
-/
theorem sphericalMap_apply_two (p : Euclidean3) :
    sphericalMap p 2 = p 0 * cos (p 2) := by rfl

/-! ### 标准球坐标参数域上的换元 -/

/-- 标准球坐标参数域：`ρ > 0`、`-π < θ < π`、`0 < φ < π`。
开区间排除了坐标退化点，并为每个像点选择唯一的角度代表。-/
def sphericalSource : Set Euclidean3 :=
  {p | p 0 ∈ Ioi (0 : ℝ) ∧ p 1 ∈ Ioo (-π) π ∧ p 2 ∈ Ioo (0 : ℝ) π}

/--
@isnad1 id=measurab.0h0v.s4.ae61c14e2a31 from=translated src=- shape=25b03439 vocab=e1341704
-/
theorem measurableSet_sphericalSource : MeasurableSet sphericalSource := by
  unfold sphericalSource
  measurability

/--
@isnad1 id=isopen.0h0v.s4.cda391029754 from=translated src=- shape=25b03439 vocab=d61aadc4
-/
theorem isOpen_sphericalSource : IsOpen sphericalSource := by
  rw [show sphericalSource =
      (fun p : Euclidean3 ↦ p 0) ⁻¹' Ioi 0 ∩
        ((fun p : Euclidean3 ↦ p 1) ⁻¹' Ioo (-π) π ∩
          (fun p : Euclidean3 ↦ p 2) ⁻¹' Ioo 0 π) by
    ext p
    simp [sphericalSource]]
  exact (isOpen_Ioi.preimage (by fun_prop)).inter
    ((isOpen_Ioo.preimage (by fun_prop)).inter
      (isOpen_Ioo.preimage (by fun_prop)))

/--
@isnad1 id=differen.0h0v.s7.f9c33a5843a1 from=translated src=- shape=996807f9 vocab=21a2c3da
-/
theorem differentiableOn_sphericalMap :
    DifferentiableOn ℝ sphericalMap sphericalSource :=
  differentiable_sphericalMap.differentiableOn

/-- 球坐标映射在标准参数域上单射。证明依次从像点恢复半径、极角和方位角：
三坐标平方和给出正半径，第三坐标给出 `cos φ`，前两坐标给出 `cos θ` 与
`sin θ`。开区间条件消除了三角函数的周期歧义。
@isnad1 id=injon.0h0v.s2.3faf208fef3f from=translated src=- shape=4ce37f0a vocab=e091d029
-/
theorem injOn_sphericalMap : InjOn sphericalMap sphericalSource := by
  intro p hp q hq hpq
  have h0 := congrFun hpq (0 : Fin 3)
  have h1 := congrFun hpq (1 : Fin 3)
  have h2 := congrFun hpq (2 : Fin 3)
  simp only [sphericalMap_apply_zero] at h0
  simp only [sphericalMap_apply_one] at h1
  simp only [sphericalMap_apply_two] at h2
  have pnorm :
      (sphericalMap p 0) ^ 2 + (sphericalMap p 1) ^ 2 +
        (sphericalMap p 2) ^ 2 = (p 0) ^ 2 := by
    rw [sphericalMap_apply_zero, sphericalMap_apply_one,
      sphericalMap_apply_two]
    calc
      _ = (p 0) ^ 2 * ((sin (p 2)) ^ 2 *
          ((cos (p 1)) ^ 2 + (sin (p 1)) ^ 2) + (cos (p 2)) ^ 2) := by ring
      _ = _ := by
        rw [add_comm ((cos (p 1)) ^ 2), sin_sq_add_cos_sq, mul_one,
          sin_sq_add_cos_sq]
        ring
  have qnorm :
      (sphericalMap q 0) ^ 2 + (sphericalMap q 1) ^ 2 +
        (sphericalMap q 2) ^ 2 = (q 0) ^ 2 := by
    rw [sphericalMap_apply_zero, sphericalMap_apply_one,
      sphericalMap_apply_two]
    calc
      _ = (q 0) ^ 2 * ((sin (q 2)) ^ 2 *
          ((cos (q 1)) ^ 2 + (sin (q 1)) ^ 2) + (cos (q 2)) ^ 2) := by ring
      _ = _ := by
        rw [add_comm ((cos (q 1)) ^ 2), sin_sq_add_cos_sq, mul_one,
          sin_sq_add_cos_sq]
        ring
  have hrho_sq : (p 0) ^ 2 = (q 0) ^ 2 := by
    rw [← pnorm, ← qnorm, hpq]
  have hrho : p 0 = q 0 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hrho_sq with h | h
    · exact h
    · exfalso
      have hpos : 0 < p 0 + q 0 := add_pos hp.1 hq.1
      rw [h] at hpos
      linarith
  have hcos_phi : cos (p 2) = cos (q 2) := by
    rw [hrho] at h2
    exact mul_left_cancel₀ (ne_of_gt hq.1) h2
  have hphi : p 2 = q 2 := by
    apply Real.strictAntiOn_cos.injOn
    · exact ⟨le_of_lt hp.2.2.1, le_of_lt hp.2.2.2⟩
    · exact ⟨le_of_lt hq.2.2.1, le_of_lt hq.2.2.2⟩
    · exact hcos_phi
  rw [hrho, hphi] at h0 h1
  have hcoeff : q 0 * sin (q 2) ≠ 0 := mul_ne_zero
    (ne_of_gt hq.1) (ne_of_gt (sin_pos_of_pos_of_lt_pi hq.2.2.1 hq.2.2.2))
  have hcos_theta : cos (p 1) = cos (q 1) := mul_left_cancel₀ hcoeff h0
  have hsin_theta : sin (p 1) = sin (q 1) := mul_left_cancel₀ hcoeff h1
  have hangle : (p 1 : Real.Angle) = (q 1 : Real.Angle) :=
    Real.Angle.cos_sin_inj hcos_theta hsin_theta
  have htheta := congrArg Real.Angle.toReal hangle
  rw [Real.Angle.toReal_coe_eq_self_iff.2
      ⟨hp.2.1.1, le_of_lt hp.2.1.2⟩,
    Real.Angle.toReal_coe_eq_self_iff.2
      ⟨hq.2.1.1, le_of_lt hq.2.1.2⟩] at htheta
  funext i
  fin_cases i
  · exact hrho
  · exact htheta
  · exact hphi

/-- 在标准参数域内部，区域内导数等于全导数，且 Jacobian 的绝对值为
`ρ² sin φ`。
@isnad1 id=eq.1h1v.s6.7a1ff55f1dd3 from=translated src=- shape=1e66b94b vocab=b3fa8434
-/
theorem absJacobianWithin_sphericalMap (p : Euclidean3) (hp : p ∈ sphericalSource) :
    absJacobianWithin sphericalMap sphericalSource p = (p 0) ^ 2 * sin (p 2) := by
  unfold absJacobianWithin
  rw [fderivWithin_of_isOpen isOpen_sphericalSource hp,
    det_fderiv_sphericalMap, abs_neg, abs_of_nonneg]
  exact mul_nonneg (sq_nonneg _) (le_of_lt
    (sin_pos_of_pos_of_lt_pi hp.2.2.1 hp.2.2.2))

/-- **标准域球坐标换元公式**：球坐标像区域上的积分等于参数域上乘以
`rho² sin phi` 后的积分。全空间版本还需证明像的补集为零测集。
@isnad1 id=eq.0h1v.s8.b673a5eb3b3e from=translated src=- shape=dc0ce1e4 vocab=bcfea5dc
-/
theorem integral_spherical_image (f : Euclidean3 → ℝ) :
    (∫ x in sphericalMap '' sphericalSource, f x) =
      ∫ p in sphericalSource, (p 0) ^ 2 * sin (p 2) * f (sphericalMap p) := by
  rw [integral_image_eq_integral_absJacobian_mul
    measurableSet_sphericalSource differentiableOn_sphericalMap injOn_sphericalMap]
  apply setIntegral_congr_fun measurableSet_sphericalSource
  intro p hp
  dsimp only
  rw [absJacobianWithin_sphericalMap p hp]

/-- 横向第二坐标非零的每个空间点都由标准球坐标参数域覆盖。

证明避免重新发展反三角函数：先对 `(x,y)` 使用二维极坐标恢复 `(r,θ)`，再对
`(z,r)` 使用二维极坐标恢复 `(ρ,φ)`。由于 `y ≠ 0`，有 `r > 0`，从而第二次
得到的极角严格位于 `(0,π)`。
@isnad1 id=mem.1h1v.s5.0c01154bc3ad from=translated src=- shape=6bd27955 vocab=e217b5c7
-/
theorem mem_spherical_image_of_coord_one_ne_zero (x : Euclidean3) (hx : x 1 ≠ 0) :
    x ∈ sphericalMap '' sphericalSource := by
  let a : ℝ × ℝ := polarCoord (x 0, x 1)
  have hha : (x 0, x 1) ∈ polarCoord.source := Or.inr hx
  have ha : a ∈ polarCoord.target := polarCoord.map_source hha
  have hainv : polarCoord.symm a = (x 0, x 1) := polarCoord.left_inv hha
  let b : ℝ × ℝ := polarCoord (x 2, a.1)
  have hva : 0 < a.1 := ha.1
  have hvb : (x 2, a.1) ∈ polarCoord.source := Or.inr (ne_of_gt hva)
  have hb : b ∈ polarCoord.target := polarCoord.map_source hvb
  have hbinv : polarCoord.symm b = (x 2, a.1) := polarCoord.left_inv hvb
  have hsin : 0 < sin b.2 := by
    have hprod : 0 < b.1 * sin b.2 := by
      rw [show b.1 * sin b.2 = a.1 by exact congrArg Prod.snd hbinv]
      exact hva
    exact pos_of_mul_pos_right hprod (le_of_lt hb.1)
  have hphi0 : 0 < b.2 := by
    by_contra h
    have hnonpos : sin b.2 ≤ 0 :=
      sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_gt h) (le_of_lt hb.2.1)
    exact (not_lt_of_ge hnonpos) hsin
  refine ⟨![b.1, a.2, b.2], ?_, ?_⟩
  · exact ⟨hb.1, ha.2, hphi0, hb.2.2⟩
  · funext i
    fin_cases i
    · change b.1 * sin b.2 * cos a.2 = x 0
      rw [show b.1 * sin b.2 = a.1 by exact congrArg Prod.snd hbinv]
      exact congrArg Prod.fst hainv
    · change b.1 * sin b.2 * sin a.2 = x 1
      rw [show b.1 * sin b.2 = a.1 by exact congrArg Prod.snd hbinv]
      exact congrArg Prod.snd hainv
    · change b.1 * cos b.2 = x 2
      exact congrArg Prod.fst hbinv

/-- 标准球坐标像的补集包含在坐标超平面 `y = 0` 中。这个上界略大于实际的
角度割面，但足以证明补集为零测集。
@isnad1 id=le.0h0v.s5.197645cab6a9 from=translated src=- shape=d3d480e6 vocab=9ec8e175
-/
theorem spherical_image_compl_subset_hyperplane :
    (sphericalMap '' sphericalSource)ᶜ ⊆ {x : Euclidean3 | x 1 = 0} := by
  intro x hx
  by_contra h
  exact hx (mem_spherical_image_of_coord_one_ne_zero x h)

/-- 标准球坐标像几乎处处等于整个三维空间；遗漏的角度割面为零测集。
@isnad1 id=eventual.0h0v.s6.14f7473f7190 from=translated src=- shape=e05ec6a2 vocab=9371ccc0
-/
theorem spherical_image_ae_eq_univ :
    sphericalMap '' sphericalSource =ᵐ[volume] (univ : Set Euclidean3) := by
  rw [ae_eq_univ]
  apply measure_mono_null spherical_image_compl_subset_hyperplane
  rw [volume_pi]
  exact Measure.pi_hyperplane (fun _ : Fin 3 ↦ volume) (1 : Fin 3) 0

/-- **全空间球坐标公式**：标准球坐标像仅遗漏零测割面，故像区域换元公式可以
直接升级为整个 `ℝ³` 上的积分公式。
@isnad1 id=eq.0h1v.s8.a0d7eb173483 from=translated src=- shape=6213244c vocab=368fa7b2
-/
theorem integral_space_eq_spherical (f : Euclidean3 → ℝ) :
    (∫ x, f x) =
      ∫ p in sphericalSource, (p 0) ^ 2 * sin (p 2) * f (sphericalMap p) := by
  rw [← integral_spherical_image]
  rw [← setIntegral_univ]
  exact setIntegral_congr_set spherical_image_ae_eq_univ.symm

/-! ### 教材中的三重累次形式 -/

/-- 把嵌套三元组 `(ρ,(θ,φ))` 改写为函数坐标 `![ρ,θ,φ]` 的可测等价。-/
def sphericalParamsEquiv : ℝ × (ℝ × ℝ) ≃ᵐ Euclidean3 :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.finTwoArrow (α := ℝ)).symm).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).symm

/--
@isnad1 id=eq.0h1v.s7.888268acfed6 from=translated src=- shape=9dfe83ef vocab=89c009c9
-/
theorem sphericalParamsEquiv_apply (p : ℝ × (ℝ × ℝ)) :
    sphericalParamsEquiv p = ![p.1, p.2.1, p.2.2] := by
  funext i
  fin_cases i <;> rfl

/-- 坐标重排 `(ρ,(θ,φ)) ↔ ![ρ,θ,φ]` 保持三维 Lebesgue 体积。
@isnad1 id=measurep.0h0v.s7.c82dde5b9fe8 from=translated src=- shape=532e3077 vocab=4495f685
-/
theorem measurePreserving_sphericalParamsEquiv :
    MeasurePreserving sphericalParamsEquiv := by
  apply MeasurePreserving.trans
  · convert (MeasurePreserving.id (volume : Measure ℝ)).prod
      (volume_preserving_finTwoArrow ℝ).symm using 1
    · funext p
      rfl
    · exact Measure.volume_eq_prod ℝ (ℝ × ℝ)
  · exact (volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).symm

/--
@isnad1 id=eq.0h0v.s7.0d1f99cb1320 from=translated src=- shape=e54f8a0c vocab=9e9b4f7d
-/
theorem sphericalParamsEquiv_preimage_source :
    sphericalParamsEquiv ⁻¹' sphericalSource =
      Ioi (0 : ℝ) ×ˢ (Ioo (-π) π ×ˢ Ioo (0 : ℝ) π) := by
  ext p
  simp [sphericalSource, sphericalParamsEquiv_apply]

/--
@isnad1 id=eq.0h1v.s8.791d687626db from=translated src=- shape=34a4cccc vocab=a811cb0e
-/
theorem sphericalParamsEquiv_map (p : ℝ × (ℝ × ℝ)) :
    sphericalMap (sphericalParamsEquiv p) =
      ![p.1 * sin p.2.2 * cos p.2.1,
        p.1 * sin p.2.2 * sin p.2.1,
        p.1 * cos p.2.2] := by
  simp [sphericalMap, sphericalParamsEquiv_apply]

/-- **全空间球坐标的三重累次积分公式**：若带 Jacobian 权重的拉回函数在标准
参数域可积，则 Fubini 定理把全空间积分展开为先极角、再方位角、最后半径的积分。

截面可积性无需额外假设：它由整体可积性通过 Fubini 自动在几乎处处的半径上成立，
这已经足以在外层集合积分中替换内层二重积分。
@isnad1 id=eq.1h1v.s9.f7495e2264fa from=translated src=- shape=130e39b1 vocab=a285f11e
-/
theorem integral_space_eq_iterated_spherical (f : Euclidean3 → ℝ)
    (hf : IntegrableOn
      (fun p : ℝ × (ℝ × ℝ) ↦
        p.1 ^ 2 * sin p.2.2 * f (sphericalMap (sphericalParamsEquiv p)))
      (Ioi (0 : ℝ) ×ˢ (Ioo (-π) π ×ˢ Ioo (0 : ℝ) π))
      (volume.prod (volume.prod volume))) :
    (∫ x, f x) =
      ∫ ρ in Ioi (0 : ℝ), ∫ θ in Ioo (-π) π, ∫ φ in Ioo (0 : ℝ) π,
        ρ ^ 2 * sin φ * f ![ρ * sin φ * cos θ,
          ρ * sin φ * sin θ, ρ * cos φ] := by
  rw [integral_space_eq_spherical]
  have hchange :
      (∫ p in sphericalSource, p 0 ^ 2 * sin (p 2) * f (sphericalMap p)) =
        ∫ p in Ioi (0 : ℝ) ×ˢ (Ioo (-π) π ×ˢ Ioo (0 : ℝ) π),
          p.1 ^ 2 * sin p.2.2 * f (sphericalMap (sphericalParamsEquiv p))
          ∂(volume.prod (volume.prod volume)) := by
    rw [← measurePreserving_sphericalParamsEquiv.map_eq,
      setIntegral_map_equiv, sphericalParamsEquiv_preimage_source]
    rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), Measure.volume_eq_prod ℝ ℝ]
    simp [sphericalParamsEquiv_apply, sphericalMap]
  have hsec : ∀ᵐ ρ ∂volume.restrict (Ioi (0 : ℝ)), IntegrableOn
      (fun a : ℝ × ℝ ↦
        ρ ^ 2 * sin a.2 * f (sphericalMap (sphericalParamsEquiv (ρ, a))))
      (Ioo (-π) π ×ˢ Ioo (0 : ℝ) π) (volume.prod volume) := by
    have hf' := hf
    rw [IntegrableOn, ← Measure.prod_restrict] at hf'
    exact hf'.prod_right_ae
  rw [hchange, setIntegral_prod _ hf]
  apply integral_congr_ae
  filter_upwards [hsec] with ρ hρ
  rw [setIntegral_prod _ hρ]
  simp [sphericalParamsEquiv_apply, sphericalMap]

end SandronesLibrary.Analysis.Multivariable

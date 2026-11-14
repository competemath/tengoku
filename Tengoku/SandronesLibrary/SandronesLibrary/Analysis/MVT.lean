/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Filter Topology
open scoped Filter Topology

/-!
# Analysis / MVT —— 微分中值定理（第七章）

本文件当前条目（引理清单，§0 铁律4：一次一条，逐条编译）：

* **analysis.mvt.rolle**（罗尔定理）。
* **analysis.mvt.lagrange**（拉格朗日中值定理）。
* **analysis.mvt.lagrange-deriv**（带导函数版 Lagrange）。
* **analysis.mvt.monotone-deriv**（导数符号判别单调）。
* **analysis.mvt.cauchy**（柯西中值定理）。
* **analysis.mvt.lhopital**（L'Hôpital 法则，0/0 型）。
* **analysis.mvt.taylor**（泰勒公式，Lagrange 余项）。
-/

namespace SandronesLibrary

namespace Analysis.MVT

/-- 罗尔定理：闭区间连续、开区间可导、端点值相等的函数，在开区间内某点导数为 0。 
> **Entry**: analysis.mvt.rolle
@isnad1 id=ex.4h3v.s7.3a1d3a0720e0 from=translated src=- shape=0fd8bdf9 vocab=c7c017ce
-/
theorem rolle {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b))
    (_hfd : DifferentiableOn ℝ f (Set.Ioo a b)) (hfI : f a = f b) :
    ∃ c ∈ Set.Ioo a b, deriv f c = 0 :=
  exists_deriv_eq_zero hab hfc hfI

/-- 拉格朗日中值定理：闭区间连续、开区间可导，存在 c 使 f'(c) 等于割线斜率。 
> **Entry**: analysis.mvt.lagrange
@isnad1 id=ex.3h3v.s7.f807959a2903 from=translated src=- shape=7bd9f4cb vocab=f0ba514b
-/
theorem lagrange {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b))
    (hfd : DifferentiableOn ℝ f (Set.Ioo a b)) :
    ∃ c ∈ Set.Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hfc hfd

/-- 拉格朗日中值定理（带导函数 f' 版本）：若 f' 是 f 的导数，则存在 c 使 f'(c) 等于割线斜率。 
> **Entry**: analysis.mvt.lagrange-deriv
@isnad1 id=ex.3h4v.s7.33c6c4e6aa9e from=translated src=- shape=c5965fc3 vocab=b5dd52e1
-/
theorem lagrange_deriv {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b))
    (hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Set.Ioo a b, f' c = (f b - f a) / (b - a) :=
  exists_hasDerivAt_eq_slope f f' hab hfc hff'

/-- 导数非负 ⟹ 单调不减：导数符号判别单调性的一个方向。
  （MVT 推论：f' ≥ 0 在区间内 ⟹ f 在该区间单调不减。） 
> **Entry**: analysis.mvt.monotone-deriv
@isnad1 id=monotone.4h3v.s7.7d9e8d1ccf1f from=translated src=- shape=ec40df1c vocab=02285812
-/
theorem monotone_of_deriv_nonneg {f : ℝ → ℝ} {a b : ℝ} (_hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b))
    (hfd : DifferentiableOn ℝ f (Set.Ioo a b))
    (hf' : ∀ x ∈ Set.Ioo a b, 0 ≤ deriv f x) :
    MonotoneOn f (Set.Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (D := Set.Icc a b)
  · exact convex_Icc a b
  · exact hfc
  · simpa [interior_Icc] using hfd
  · intro x hx
    exact hf' x (by simpa [interior_Icc] using hx)

/-- 导数恒正 ⟹ 严格递增（MVT 推论）。 
> **Entry**: analysis.mvt.monotone-deriv
@isnad1 id=strictmo.3h3v.s6.ddde3f8543b5 from=translated src=- shape=23a5b1e5 vocab=a3635d03
-/
theorem strict_mono_of_deriv_pos {f : ℝ → ℝ} {a b : ℝ} (_hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b))
    (hf' : ∀ x ∈ Set.Ioo a b, 0 < deriv f x) :
    StrictMonoOn f (Set.Icc a b) := by
  apply strictMonoOn_of_deriv_pos (D := Set.Icc a b)
  · exact convex_Icc a b
  · exact hfc
  · intro x hx
    exact hf' x (by simpa [interior_Icc] using hx)

/-- 柯西中值定理：两函数 f、g 在闭区间连续、开区间可导，则存在 c 使
  (g b − g a)·f'(c) = (f b − f a)·g'(c)。这是 L'Hôpital 法则的基础。
> **Entry**: analysis.mvt.cauchy
@isnad1 id=ex.5h4v.s8.e28d2545af81 from=translated src=- shape=7be17570 vocab=61b33f9d
-/
theorem cauchy_mvt {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b)) (hgc : ContinuousOn g (Set.Icc a b))
    (hgd : DifferentiableOn ℝ g (Set.Ioo a b)) (hfd : DifferentiableOn ℝ f (Set.Ioo a b)) :
    ∃ c ∈ Set.Ioo a b, (g b - g a) * deriv f c = (f b - f a) * deriv g c :=
  exists_ratio_deriv_eq_ratio_slope f hab hfc hfd g hgc hgd

/-- 泰勒定理（带 Lagrange 余项，Rudin Thm 5.15）：f 是 [a,b] 上 n 阶光滑函数，
  则存在 x' 位于 x₀ 与 x 之间，使
  f x = (n 阶 Taylor 多项式在 x 的值) + f⁽ⁿ⁺¹⁾(x')·(x−x₀)ⁿ⁺¹/(n+1)!。
  mathlib 的 `taylor_mean_remainder_lagrange` 给出同款 Lagrange 余项。 
> **Entry**: analysis.mvt.taylor
@isnad1 id=ex.3h4v.s8.67cdb231e443 from=translated src=- shape=f61ada64 vocab=24ae4aae
-/
theorem taylor_lagrange_remainder {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ (↑n) f (Set.uIcc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Set.uIcc x₀ x)) (Set.uIoo x₀ x)) :
    ∃ x' ∈ Set.uIoo x₀ x,
      f x - taylorWithinEval f n (Set.uIcc x₀ x) x₀ x =
        iteratedDerivWithin (n + 1) f (Set.uIcc x₀ x) x' * (x - x₀) ^ (n + 1) / ↑(n + 1).factorial :=
  taylor_mean_remainder_lagrange hx hf hf'

/-- L'Hôpital 法则（0/0 型，Rudin Thm 5.13）：f、g 在 a 的去心邻域可导、g' ≠ 0，
  且 f → 0、g → 0，若 f'/g' → l，则 f/g → l。 
> **Entry**: analysis.mvt.lhopital
@isnad1 id=tendsto.6h6v.s8.f4a102473f30 from=translated src=- shape=a2cc1d62 vocab=ec567c6f
-/
theorem lhopital_zero_real {f g f' g' : ℝ → ℝ} {a : ℝ} {l : ℝ}
    (hff' : ∀ᶠ x in 𝓝[≠] a, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in 𝓝[≠] a, HasDerivAt g (g' x) x)
    (hg' : ∀ᶠ x in 𝓝[≠] a, g' x ≠ 0)
    (hfa : Tendsto f (𝓝[≠] a) (𝓝 0)) (hga : Tendsto g (𝓝[≠] a) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[≠] a) (𝓝 l)) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a) (𝓝 l) :=
  HasDerivAt.lhopital_zero_nhdsNE hff' hgg' hg' hfa hga hdiv

/-- **导数恒为 0 ⟹ 函数为常数**：若 f 处处可导且 f' ≡ 0，则 f 是常值函数。
  （中值定理推论；对任意 x,y 在 [x,y] 上套 Lagrange 即得。） 
> **Entry**: analysis.mvt.constant
@isnad1 id=eq.2h3v.s6.a8ddcce7f930 from=translated src=- shape=05d238ab vocab=b90f06fa
-/
theorem is_constant_of_deriv_zero {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (h0 : ∀ x, deriv f x = 0) (x y : ℝ) : f x = f y := by
  by_cases hxy : x ≤ y
  · rcases lt_or_eq_of_le hxy with hlt | heq
    · have hc : ContinuousOn f (Set.Icc x y) := hf.continuous.continuousOn
      have hd : DifferentiableOn ℝ f (Set.Ioo x y) := hf.differentiableOn.mono (Set.subset_univ (s := Set.Ioo x y))
      rcases exists_deriv_eq_slope f hlt hc hd with ⟨c, hcI, hcslope⟩
      specialize h0 c
      have hfrac : (f y - f x) / (y - x) = 0 := by rw [← hcslope, h0]
      have hyx : y - x ≠ 0 := by linarith
      have hdiff : f y - f x = 0 := by
        rcases (div_eq_zero_iff.mp hfrac) with h1 | h2
        · exact h1
        · exact False.elim (hyx h2)
      suffices f y = f x by exact this.symm
      apply_fun fun z ↦ z - f x
      · simpa using hdiff
      · intro a b hab
        linarith
    · rw [heq]
  · have hyx : y < x := lt_of_not_ge hxy
    have hc : ContinuousOn f (Set.Icc y x) := hf.continuous.continuousOn
    have hd : DifferentiableOn ℝ f (Set.Ioo y x) := hf.differentiableOn.mono (Set.subset_univ (s := Set.Ioo y x))
    rcases exists_deriv_eq_slope f hyx hc hd with ⟨c, hcI, hcslope⟩
    have h0c : deriv f c = 0 := h0 c
    have hfrac : (f x - f y) / (x - y) = 0 := by rw [← hcslope, h0c]
    have hxy0 : x - y ≠ 0 := by linarith
    have hdiff : f x - f y = 0 := by
      rcases (div_eq_zero_iff.mp hfrac) with h1 | h2
      · exact h1
      · exact False.elim (hxy0 h2)
    linarith

/-! ### 有限阶 Taylor–Lagrange 展开实例

这些实例只使用有限阶余项，不使用数项级数或幂级数。 -/

/-- 指数函数的一阶 Taylor–Lagrange 展开。
@isnad1 id=ex.1h1v.s5.251f8e3edf51 from=translated src=- shape=e57d5003 vocab=cd40f20a
-/
theorem exp_taylor_first_order {x : ℝ} (hx : x ≠ 0) :
    ∃ c ∈ Set.uIoo 0 x, Real.exp x = 1 + Real.exp c * x := by
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · have hfc : ContinuousOn Real.exp (Set.Icc x 0) := Real.continuous_exp.continuousOn
    have hff' : ∀ y ∈ Set.Ioo x 0, HasDerivAt Real.exp (Real.exp y) y := by
      intro y hy
      exact Real.hasDerivAt_exp y
    rcases exists_hasDerivAt_eq_slope Real.exp Real.exp hlt hfc hff' with
      ⟨c, hc, hcs⟩
    refine ⟨c, ?_, ?_⟩
    · rw [Set.uIoo_comm, Set.uIoo_of_lt hlt]
      exact hc
    · have hform : Real.exp c = (Real.exp 0 - Real.exp x) / (0 - x) := hcs
      rw [Real.exp_zero] at hform
      field_simp at hform ⊢
      linarith
  · have hfc : ContinuousOn Real.exp (Set.Icc 0 x) := Real.continuous_exp.continuousOn
    have hff' : ∀ y ∈ Set.Ioo 0 x, HasDerivAt Real.exp (Real.exp y) y := by
      intro y hy
      exact Real.hasDerivAt_exp y
    rcases exists_hasDerivAt_eq_slope Real.exp Real.exp hgt hfc hff' with
      ⟨c, hc, hcs⟩
    refine ⟨c, ?_, ?_⟩
    · rw [Set.uIoo_of_lt hgt]
      exact hc
    · have hform : Real.exp c = (Real.exp x - Real.exp 0) / (x - 0) := hcs
      rw [Real.exp_zero] at hform
      field_simp at hform ⊢
      linarith

/-- 正弦函数的二阶 Taylor–Lagrange 展开。
@isnad1 id=ex.1h1v.s6.830a27dadeba from=translated src=- shape=cbe68940 vocab=60f1043e
-/
theorem sin_taylor_second_order {x : ℝ} (hx : x ≠ 0) :
    ∃ c ∈ Set.uIoo 0 x, Real.sin x = x - Real.sin c * x ^ 2 / 2 := by
  rcases taylor_mean_remainder_lagrange_iteratedDeriv (x := x) (x₀ := 0) (n := 1) hx.symm
      (Real.contDiff_sin.contDiffOn) with ⟨c, hc, h⟩
  refine ⟨c, hc, ?_⟩
  have hs : 0 ∈ Set.uIcc (0 : ℝ) x := by simp
  have hu : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) x) := uniqueDiffOn_uIcc hx.symm
  have hd0 : derivWithin Real.sin (Set.uIcc (0 : ℝ) x) 0 = Real.cos 0 :=
    (Real.hasDerivAt_sin 0).hasDerivWithinAt.derivWithin (hu.uniqueDiffWithinAt hs)
  have h' := h
  simp [taylor_within_apply, iteratedDerivWithin_zero, Real.sin_zero, Real.cos_zero,
    hd0, Real.iteratedDeriv_even_sin] at h'
  linarith

/-- 余弦函数的二阶 Taylor–Lagrange 展开。
> **Entry**: analysis.mvt.taylor-examples
@isnad1 id=ex.1h1v.s6.7491c75adee9 from=translated src=- shape=f6b6484f vocab=129ec016
-/
theorem cos_taylor_second_order {x : ℝ} (hx : x ≠ 0) :
    ∃ c ∈ Set.uIoo 0 x, Real.cos x = 1 - Real.cos c * x ^ 2 / 2 := by
  rcases taylor_mean_remainder_lagrange_iteratedDeriv (x := x) (x₀ := 0) (n := 1) hx.symm
      (Real.contDiff_cos.contDiffOn) with ⟨c, hc, h⟩
  refine ⟨c, hc, ?_⟩
  have hs : 0 ∈ Set.uIcc (0 : ℝ) x := by simp
  have hu : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) x) := uniqueDiffOn_uIcc hx.symm
  have hd0 : derivWithin Real.cos (Set.uIcc (0 : ℝ) x) 0 = -Real.sin 0 :=
    (Real.hasDerivAt_cos 0).hasDerivWithinAt.derivWithin (hu.uniqueDiffWithinAt hs)
  have h' := h
  simp [taylor_within_apply, iteratedDerivWithin_zero, Real.cos_zero, Real.sin_zero,
    hd0] at h'
  linarith

end Analysis.MVT

end SandronesLibrary

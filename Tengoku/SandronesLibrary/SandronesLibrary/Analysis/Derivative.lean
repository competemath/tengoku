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
# Analysis / Derivative —— 导数基础条目（第六章）

本文件当前条目（引理清单，§0 铁律4：一次一条，逐条编译）：

* **analysis.derivative.definition**（导数定义）。
* **analysis.derivative.unique**（导数唯一）。
* **analysis.derivative.const**（常数/恒等函数的导数）。
* **analysis.derivative.add**（和/差的导数）。
* **analysis.derivative.mul**（积的导数，Leibniz）。
* **analysis.derivative.div**（商的导数，分母非零）。
* **analysis.derivative.const-mul**（常数数乘的导数）。
* **analysis.derivative.chain-rule**（链式法则）。
* **analysis.derivative.inverse-function**（反函数求导，已完成）。
-/

namespace SandronesLibrary

namespace Analysis.Derivative

/-- 实函数 `f` 在 `x` 处以 `f'` 为导数的教材去心差商极限定义。
> **Entry**: analysis.derivative.definition-/
def HasDerivativeAtTextbook (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  Tendsto (fun y => (f y - f x) / (y - x)) (𝓝[≠] x) (𝓝 f')

/-- 本库差商极限定义与 Mathlib 的 `HasDerivAt` 完全等价。-/
theorem hasDerivativeAtTextbook_iff_hasDerivAt {f : ℝ → ℝ} {f' x : ℝ} :
    HasDerivativeAtTextbook f f' x ↔ HasDerivAt f f' x := by
  have hslope : (fun y => (f y - f x) / (y - x)) = slope f x := by
    funext y
    exact (slope_def_field f x y).symm
  rw [HasDerivativeAtTextbook, hslope]
  exact (hasDerivAt_iff_tendsto_slope (f := f) (f' := f') (x := x)).symm

/-- 教材差商接口下的导数唯一性。-/
theorem hasDerivativeAtTextbook_unique {f : ℝ → ℝ} {x a b : ℝ}
    (ha : HasDerivativeAtTextbook f a x) (hb : HasDerivativeAtTextbook f b x) : a = b := by
  exact (hasDerivativeAtTextbook_iff_hasDerivAt.mp ha).unique
    (hasDerivativeAtTextbook_iff_hasDerivAt.mp hb)

/-- 导数唯一：同一函数同一点的两个导数必相等。
> **Entry**: analysis.derivative.unique-/
lemma deriv_unique_real {f : ℝ → ℝ} {x : ℝ} {a b : ℝ}
    (ha : HasDerivAt f a x) (hb : HasDerivAt f b x) : a = b :=
  HasDerivAt.unique ha hb

/-- 常数函数导数 = 0。 
> **Entry**: analysis.derivative.const-/
lemma deriv_const_real (c : ℝ) (x : ℝ) : deriv (fun _ : ℝ => c) x = 0 :=
  deriv_const x c

/-- 恒等函数导数 = 1。 
> **Entry**: analysis.derivative.const-/
lemma deriv_identity_real (x : ℝ) : deriv (id : ℝ → ℝ) x = 1 :=
  deriv_id x

/-- 线性函数 a·x + b 的导数 = a。 
> **Entry**: analysis.derivative.const-/
lemma deriv_linear_real (a b : ℝ) : deriv (fun x : ℝ => a * x + b) = fun _ => a := by
  funext x
  simp [deriv_add_const]

/-- 和/差导数：deriv (f ± g) = deriv f ± deriv g。 
> **Entry**: analysis.derivative.add-/
lemma deriv_add_sub_real {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (f + g) x = deriv f x + deriv g x :=
  deriv_add hf hg

/-- 积的导数（Leibniz）：(fg)' = f'g + fg'。 
> **Entry**: analysis.derivative.mul-/
lemma deriv_mul_real {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (f * g) x = deriv f x * g x + f x * deriv g x :=
  deriv_mul hf hg

/-- 商导数：deriv (f/g) = (f'g - fg')/g²（g x ≠ 0）。 
> **Entry**: analysis.derivative.div-/
lemma deriv_div_real {f g : ℝ → ℝ} {x : ℝ} (hgx : g x ≠ 0)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (f / g) x = (deriv f x * g x - f x * deriv g x) / (g x ^ 2) :=
  deriv_div hf hg hgx

/-- 常数数乘导数：deriv (c·f) = c·deriv f。 
> **Entry**: analysis.derivative.const-mul-/
lemma deriv_const_mul_real {f : ℝ → ℝ} {x : ℝ} (c : ℝ)
    (hf : DifferentiableAt ℝ f x) : deriv (fun y => c * f y) x = c * deriv f x :=
  deriv_const_mul c hf

/-- 链式法则：deriv (g ∘ f) x = deriv g (f x) · deriv f x。 
> **Entry**: analysis.derivative.chain-rule-/
lemma deriv_chain_rule_real {f : ℝ → ℝ} {g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x)) :
  deriv (fun y => g (f y)) x = deriv g (f x) * deriv f x :=
  deriv_comp x hg hf

/-- 反函数求导的教材层形式：若 `g ∘ f` 在 `x` 的邻域内等于恒等函数，
且 `f' x ≠ 0`，则 `g' (f x) = 1 / f' x`。
> **Entry**: analysis.derivative.inverse-function-/
theorem deriv_inverse_of_eventually_left_inverse
    {f g : ℝ → ℝ} {x f' g' : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' (f x))
    (hinv : ∀ᶠ y in 𝓝 x, g (f y) = y) (hf' : f' ≠ 0) :
    g' = 1 / f' := by
  have hcomp : HasDerivAt (g ∘ f) (g' * f') x := hg.comp x hf
  have hinv' : id =ᶠ[𝓝 x] g ∘ f := by
    filter_upwards [hinv] with y hy
    exact hy.symm
  have hid : HasDerivAt id (g' * f') x := by
    exact hcomp.congr_of_eventuallyEq hinv'
  have hprod : g' * f' = 1 := hid.unique (hasDerivAt_id x)
  field_simp
  exact hprod

end Analysis.Derivative

end SandronesLibrary

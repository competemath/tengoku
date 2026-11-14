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

/-- 本库差商极限定义与 Mathlib 的 `HasDerivAt` 完全等价。
@isnad1 id=iff.0h3v.s5.8878808bdc3e from=translated src=- shape=ab2db3c9 vocab=1f2cd72d
-/
theorem hasDerivativeAtTextbook_iff_hasDerivAt {f : ℝ → ℝ} {f' x : ℝ} :
    HasDerivativeAtTextbook f f' x ↔ HasDerivAt f f' x := by
  have hslope : (fun y => (f y - f x) / (y - x)) = slope f x := by
    funext y
    exact (slope_def_field f x y).symm
  rw [HasDerivativeAtTextbook, hslope]
  exact (hasDerivAt_iff_tendsto_slope (f := f) (f' := f') (x := x)).symm

/-- 教材差商接口下的导数唯一性。
@isnad1 id=eq.2h4v.s4.0edfb9ae7fb1 from=translated src=- shape=ea54e83b vocab=6015fed1
-/
theorem hasDerivativeAtTextbook_unique {f : ℝ → ℝ} {x a b : ℝ}
    (ha : HasDerivativeAtTextbook f a x) (hb : HasDerivativeAtTextbook f b x) : a = b := by
  exact (hasDerivativeAtTextbook_iff_hasDerivAt.mp ha).unique
    (hasDerivativeAtTextbook_iff_hasDerivAt.mp hb)

/-- 导数唯一：同一函数同一点的两个导数必相等。
> **Entry**: analysis.derivative.unique
@isnad1 id=eq.2h4v.s6.dd9088d00c21 from=translated src=- shape=62b5ed6f vocab=6ed66805
-/
lemma deriv_unique_real {f : ℝ → ℝ} {x : ℝ} {a b : ℝ}
    (ha : HasDerivAt f a x) (hb : HasDerivAt f b x) : a = b :=
  HasDerivAt.unique ha hb

/-- 常数函数导数 = 0。 
> **Entry**: analysis.derivative.const
@isnad1 id=eq.0h2v.s5.307a77c42cec from=translated src=- shape=0e65ef63 vocab=f7be9ba9
-/
lemma deriv_const_real (c : ℝ) (x : ℝ) : deriv (fun _ : ℝ => c) x = 0 :=
  deriv_const x c

/-- 恒等函数导数 = 1。 
> **Entry**: analysis.derivative.const
@isnad1 id=eq.0h1v.s5.882d6d8c209b from=translated src=- shape=420b7cd7 vocab=cb95453f
-/
lemma deriv_identity_real (x : ℝ) : deriv (id : ℝ → ℝ) x = 1 :=
  deriv_id x

/-- 线性函数 a·x + b 的导数 = a。 
> **Entry**: analysis.derivative.const
@isnad1 id=eq.0h2v.s5.459c075ee6cc from=translated src=- shape=8c3dd78e vocab=e288efc8
-/
lemma deriv_linear_real (a b : ℝ) : deriv (fun x : ℝ => a * x + b) = fun _ => a := by
  funext x
  simp [deriv_add_const]

/-- 和/差导数：deriv (f ± g) = deriv f ± deriv g。 
> **Entry**: analysis.derivative.add
@isnad1 id=eq.2h3v.s7.2cfeac03bb49 from=translated src=- shape=151c00bb vocab=451cfb76
-/
lemma deriv_add_sub_real {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (f + g) x = deriv f x + deriv g x :=
  deriv_add hf hg

/-- 积的导数（Leibniz）：(fg)' = f'g + fg'。 
> **Entry**: analysis.derivative.mul
@isnad1 id=eq.2h3v.s7.60d35a42dfe6 from=translated src=- shape=8ef6fb50 vocab=746dbe48
-/
lemma deriv_mul_real {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (f * g) x = deriv f x * g x + f x * deriv g x :=
  deriv_mul hf hg

/-- 商导数：deriv (f/g) = (f'g - fg')/g²（g x ≠ 0）。 
> **Entry**: analysis.derivative.div
@isnad1 id=eq.3h3v.s8.57bccc49917a from=translated src=- shape=1932b95e vocab=531edc97
-/
lemma deriv_div_real {f g : ℝ → ℝ} {x : ℝ} (hgx : g x ≠ 0)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (f / g) x = (deriv f x * g x - f x * deriv g x) / (g x ^ 2) :=
  deriv_div hf hg hgx

/-- 常数数乘导数：deriv (c·f) = c·deriv f。 
> **Entry**: analysis.derivative.const-mul
@isnad1 id=eq.1h3v.s7.4c12bff7e11d from=translated src=- shape=f679fb4e vocab=818e4c89
-/
lemma deriv_const_mul_real {f : ℝ → ℝ} {x : ℝ} (c : ℝ)
    (hf : DifferentiableAt ℝ f x) : deriv (fun y => c * f y) x = c * deriv f x :=
  deriv_const_mul c hf

/-- 链式法则：deriv (g ∘ f) x = deriv g (f x) · deriv f x。 
> **Entry**: analysis.derivative.chain-rule
@isnad1 id=eq.2h3v.s7.82f9aa8ab29a from=translated src=- shape=93b74b11 vocab=818e4c89
-/
lemma deriv_chain_rule_real {f : ℝ → ℝ} {g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x)) :
  deriv (fun y => g (f y)) x = deriv g (f x) * deriv f x :=
  deriv_comp x hg hf

/-- 反函数求导的教材层形式：若 `g ∘ f` 在 `x` 的邻域内等于恒等函数，
且 `f' x ≠ 0`，则 `g' (f x) = 1 / f' x`。
> **Entry**: analysis.derivative.inverse-function
@isnad1 id=eq.4h5v.s7.feb9885281eb from=translated src=- shape=1d389879 vocab=e682d7ac
-/
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

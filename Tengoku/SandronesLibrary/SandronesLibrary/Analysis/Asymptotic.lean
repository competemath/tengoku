/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Filter Topology

/-!
# Analysis / Asymptotic —— 初等函数的渐进比较

本模块收录数学分析中最常用的增长阶结论：对数相对于恒等函数是高阶无穷小，
指数函数相对于任意固定自然幂是高阶无穷大。所有结论使用 `Tendsto` 和
`IsLittleO` 表述，服务于后续无穷小/无穷大阶比较。
-/

namespace SandronesLibrary
namespace Analysis.Asymptotic

/-- 对数函数在正无穷处趋于正无穷。-/
theorem log_tendsto_atTop : Tendsto Real.log atTop atTop := by
  exact Real.tendsto_log_atTop

/-- 对数函数相对于恒等函数是高阶无穷小。
> **Entry**: analysis.limits.asymptotic-/
theorem log_little_o_id : (fun x : ℝ => Real.log x) =o[atTop] id := by
  exact Real.isLittleO_log_id_atTop

/-- 指数函数除以任意固定自然幂后仍趋于正无穷。-/
theorem exp_div_pow_tendsto_atTop (n : ℕ) :
    Tendsto (fun x : ℝ => Real.exp x / x ^ n) atTop atTop := by
  exact Real.tendsto_exp_div_pow_atTop n

/-- 任意固定自然幂相对于指数函数是高阶无穷小。-/
theorem pow_little_o_exp (n : ℕ) :
    (fun x : ℝ => x ^ n) =o[atTop] Real.exp := by
  exact Real.isLittleO_pow_exp_atTop

end Analysis.Asymptotic
end SandronesLibrary

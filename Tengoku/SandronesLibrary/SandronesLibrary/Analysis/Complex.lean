/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Analysis / Complex —— 复数的教材定义与基本运算

复数由一对实数 `(x,y)` 构成，记作 `x+yi`。本文件把这一教材定义与 mathlib 的
复数类型 `ℂ` 对齐，并给出实部、虚部、加法、乘法、虚数单位、共轭和模的基本公式。
-/

namespace SandronesLibrary.Analysis.Complex

/-- 由实部 `x` 与虚部 `y` 构成复数 `x + yi`。

> **Entry**: analysis.complex.definition-/
def mk (x y : ℝ) : ℂ := ⟨x, y⟩

/-- 两个复数相等当且仅当实部、虚部分别相等。-/
theorem ext_iff (z w : ℂ) : z = w ↔ z.re = w.re ∧ z.im = w.im := by
  exact _root_.Complex.ext_iff

/-- 每个复数唯一写成 `x + yi`。-/
theorem existsUnique_real_imag (z : ℂ) :
    ∃! p : ℝ × ℝ, z = mk p.1 p.2 := by
  refine ⟨(z.re, z.im), ?_, ?_⟩
  · apply Complex.ext <;> rfl
  · rintro ⟨x, y⟩ h
    apply Prod.ext
    · exact congrArg Complex.re h |>.symm
    · exact congrArg Complex.im h |>.symm

@[simp] theorem mk_re (x y : ℝ) : (mk x y).re = x := rfl
@[simp] theorem mk_im (x y : ℝ) : (mk x y).im = y := rfl

/-- 复数加法逐坐标进行。-/
theorem mk_add (x y u v : ℝ) : mk x y + mk u v = mk (x + u) (y + v) := by
  apply Complex.ext <;> simp [mk]

/-- 复数乘法由 `i²=-1` 展开。-/
theorem mk_mul (x y u v : ℝ) :
    mk x y * mk u v = mk (x * u - y * v) (x * v + y * u) := by
  apply Complex.ext <;> simp [mk]

/-- 虚数单位就是实部为零、虚部为一的复数。-/
theorem I_eq_mk : Complex.I = mk 0 1 := by
  apply Complex.ext <;> simp [mk]

/-- 虚数单位满足 `i²=-1`。-/
theorem I_sq : Complex.I ^ 2 = -1 := by
  norm_num [pow_two]

/-- 共轭保持实部并反转虚部。-/
theorem conj_mk (x y : ℝ) : star (mk x y) = mk x (-y) := by
  apply Complex.ext <;> simp [mk]

/-- 复数与其共轭之积等于实数 `x²+y²`。-/
theorem mul_conj (x y : ℝ) :
    mk x y * star (mk x y) = mk (x ^ 2 + y ^ 2) 0 := by
  rw [conj_mk, mk_mul]
  apply Complex.ext <;> simp [mk] <;> ring

/-- 复数模平方是实部、虚部平方和。-/
theorem norm_sq (x y : ℝ) : ‖mk x y‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [_root_.Complex.sq_norm, _root_.Complex.normSq_apply]
  simp [mk]
  ring

end SandronesLibrary.Analysis.Complex

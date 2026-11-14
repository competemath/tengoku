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

/-- 两个复数相等当且仅当实部、虚部分别相等。
@isnad1 id=iff.0h2v.s4.1d71beb6cc73 from=translated src=- shape=1839e622 vocab=f4acbe6d
-/
theorem ext_iff (z w : ℂ) : z = w ↔ z.re = w.re ∧ z.im = w.im := by
  exact _root_.Complex.ext_iff

/-- 每个复数唯一写成 `x + yi`。
@isnad1 id=existsun.0h1v.s4.2bc7d7475371 from=translated src=- shape=770342e7 vocab=5097e2a3
-/
theorem existsUnique_real_imag (z : ℂ) :
    ∃! p : ℝ × ℝ, z = mk p.1 p.2 := by
  refine ⟨(z.re, z.im), ?_, ?_⟩
  · apply Complex.ext <;> rfl
  · rintro ⟨x, y⟩ h
    apply Prod.ext
    · exact congrArg Complex.re h |>.symm
    · exact congrArg Complex.im h |>.symm

/--
@isnad1 id=eq.0h2v.s3.a6949cea1ed6 from=translated src=- shape=a92ce29b vocab=5b128e9f
-/
@[simp] theorem mk_re (x y : ℝ) : (mk x y).re = x := rfl
/--
@isnad1 id=eq.0h2v.s3.e9af5aac1919 from=translated src=- shape=bed1e912 vocab=033f888d
-/
@[simp] theorem mk_im (x y : ℝ) : (mk x y).im = y := rfl

/-- 复数加法逐坐标进行。
@isnad1 id=eq.0h4v.s5.f5657feef13f from=translated src=- shape=8a7b2152 vocab=886206bf
-/
theorem mk_add (x y u v : ℝ) : mk x y + mk u v = mk (x + u) (y + v) := by
  apply Complex.ext <;> simp [mk]

/-- 复数乘法由 `i²=-1` 展开。
@isnad1 id=eq.0h4v.s6.9f2faf63a5ee from=translated src=- shape=0de13652 vocab=ef48f04d
-/
theorem mk_mul (x y u v : ℝ) :
    mk x y * mk u v = mk (x * u - y * v) (x * v + y * u) := by
  apply Complex.ext <;> simp [mk]

/-- 虚数单位就是实部为零、虚部为一的复数。
@isnad1 id=eq.0h0v.s4.98713931ba30 from=translated src=- shape=7a1d0b68 vocab=dc55fd49
-/
theorem I_eq_mk : Complex.I = mk 0 1 := by
  apply Complex.ext <;> simp [mk]

/-- 虚数单位满足 `i²=-1`。
@isnad1 id=eq.0h0v.s4.0339f25317f2 from=translated src=- shape=8e19147c vocab=281d2493
-/
theorem I_sq : Complex.I ^ 2 = -1 := by
  norm_num [pow_two]

/-- 共轭保持实部并反转虚部。
@isnad1 id=eq.0h2v.s5.59cf09be7e8d from=translated src=- shape=9fe33465 vocab=72e4552b
-/
theorem conj_mk (x y : ℝ) : star (mk x y) = mk x (-y) := by
  apply Complex.ext <;> simp [mk]

/-- 复数与其共轭之积等于实数 `x²+y²`。
@isnad1 id=eq.0h2v.s6.6055acb92618 from=translated src=- shape=782f7c53 vocab=da81a8bb
-/
theorem mul_conj (x y : ℝ) :
    mk x y * star (mk x y) = mk (x ^ 2 + y ^ 2) 0 := by
  rw [conj_mk, mk_mul]
  apply Complex.ext <;> simp [mk] <;> ring

/-- 复数模平方是实部、虚部平方和。
@isnad1 id=eq.0h2v.s6.3423b9cf2f80 from=translated src=- shape=9dd1f078 vocab=542db8db
-/
theorem norm_sq (x y : ℝ) : ‖mk x y‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [_root_.Complex.sq_norm, _root_.Complex.normSq_apply]
  simp [mk]
  ring

end SandronesLibrary.Analysis.Complex

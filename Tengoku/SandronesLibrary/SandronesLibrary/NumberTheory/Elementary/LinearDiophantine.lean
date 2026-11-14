/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.Data.Int.GCD
import Tengoku.Seed.Algebra.Ring.Divisibility.Basic
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 二元一次不定方程

本文件当前条目：

- `number-theory.elementary.linear-diophantine`：方程 `a x + b y = c` 的 gcd 可解判据。

先用扩展 Euclid 算法显式构造 `gcd(a,b)` 的任意倍数，再把必要性与充分性组装为教材判据。
-/

namespace SandronesLibrary.NumberTheory.Elementary

/-- 二元一次不定方程 `a x + b y = c` 在整数中有解。
> **Entry**: number-theory.elementary.linear-diophantine-/
def LinearDiophantineSolvable (a b c : ℤ) : Prop :=
  ∃ x y : ℤ, a * x + b * y = c

/-- 扩展 Euclid 系数给出 `a x + b y = gcd(a,b)·k` 的显式解：
`x = gcdA(a,b)·k`，`y = gcdB(a,b)·k`。
> **Entry**: number-theory.elementary.linear-diophantine
@isnad1 id=lineardi.0h3v.s4.42aed90dff6e from=translated src=- shape=9a1a56aa vocab=1484202a
-/
theorem linearDiophantine_of_gcd_mul (a b k : ℤ) :
    LinearDiophantineSolvable a b ((Int.gcd a b : ℤ) * k) := by
  refine ⟨Int.gcdA a b * k, Int.gcdB a b * k, ?_⟩
  calc
    a * (Int.gcdA a b * k) + b * (Int.gcdB a b * k) =
        (a * Int.gcdA a b + b * Int.gcdB a b) * k := by ring
    _ = (Int.gcd a b : ℤ) * k := by rw [← Int.gcd_eq_gcd_ab]

/-- **二元一次不定方程可解判据**：`a x + b y = c` 有整数解，当且仅当
`gcd(a,b)` 整除 `c`。
> **Entry**: number-theory.elementary.linear-diophantine
@isnad1 id=iff.0h3v.s4.a6b3ab1c9044 from=translated src=- shape=82cb927c vocab=b2297a1c
-/
theorem linearDiophantine_iff_gcd_dvd (a b c : ℤ) :
    LinearDiophantineSolvable a b c ↔ (Int.gcd a b : ℤ) ∣ c := by
  constructor
  · rintro ⟨x, y, rfl⟩
    exact dvd_add (dvd_mul_of_dvd_left (Int.gcd_dvd_left a b) x)
      (dvd_mul_of_dvd_left (Int.gcd_dvd_right a b) y)
  · rintro ⟨k, rfl⟩
    exact linearDiophantine_of_gcd_mul a b k

/-- `a,b` 互素，当且仅当每一个整数 `c` 都能写成 `a x + b y`。
这是 Bézout 恒等式与线性不定方程判据的统一表述。
> **Entry**: number-theory.elementary.linear-diophantine
@isnad1 id=iff.0h2v.s4.5af7b52931f4 from=translated src=- shape=b2d2e25b vocab=15d49b8e
-/
theorem coprime_iff_linearDiophantine_all (a b : ℤ) :
    Int.gcd a b = 1 ↔ ∀ c : ℤ, LinearDiophantineSolvable a b c := by
  constructor
  · intro hgcd c
    apply (linearDiophantine_iff_gcd_dvd a b c).mpr
    rw [hgcd]
    exact one_dvd c
  · intro h
    have hdvdInt : (Int.gcd a b : ℤ) ∣ (1 : ℤ) :=
      (linearDiophantine_iff_gcd_dvd a b 1).mp (h 1)
    have hdvdNat : Int.gcd a b ∣ (1 : ℕ) := by
      exact_mod_cast hdvdInt
    exact Nat.dvd_one.mp hdvdNat

end SandronesLibrary.NumberTheory.Elementary

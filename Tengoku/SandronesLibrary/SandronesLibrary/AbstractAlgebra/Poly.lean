/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# AbstractAlgebra / Polynomial —— 多项式环与整除性（抽象代数第一学期 A3）

本文件当前条目（引理清单，§0 铁律4：一次一条，逐条编译）：

* **abstract-algebra.poly.mathlib-compat**（历史 Mathlib 多项式兼容接口；含由旧 `Poly.lean`
  不可约性/带余除法块重归的历史包装）✅。
* **abstract-algebra.poly.roots-card**（根属于根集/乘积的根/根个数≤次数）✅。

> 不可约性的规范条目位于 `SandronesLibrary/AbstractAlgebra/PolynomialIrreducibility.lean`；
> 本文件不再承载该 Entry。

> **语言说明**：抽象代数阶段（§Phase3）允许直接用 mathlib 的 `Polynomial`/`Irreducible`/
> `EuclideanDomain` 等教材结构；`Module` 仍不允许（线性代数已用 LinearSpace 承载）。
-/

open Polynomial

namespace SandronesLibrary

namespace AbstractAlgebra.Poly

/-- **多项式外延性**：各项系数全相等 ⟹ 多项式相等。 
> **Entry**: abstract-algebra.poly.mathlib-compat
@isnad1 id=eq.1h3v.s5.de503d65368d from=translated src=- shape=48e4affc vocab=0261ec8b
-/
theorem poly_ext {R : Type*} [Semiring R] {p q : R[X]} (h : ∀ n : ℕ, p.coeff n = q.coeff n) :
    p = q := by
  exact Polynomial.ext h

/-- **多项式的根**（教材定义）：a 是 p 的根 ⟺ 在 a 处取值为 0。
@isnad1 id=iff.0h3v.s5.3c2f0c125912 from=translated src=- shape=c2519556 vocab=216724cb
-/
theorem is_root_iff_eval_eq_zero {R : Type*} [Semiring R] (p : R[X]) (a : R) :
    p.IsRoot a ↔ p.eval a = 0 := by
  rfl

/-- **因式定理（X−a 整除 ⟺ 根）**：X − C a 整除 p ⟺ a 是 p 的根。
  教材核心：a 是根 ⟺ 多项式含因式 X−a。 
> **Entry**: abstract-algebra.poly.mathlib-compat
@isnad1 id=iff.0h3v.s7.2db1d1e246d4 from=translated src=- shape=b7cf5bed vocab=ebf29daa
-/
theorem dvd_X_sub_C_iff_isRoot {R : Type*} [CommRing R] (p : R[X]) (a : R) :
    X - C a ∣ p ↔ p.IsRoot a := by
  exact Polynomial.dvd_iff_isRoot (p := p) (a := a)

/-- **多项式环整环性**：系数环 R 是整环 ⟹ 多项式环 R[X] 是整环。 
> **Entry**: abstract-algebra.poly.mathlib-compat
@isnad1 id=isdomain.0h1v.s4.a7276962e1f4 from=translated src=- shape=d96e9922 vocab=2b116b70
-/
theorem poly_is_domain_of_is_domain {R : Type*} [CommRing R] [IsDomain R] :
    IsDomain R[X] := by
  infer_instance

/-- **多项式环的单位元 = 非零常数**：p 可逆 ⟺ p 是某个可逆常数。 
> **Entry**: abstract-algebra.poly.mathlib-compat
@isnad1 id=iff.0h2v.s6.82221fffa54b from=translated src=- shape=77016aba vocab=f72b148c
-/
theorem poly_isUnit_iff {R : Type*} [Semiring R] [NoZeroDivisors R] (p : R[X]) :
    IsUnit p ↔ ∃ r : R, IsUnit r ∧ C r = p := by
  exact Polynomial.isUnit_iff

/-- **不可约的教材判据**：p 不可约 ⟹ 若 p = a·b，则 a 或 b 是单位。 
> **Entry**: abstract-algebra.poly.mathlib-compat
@isnad1 id=or.2h4v.s5.643faa0dd481 from=translated src=- shape=2fb42bae vocab=3e966289
-/
theorem irreducible_mul_iff {M : Type*} [Monoid M] {p : M} (hp : Irreducible p)
    {a b : M} (hab : p = a * b) : IsUnit a ∨ IsUnit b := by
  exact hp.isUnit_or_isUnit hab

/-- **X − a 不可约**：一次因式 X−a 是不可约多项式。 
> **Entry**: abstract-algebra.poly.mathlib-compat
@isnad1 id=irreduci.0h2v.s7.85d65f38e700 from=translated src=- shape=9abf7de4 vocab=41de03f2
-/
theorem irreducible_X_sub_C {R : Type*} [CommRing R] [IsDomain R] (a : R) :
    Irreducible (X - C a) := by
  exact Polynomial.irreducible_X_sub_C a

/-- **X 不可约**：不定元 X 本身是不可约多项式。 
> **Entry**: abstract-algebra.poly.mathlib-compat
@isnad1 id=irreduci.0h1v.s5.a78b2e352301 from=translated src=- shape=da9a72aa vocab=f7cc85f9
-/
theorem irreducible_X {R : Type*} [CommRing R] [IsDomain R] :
    Irreducible (X : R[X]) := by
  exact Polynomial.irreducible_X

/-- **次数 1 多项式不可约**（域上）：域上的一次多项式是不可约的。 
> **Entry**: abstract-algebra.poly.mathlib-compat
@isnad1 id=irreduci.1h2v.s6.73a1e5be41c7 from=translated src=- shape=80331c54 vocab=3ffcadce
-/
theorem irreducible_of_degree_eq_one {R : Type*} [Field R] {p : R[X]}
    (hp : p.degree = 1) : Irreducible p := by
  exact Polynomial.irreducible_of_degree_eq_one hp

/-- **带余除法整除判据**：p 被首一多项式 q 整除 ⟺ 余式为 0（`p %ₘ q = 0`）。 
> **Entry**: abstract-algebra.poly.mathlib-compat
@isnad1 id=iff.1h3v.s6.c308f0722aff from=translated src=- shape=898d2caa vocab=345380c8
-/
theorem modByMonic_eq_zero_iff_dvd {R : Type*} [Ring R] {p q : R[X]}
    (hq : q.Monic) : p %ₘ q = 0 ↔ q ∣ p := by
  exact Polynomial.modByMonic_eq_zero_iff_dvd hq

/-- **余式次数小于除式**：带余除法中，余式次数严格小于除式次数（欧几里得性质）。 
> **Entry**: abstract-algebra.poly.mathlib-compat
@isnad1 id=lt.1h3v.s5.85789355cf95 from=translated src=- shape=a66dbf6e vocab=d978da56
-/
theorem degree_modByMonic_lt {R : Type*} [Ring R] [Nontrivial R] (p : R[X])
    {q : R[X]} (hq : q.Monic) : (p %ₘ q).degree < q.degree := by
  exact Polynomial.degree_modByMonic_lt p hq

/-- **根属于根集**：a 是 p 的根 ⟺ a 属于根集 p.roots（根集 = 全体根的 multiset）。 
> **Entry**: abstract-algebra.poly.mathlib-compat
@isnad1 id=iff.1h3v.s6.3db912f6fd5f from=translated src=- shape=bc21b5ec vocab=6c30cdc6
-/
theorem mem_roots_iff_isRoot {R : Type*} [CommRing R] [IsDomain R] {p : R[X]}
    (hp : p ≠ 0) (a : R) : a ∈ p.roots ↔ p.IsRoot a := by
  exact Polynomial.mem_roots hp

/-- **乘积的根**：a 是 p·q 的根 ⟺ a 是 p 的根或 q 的根（整环上）。 
> **Entry**: abstract-algebra.poly.mathlib-compat
@isnad1 id=iff.0h4v.s6.5a575faf0bc2 from=translated src=- shape=355196c3 vocab=5459387e
-/
theorem root_mul_iff {R : Type*} [CommRing R] [IsDomain R] {p q : R[X]} (a : R) :
    (p * q).IsRoot a ↔ p.IsRoot a ∨ q.IsRoot a := by
  exact Polynomial.root_mul (a := a)

/-- **根的个数不超过次数**：非零 n 次多项式至多有 n 个根（含重数计）。
  教材核心定理：域上 n 次多项式至多 n 个根。 
> **Entry**: abstract-algebra.poly.roots-card
@isnad1 id=le.1h2v.s6.f6477fc55d8f from=translated src=- shape=308137d9 vocab=59d418a3
-/
theorem card_roots_le_degree {R : Type*} [CommRing R] [IsDomain R] {p : R[X]}
    (hp : p ≠ 0) : (p.roots.card : WithBot ℕ) ≤ p.degree := by
  exact Polynomial.card_roots hp

end AbstractAlgebra.Poly

end SandronesLibrary

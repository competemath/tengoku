/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Analysis / Real —— 实数系基础条目

本文件当前条目：

* **analysis.real.archimedean**（阿基米德性质）：对任意正实数 x 与实数 y，
  存在自然数 n 使得 n·x > y。实数系是阿基米德序域的直接推论。
* **analysis.real.bounded-sets.bdd-above**（有上界集）：`BddAbove s` ⟺
  存在上界 M 使得每个 x ∈ s 满足 x ≤ M。
* **analysis.real.bounded-sets.subset**（子集继承有界）：`s ⊆ t` 且 `t` 有上界
  ⇒ `s` 有上界。
* **analysis.real.density**（有理数稠密）：任意两个实数之间夹着一个有理数。
* **analysis.real.sup**（确界原理/完备性）：非空有上界集的上确界存在，
  且 `sSup s` 正是其最小上界。
* **analysis.real.bounded-sets.bdd-below**（有下界集）：`BddBelow s` ⟺
  存在下界 a 使得每个 x ∈ s 满足 a ≤ x。
* **analysis.real.inf**（下确界原理）：非空有下界集 s 的下确界 `sInf s` 是 s 的下界，
  且是所有下界里最大的。确界原理的下界镜像。
* **analysis.real.construction-cauchy**（实数构造 · Cantor）：实数 = 有理柯西序列的等价类；
  "差序列趋于 0"是等价关系；两条序列给出同一实数 ⟺ 它们之差趋于 0；
  每个有理数给出常量柯西序列，从而可嵌入实数。
-/

namespace SandronesLibrary

namespace Analysis.Real

/--
> **Entry**: analysis.real.archimedean
> **一句话**: 对任意正实数 x 与实数 y，存在自然数 n 使得 n·x > y。
> **直觉**: 把"步长 x"放大 n 倍能超过任何给定的 y；等价地，整数 n 能超过 y/x。
> **依赖**: 无（直接使用 mathlib 的 `exists_nat_gt`，即 `Archimedean ℝ` 实例）
> **mathlib**: `exists_nat_gt`, `div_lt_iff₀`
@isnad1 id=ex.1h2v.s5.0e73be3ab59c from=translated src=- shape=063438c2 vocab=632e02f8
-/
theorem archimedean_property (x y : ℝ) (hx : 0 < x) : ∃ n : ℕ, y < n * x := by
  -- 思路：目标是"放大步长 x 超过 y"，化为"整数超过比值 y/x"，
  -- 由实数的阿基米德性（Archimedean 类型类）保证整数可以任意大。
  -- Step 1: 用 exists_nat_gt 选一个 n : ℕ 使得 y/x < n（choose 取 witness，choose_spec 是其性质）。
  let n := (exists_nat_gt (y / x)).choose
  use n
  -- Step 2: 回到原来的不等式：y/x < n 且 x > 0 ⇔ y < n·x（乘正数不改变序方向）。
  exact (div_lt_iff₀ hx).mp (exists_nat_gt (y / x)).choose_spec

/-- 由阿基米德性质直接推出 `exists_nat_gt` 的整数倍形式（供后续条目复用）。
@isnad1 id=ex.1h2v.s5.0e73be3ab59c from=translated src=- shape=063438c2 vocab=632e02f8
-/
theorem exists_nat_mul_gt (x y : ℝ) (hx : 0 < x) : ∃ n : ℕ, y < n * x :=
  archimedean_property x y hx

/--
> **Entry**: analysis.real.bounded-sets.bdd-above
> **一句话**: "集合有上界" 的定义展开：存在实数 M 使每个元素都不超过 M。
> **直觉**: BddAbove 就是"把所有元素摁在某个天花板 M 下面"。
> **依赖**: 无
> **mathlib**: `BddAbove`
@isnad1 id=iff.0h1v.s4.c8a4b2128237 from=translated src=- shape=4a013a2f vocab=0cdd3465
-/
theorem bdd_above_iff (s : Set ℝ) : BddAbove s ↔ ∃ M : ℝ, ∀ x ∈ s, x ≤ M := by
  -- 思路：BddAbove 在 mathlib 里就是 `∃ a, ∀ b ∈ s, b ≤ a`，逐字展开即得。
  rfl

/--
> **Entry**: analysis.real.bounded-sets.subset
> **一句话**: 有上界集的子集仍然有上界：`s ⊆ t` 且 `t` 有上界 ⇒ `s` 有上界。
> **直觉**: 天花板对更大的集合有效，当然对小集合也有效——同一个 M 继续用。
> **依赖**: `analysis.real.bounded-sets.bdd-above`
> **mathlib**: `BddAbove.mono`
@isnad1 id=bddabove.2h2v.s4.90e436e7b2c9 from=translated src=- shape=f42ca658 vocab=7bbffe42
-/
theorem bdd_above_subset {s t : Set ℝ} (hst : s ⊆ t) (ht : BddAbove t) : BddAbove s := by
  -- 思路：t 有上界 M，s 的每个元素都在 t 里，所以都不超过 M。
  exact BddAbove.mono hst ht

/--
> **Entry**: analysis.real.density
> **一句话**: 有理数在实数中稠密：任意两个实数之间存在有理数。
> **直觉**: 无论两个实数贴得多近，总能塞进一个有理数——有理数是实数的"可数骨架"。
> **依赖**: 无
> **mathlib**: `exists_rat_btwn`
@isnad1 id=ex.1h2v.s4.1623d77c3d99 from=translated src=- shape=f4943276 vocab=6efc4b7c
-/
theorem rational_dense (x y : ℝ) (hxy : x < y) : ∃ q : ℚ, x < (q : ℝ) ∧ (q : ℝ) < y := by
  -- 思路：教材用阿基米德性质构造分母 n 再取分子；mathlib 的 `exists_rat_btwn`
  -- 已把这个构造打包成多态版本（任意阿基米德序域），直接引用。
  exact exists_rat_btwn hxy

/--
> **Entry**: analysis.real.sup
> **一句话**: 确界原理（完备性）：非空有上界集必有上确界，`sSup s` 即其最小上界。
> **直觉**: 实数是"不露缝"的——任何被压住不放手的集合，都会碰到天花板本身。
>   这是 ℚ 没有的性质（{q | q² < 2} 在 ℚ 里没有上确界）。
> **依赖**: `analysis.real.bounded-sets.bdd-above`
> **mathlib**: `Real.isLUB_sSup`
@isnad1 id=islub.2h1v.s4.955b6b0ef5bc from=translated src=- shape=6d45767b vocab=7ce05715
-/
theorem sup_lub (s : Set ℝ) (hne : s.Nonempty) (hbdd : BddAbove s) : IsLUB s (sSup s) := by
  -- 思路：sSup 是"条件完备格"提供的最小上界算子；`IsLUB s (sSup s)` 正是
  -- "sSup 是 s 的上界，且是最小的上界"。这正是教科书的确界原理。
  exact Real.isLUB_sSup hne hbdd

/--
> **Entry**: analysis.real.bounded-sets.bdd-below
> **一句话**: 集合 s 有下界 ⟺ 存在实数 a 使得 s 的每个元素都不小于 a。
> **直觉**: 下界就是"天花板"的镜像：从上方压的是上界，从下方托住的是下界。
>   这是 `bdd-above` 的整形拷贝——把"上"换成"下"、把 `x ≤ M` 换成 `a ≤ x`。
> **依赖**: 无（定义展开即终局）
> **mathlib**: `BddBelow`, `Set.Nonempty`
@isnad1 id=iff.0h1v.s4.aba434eba76f from=translated src=- shape=85f7838f vocab=c0d2d557
-/
theorem bdd_below_iff (s : Set ℝ) : BddBelow s ↔ ∃ a : ℝ, ∀ x ∈ s, a ≤ x := by
  -- 思路：`BddBelow s` 的定义就是"存在 a 对 s 中一切 x 有 a ≤ x"，
  -- 所以左右两边逐词相同，`rfl` 即证。
  rfl

/--
> **Entry**: analysis.real.inf
> **一句话**: 非空且有下界的集合 s，其下确界 `sInf s` 是 s 的下界，
>   且大于等于一切别的下界（最大的下界）。
> **直觉**: 上确界是"被压住时的天花板"，下确界是"被托住时的地板"。
>   确界原理说天花板必存在，对地板是同一回事（换个方向）。
> **依赖**: `analysis.real.bounded-sets.bdd-below`
> **mathlib**: `sInf`, `IsGLB`, `isGLB_csInf`
@isnad1 id=isglb.2h1v.s4.2b88e22d9a21 from=translated src=- shape=6d45767b vocab=3370bd49
-/
theorem inf_glb (s : Set ℝ) (hne : s.Nonempty) (hbdd : BddBelow s) : IsGLB s (sInf s) := by
  -- 思路：与 sup_lub 完全对称：`IsGLB s (sInf s)` 即 "sInf s 是 s 的下界，
  -- 且是所有下界中最大的"。sInf 由条件完备格提供，直接引用。
  exact isGLB_csInf hne hbdd

/--
> **Entry**: analysis.real.construction-cauchy
> **一句话**: 实数 = 有理柯西序列的等价类；"差序列趋于 0"是等价关系；
>   两条序列给同一实数 ⟺ 差趋于 0；每个有理数给出常量柯西序列（嵌入）。
> **直觉**: 用有理数去"逼近"实数。放任所有有理柯西序列为候选，
>   再把给出同一个实数的（差趋于 0）合并成一个等价类，商得的每个类就是一个实数。
> **依赖**: `settheory.set.relations`（等价关系/商集）
> **mathlib**: `CauSeq`, `CauSeq.equiv`, `CauSeq.Completion.mk`, `Real.ofCauchy`
>
> 本条收录：
> * `cau_equiv_refl` / `cau_equiv_symm` / `cau_equiv_trans`：差趋于 0 是等价关系；
> * `real_eq_iff_cau_equiv`：商构造的核心判等准则；
> * `rat_const_cauchy`：每个有理数给出常量柯西序列（嵌入）。
>
> （`cau_equiv_refl` 的证明体纯构造——ε-δ 直写；`#print axioms` 仍报
> `Classical.choice`，来源是 `CauSeq.equiv` 实例被 reducible 展开而带入的
> 库内证明开销，非本条目数学内容——Playbook §3.5。）
@isnad1 id=equiv.0h1v.s5.938a0adf2251 from=translated src=- shape=16a9ded1 vocab=74f1e691
-/
theorem cau_equiv_refl (f : CauSeq ℚ (abs : ℚ → ℚ)) : f ≈ f := by
  intro ε hε
  refine ⟨0, ?_⟩
  intro j hj
  simpa [sub_eq_add_neg] using hε

/-- "差趋于 0"是等价关系（对称性）：|aₙ − bₙ| 与 |bₙ − aₙ| 同趋于 0。
@isnad1 id=equiv.0h3v.s6.622725b3142d from=translated src=- shape=bf2b2928 vocab=74f1e691
-/
theorem cau_equiv_symm {f g : CauSeq ℚ (abs : ℚ → ℚ)} (h : f ≈ g) : g ≈ f := by
  intro ε hε
  rcases h ε hε with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  intro j hj
  simpa [abs_sub_comm] using hi j hj

/-- "差趋于 0"是等价关系（传递性）：三角不等式 |aₙ − cₙ| ≤ |aₙ − bₙ| + |bₙ − cₙ|
  把两步趋近接力成一步趋近，这正是等价关系里最难、也最关键的性质。
@isnad1 id=equiv.0h5v.s7.ffa13c7d835f from=translated src=- shape=867ed65b vocab=74f1e691
-/
theorem cau_equiv_trans {f g h : CauSeq ℚ (abs : ℚ → ℚ)}
    (hfg : f ≈ g) (hgh : g ≈ h) : f ≈ h := by
  intro ε hε
  rcases hfg (ε / 2) (half_pos hε) with ⟨i, hi⟩
  rcases hgh (ε / 2) (half_pos hε) with ⟨j, hj⟩
  refine ⟨max i j, ?_⟩
  intro k hk
  have h1 : abs (f k - g k) < ε / 2 := by
    simpa using hi k (le_trans (le_max_left i j) hk)
  have h2 : abs (g k - h k) < ε / 2 := by
    simpa using hj k (le_trans (le_max_right i j) hk)
  calc
    abs (f k - h k) = abs ((f k - g k) + (g k - h k)) := by ring_nf
    _ ≤ abs (f k - g k) + abs (g k - h k) := abs_add_le _ _
    _ < ε := by linarith

/-- 商构造的核心判等：两个柯西序列给同一实数 ⟺ 它们之差趋于 0。
  `Real.ofCauchy` 把有理柯西序列挂进 ℝ，`CauSeq.Completion.mk` 是到商的投影。
@isnad1 id=iff.0h2v.s7.9a94e04aedf0 from=translated src=- shape=9e329330 vocab=d0edca12
-/
theorem real_eq_iff_cau_equiv {f g : CauSeq ℚ (abs : ℚ → ℚ)} :
    Real.ofCauchy (CauSeq.Completion.mk f) = Real.ofCauchy (CauSeq.Completion.mk g)
      ↔ CauSeq.LimZero (f - g) := by
  -- 思路：Real 的构造子是"把柯西商类装进壳"，它只在类层面判等（injEq）；
  -- 商层的判等（mk_eq）又恰好是"差趋于 0"，这正是 Cantor 判等准则。
  rw [Real.ofCauchy.injEq, CauSeq.Completion.mk_eq]

/-- 每个有理数给出一条常量柯西序列——Cantor 视角下"有理数⊂实数"。-/
def rat_const_cauchy (q : ℚ) : CauSeq ℚ (abs : ℚ → ℚ) :=
  CauSeq.const (abv := (abs : ℚ → ℚ)) q

end Analysis.Real

end SandronesLibrary

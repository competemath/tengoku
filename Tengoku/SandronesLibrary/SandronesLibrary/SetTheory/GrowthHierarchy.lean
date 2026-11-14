/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.Data.Nat.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / GrowthHierarchy —— 带基本列接口的增长层级近似

本文件不假定每个极限记号已经拥有某条“显然”的基本列。相反，零、后继和极限三种情形
连同极限处的基本列都属于记号系统的数据；`FundamentalSystem.Legal` 另外要求每一次递归
调用都沿指定关系下降。

为避免在尚未建立全域良基递归时过报结论，Hardy 层级和快速增长层级在这里定义为带显式
`fuel` 的可执行近似。燃料记录允许展开多少层记号；它不是序数本身。
-/

namespace SandronesLibrary.SetTheory.GrowthHierarchy

/-- 一个层级记号在递归定义中扮演的角色：零、某个记号的后继，或带基本列的极限。-/
inductive FundamentalStage (ι : Type*) where
  | zero
  | successor (previous : ι)
  | limit (sequence : ℕ → ι)

/--
增长层级所需的基本列接口。`below a b` 读作“`a` 是 `b` 的严格下级记号”；
`stage` 同时给出记号的类别以及后继前项或极限基本列。-/
structure FundamentalSystem (ι : Type*) where
  below : ι → ι → Prop
  stage : ι → FundamentalStage ι

/--
接口的合法性边界：后继必须回到严格较小的前项，极限基本列的每一项也必须严格低于极限。
这里只检查递归调用的局部下降；全域良基性和基本列的单调、共尾性质是更强的后续接口。-/
def FundamentalSystem.Legal (system : FundamentalSystem ι) : Prop :=
  ∀ a, match system.stage a with
    | .zero => True
    | .successor previous => system.below previous a
    | .limit sequence => ∀ n, system.below (sequence n) a

/-- 对函数做有限次迭代：零次不改变输入，后继次先做已有迭代，再应用一次函数。-/
def iterate (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | times + 1, n => f (iterate f times n)

/--
Hardy 层级的燃料近似。零层返回输入；后继层把输入加一后交给前项；极限层在输入 `n`
处选择基本列第 `n` 项。燃料耗尽时停止展开并返回当前输入。-/
def hardyApprox (system : FundamentalSystem ι) : ℕ → ι → ℕ → ℕ
  | 0, _, n => n
  | fuel + 1, a, n =>
      match system.stage a with
      | .zero => n
      | .successor previous => hardyApprox system fuel previous (n + 1)
      | .limit sequence => hardyApprox system fuel (sequence n) n

/--
> **Entry**: settheory.googology.fundamental-sequence-system
> **一句话**: 增长层级的记号必须显式说明零、后继和极限，并在极限处提供可检查的基本列。
> **依赖**: 无
> **mathlib**: 无（本库显式接口）-/
theorem fundamentalSystem_legal_rules (system : FundamentalSystem ι)
    (legal : system.Legal) (a : ι) :
    match system.stage a with
    | .zero => True
    | .successor previous => system.below previous a
    | .limit sequence => ∀ n, system.below (sequence n) a := by
  exact legal a

/--
> **Entry**: settheory.googology.hardy-hierarchy
> **一句话**: Hardy 层级近似按零、后继、极限三类记号计算，极限步由基本列选择下标。
> **依赖**: `settheory.googology.fundamental-sequence-system`
> **mathlib**: 无（本库显式递归）-/
theorem hardyApprox_rules (system : FundamentalSystem ι) (fuel n : ℕ) :
    (∀ a, system.stage a = .zero → hardyApprox system (fuel + 1) a n = n) ∧
    (∀ a previous, system.stage a = .successor previous →
      hardyApprox system (fuel + 1) a n = hardyApprox system fuel previous (n + 1)) ∧
    (∀ a sequence, system.stage a = .limit sequence →
      hardyApprox system (fuel + 1) a n = hardyApprox system fuel (sequence n) n) := by
  constructor
  · intro a h
    simp [hardyApprox, h]
  constructor
  · intro a previous h
    simp [hardyApprox, h]
  · intro a sequence h
    simp [hardyApprox, h]

/--
快速增长层级的燃料近似。零层是后继函数；后继层把前一级函数迭代 `n+1` 次；
极限层同样在输入 `n` 处选择基本列第 `n` 项。-/
def fastGrowingApprox (system : FundamentalSystem ι) : ℕ → ι → ℕ → ℕ
  | 0, _, n => n
  | fuel + 1, a, n =>
      match system.stage a with
      | .zero => n + 1
      | .successor previous =>
          iterate (fun x => fastGrowingApprox system fuel previous x) (n + 1) n
      | .limit sequence => fastGrowingApprox system fuel (sequence n) n

/--
> **Entry**: settheory.googology.fast-growing-hierarchy
> **一句话**: 快速增长层级近似在后继处迭代前一级函数，在极限处沿基本列下降。
> **依赖**: `settheory.googology.fundamental-sequence-system`
> **mathlib**: 无（本库显式递归）-/
theorem fastGrowingApprox_rules (system : FundamentalSystem ι) (fuel n : ℕ) :
    (∀ a, system.stage a = .zero → fastGrowingApprox system (fuel + 1) a n = n + 1) ∧
    (∀ a previous, system.stage a = .successor previous →
      fastGrowingApprox system (fuel + 1) a n =
        iterate (fun x => fastGrowingApprox system fuel previous x) (n + 1) n) ∧
    (∀ a sequence, system.stage a = .limit sequence →
      fastGrowingApprox system (fuel + 1) a n =
        fastGrowingApprox system fuel (sequence n) n) := by
  constructor
  · intro a h
    simp [fastGrowingApprox, h]
  constructor
  · intro a previous h
    simp [fastGrowingApprox, h]
  · intro a sequence h
    simp [fastGrowingApprox, h]

end SandronesLibrary.SetTheory.GrowthHierarchy

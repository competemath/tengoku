/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.FundamentalGroupTrivialityStandard
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.Circle
import Tengoku.Seed.Topology.Homotopy.Lifting
import Tengoku.Seed.Algebra.Group.Equiv.Opposite
import Tengoku.Seed.Algebra.Module.Torsion.Free

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 圆周基本群与绕数

本文件沿指数覆盖 `Circle.exp : ℝ → Circle` 建立教材中的圆周基本群计算：环路从零点提升到
实直线，其终点是唯一的 `2π` 整数倍；这个整数给出绕数同态。随后分别证明该同态单射和满射，
最终推出 `π₁(S¹, 1) ≃ Multiplicative ℤ`。最终等价不是对 Mathlib 通用覆盖空间等价的改名包装。

当前条目：

* `topology.fundamental-group.circle-standard`。
-/

open scoped unitInterval
open Set

namespace SandronesLibrary.Topology

noncomputable section

private def circleExpBasepoint : Circle.exp ⁻¹' ({1} : Set Circle) :=
  ⟨0, by simp⟩

private theorem circlePeriod_ne_zero : (2 * Real.pi : ℝ) ≠ 0 :=
  mul_ne_zero (by norm_num) Real.pi_ne_zero

/-- 指数覆盖的覆盖变换恰好是平移唯一的 `2π` 整数倍。

> **Entry**: topology.fundamental-group.circle-standard-/
def circleDeckIntEquiv : AddSubgroup.zmultiples (2 * Real.pi) ≃+ ℤ where
  toFun z := Classical.choose (AddSubgroup.mem_zmultiples_iff.mp z.property)
  invFun n := ⟨n • (2 * Real.pi), AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩⟩
  left_inv z := Subtype.ext (Classical.choose_spec
    (AddSubgroup.mem_zmultiples_iff.mp z.property))
  right_inv n := by
    apply smul_left_injective ℤ circlePeriod_ne_zero
    exact Classical.choose_spec
      (AddSubgroup.mem_zmultiples_iff.mp
        (show n • (2 * Real.pi) ∈ AddSubgroup.zmultiples (2 * Real.pi) by
          exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩))
  map_add' a b := by
    apply smul_left_injective ℤ circlePeriod_ne_zero
    change
      Classical.choose (AddSubgroup.mem_zmultiples_iff.mp (a + b).property) •
          (2 * Real.pi) =
        (Classical.choose (AddSubgroup.mem_zmultiples_iff.mp a.property) +
          Classical.choose (AddSubgroup.mem_zmultiples_iff.mp b.property)) •
            (2 * Real.pi)
    rw [Classical.choose_spec (AddSubgroup.mem_zmultiples_iff.mp (a + b).property)]
    simp only [add_smul]
    rw [Classical.choose_spec (AddSubgroup.mem_zmultiples_iff.mp a.property)]
    rw [Classical.choose_spec (AddSubgroup.mem_zmultiples_iff.mp b.property)]
    rfl

/-- 在 `circleDeckIntEquiv` 下，整数 `n` 精确对应平移量 `n • 2π`。
@isnad1 id=eq.0h1v.s8.30b982c1c21b from=translated src=- shape=9ac68cdb vocab=3c8c9a86
-/
theorem circleDeckIntEquiv_symm_apply_coe (n : ℤ) :
    ((circleDeckIntEquiv.symm n : AddSubgroup.zmultiples (2 * Real.pi)) : ℝ) =
      n • (2 * Real.pi) :=
  rfl

private def mulOppositeDeckEquivInt :
    (Multiplicative (AddSubgroup.zmultiples (2 * Real.pi)))ᵐᵒᵖ ≃* Multiplicative ℤ :=
  MulOpposite.opMulEquiv.symm.trans (AddEquiv.toMultiplicative circleDeckIntEquiv)

/-- 以零为初值，把带基点圆周环路沿 `Circle.exp` 提升到实直线。-/
def circleLoopLift (g : Path (1 : Circle) 1) : C(unitInterval, ℝ) :=
  Circle.isCoveringMap_exp.liftPath g 0 (by simp)

/-- 选定的圆周环路提升从零开始。
@isnad1 id=eq.0h1v.s6.fdb93527847a from=translated src=- shape=c1ebf479 vocab=61d36a9c
-/
theorem circleLoopLift_zero (g : Path (1 : Circle) 1) : circleLoopLift g 0 = 0 := by
  exact Circle.isCoveringMap_exp.liftPath_zero g 0 (by simp)

/-- 把选定提升逐点投影回 `Circle.exp`，得到原圆周环路。
@isnad1 id=eq.0h2v.s7.469cf5741d38 from=translated src=- shape=2a5fc5b3 vocab=9400c984
-/
theorem circleLoopLift_exp (g : Path (1 : Circle) 1) (t : unitInterval) :
    Circle.exp (circleLoopLift g t) = g t := by
  exact congr_fun (Circle.isCoveringMap_exp.liftPath_lifts g 0 (by simp)) t

/-- 绕数同态把带基点环路沿指数覆盖提升后到达的覆盖变换记录为整数。-/
def circleWindingHom : FundamentalGroup Circle 1 →* Multiplicative ℤ :=
  mulOppositeDeckEquivInt.toMonoidHom.comp
    (Circle.isAddQuotientCoveringMap_exp.fundamentalGroupToMulOpposite circleExpBasepoint)

/-- 具有相同绕数的两个带基点圆周环路类相等。
@isnad1 id=injectiv.0h0v.s8.a87f8a3c3bce from=translated src=- shape=f3b7ffe4 vocab=3e493c9e
-/
theorem circleWindingHom_injective : Function.Injective circleWindingHom := by
  exact mulOppositeDeckEquivInt.injective.comp
    (Circle.isAddQuotientCoveringMap_exp.fundamentalGroupToMulOpposite_injective
      circleExpBasepoint)

/-- 每个整数都能成为某个带基点圆周环路的绕数。
@isnad1 id=surjecti.0h0v.s8.911ebb9db7af from=translated src=- shape=f3b7ffe4 vocab=a3ea1f1c
-/
theorem circleWindingHom_surjective : Function.Surjective circleWindingHom := by
  exact mulOppositeDeckEquivInt.surjective.comp
    (Circle.isAddQuotientCoveringMap_exp.fundamentalGroupToMulOpposite_surjective
      circleExpBasepoint)

/-- 圆周基本群是无限循环群。这个等价由公开绕数同态及分别证明的单射、满射性质构造。-/
def circleFundamentalGroupEquivInt : FundamentalGroup Circle 1 ≃* Multiplicative ℤ :=
  MulEquiv.ofBijective circleWindingHom
    ⟨circleWindingHom_injective, circleWindingHom_surjective⟩

end

end SandronesLibrary.Topology

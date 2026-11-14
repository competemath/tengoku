/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.FundamentalGroupCarrierStandard

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 基本群的运算与群律

本文件解释基本群的单位、乘法和逆元怎样落实为道路同伦商上的恒等道路、拼接和反向，并说明
Mathlib 因范畴复合约定而采用的拼接次序。群律直接由标准 `Group` 实例提供。

当前条目：

* `topology.fundamental-group.operations-standard`。
-/

namespace SandronesLibrary.Topology

universe u

variable {X : Type u} [TopologicalSpace X] {x : X}

/-- 基本群的单位元在道路同伦商视角中就是基点处恒等道路的同伦类。

> **Entry**: topology.fundamental-group.operations-standard
@isnad1 id=eq.0h2v.s5.43b5687bec16 from=translated src=- shape=182cacf8 vocab=772a1984
-/
theorem fundamentalGroup_one_toPath :
    FundamentalGroup.toPath (1 : FundamentalGroup X x) =
      Path.Homotopic.Quotient.refl x :=
  rfl

/-- Mathlib 的乘法来自自同态的范畴复合，因此 `p * q` 对应先走 `q`、再走 `p`。

等式发生在道路同伦商上；它没有断言原始 `Path` 的拼接满足严格群律。
@isnad1 id=eq.0h4v.s6.783a8823eb05 from=translated src=- shape=22903302 vocab=3eedcb85
-/
theorem fundamentalGroup_mul_toPath (p q : FundamentalGroup X x) :
    FundamentalGroup.toPath (p * q) =
      (FundamentalGroup.toPath q).trans (FundamentalGroup.toPath p) :=
  rfl

/-- 基本群中的逆元在道路同伦商视角中由道路反向给出。
@isnad1 id=eq.0h3v.s6.37847dcee59a from=translated src=- shape=b6d68cdf vocab=846c368c
-/
theorem fundamentalGroup_inv_toPath (p : FundamentalGroup X x) :
    FundamentalGroup.toPath p⁻¹ = (FundamentalGroup.toPath p).symm :=
  rfl

/-- 对具体代表道路，基本群乘法仍按范畴复合的次序对应于“先 `q`、再 `p`”的拼接类。

两边都是基本群元素；右边先把拼接道路送进同伦商，所以这不是原始道路的严格等式。
@isnad1 id=eq.0h4v.s6.48edcfe42b9c from=translated src=- shape=50492d49 vocab=c035cb09
-/
theorem fundamentalGroup_mk_mul_mk (p q : Path x x) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) *
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (q.trans p)) :=
  rfl

end SandronesLibrary.Topology

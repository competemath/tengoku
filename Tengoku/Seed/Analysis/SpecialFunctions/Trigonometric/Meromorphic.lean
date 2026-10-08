/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Meromorphic.Basic
public import Tengoku.Seed.Analysis.Meromorphic.NormalForm
public import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Meromorphicity of `Complex.tan` and `Complex.tanh`
-/

public section

namespace Complex

/-- The function `tan` is meromorphic in normal form on `Set.univ`.
@isnad1 id=meromorp.0h0v.s4.56e417168765 from=seed src=0 shape=a94d82b8 vocab=06f931b0
-/
theorem meromorphicNFOn_tan : MeromorphicNFOn tan Set.univ := by
  intro x _
  refine MeromorphicNFOn.div analyticAt_sin analyticAt_cos.meromorphicNFAt ?_
  grind [sin_sq_add_cos_sq]

/-- The function `tan` is meromorphic at any `z`.
@isnad1 id=meromorp.0h1v.s4.2ea93383feaa from=seed src=0 shape=54444e7e vocab=7a21b190
-/
@[fun_prop]
theorem meromorphicAt_tan (z : ℂ) : MeromorphicAt tan z :=
  (meromorphicNFOn_tan (Set.mem_univ z)).meromorphicAt

/-- The function `tan` is meromorphic.
@isnad1 id=meromorp.0h0v.s3.c85f9fd4a7a9 from=seed src=0 shape=e3d48bcb vocab=3e36f9d0
-/
@[fun_prop]
theorem meromorphic_tan : Meromorphic tan := meromorphicAt_tan

/-- The function `tanh` is meromorphic in normal form on `Set.univ`.
@isnad1 id=meromorp.0h0v.s4.72e2232c8cf2 from=seed src=0 shape=a94d82b8 vocab=88ee232e
-/
theorem meromorphicNFOn_tanh : MeromorphicNFOn tanh Set.univ := by
  intro x _
  refine MeromorphicNFOn.div analyticAt_sinh analyticAt_cosh.meromorphicNFAt ?_
  grind [cosh_sq_sub_sinh_sq]

/-- The function `tanh` is meromorphic at any `z`.
@isnad1 id=meromorp.0h1v.s4.2f39f163f8f7 from=seed src=0 shape=54444e7e vocab=f73253b8
-/
@[fun_prop]
theorem meromorphicAt_tanh (z : ℂ) : MeromorphicAt tanh z :=
  (meromorphicNFOn_tanh (Set.mem_univ z)).meromorphicAt

/-- The function `tanh` is meromorphic.
@isnad1 id=meromorp.0h0v.s3.7aae78f30cf7 from=seed src=0 shape=e3d48bcb vocab=1604239b
-/
@[fun_prop]
theorem meromorphic_tanh : Meromorphic tanh := meromorphicAt_tanh

end Complex

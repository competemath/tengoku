/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basic
public import Tengoku

/-!
# Coordinate basis for native vectors

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This port retains the coordinate basis and reconstruction facts
needed to state coordinate weak derivatives, under the `CKN` namespace.
-/

@[expose] public section

namespace CKN

/-- The `i`th coordinate basis vector in the native ambient space. -/
def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)

/--
@isnad1 id=eq.0h3v.s5.bf76568c0403 from=translated src=- shape=6d7f2782 vocab=99c59f41
-/
@[simp]
theorem basisVec_apply {d : ℕ} (i j : Fin d) :
    basisVec i j = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h
    simp [basisVec]
  · simp [basisVec, h]

/-- Coordinate reconstruction in the native basis.
@isnad1 id=eq.0h2v.s5.4ae5f69076e4 from=translated src=- shape=750df225 vocab=11386458
-/
theorem sum_smul_basisVec {d : ℕ} (x : Vec d) :
    ∑ i : Fin d, x i • basisVec i = x := by
  funext j
  simp [basisVec_apply]

end CKN

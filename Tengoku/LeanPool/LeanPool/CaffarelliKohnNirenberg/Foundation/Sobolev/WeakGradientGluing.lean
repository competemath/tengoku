/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative
public import Tengoku

/-!
# Uniqueness of weak partial derivatives

Locally integrable weak partial derivatives of the same function on an open
set agree almost everywhere.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology BigOperators

noncomputable section

namespace CKN

/-- Locally integrable weak partial derivatives of the same function agree almost everywhere.
@isnad1 id=eventual.5h6v.s8.ba69d4fed6a7 from=translated src=- shape=6f201169 vocab=2c8d63a4
-/
theorem hasWeakPartialDerivOn_unique_ae {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {i : Fin d} {f g h : Vec d → ℝ}
    (hgLoc : LocallyIntegrableOn g U volume) (hhLoc : LocallyIntegrableOn h U volume)
    (hg : HasWeakPartialDerivOn U i f g) (hh : HasWeakPartialDerivOn U i f h) :
    g =ᵐ[volume.restrict U] h :=
  HasWeakPartialDerivOn.ae_eq hU hgLoc hhLoc hg hh

end CKN

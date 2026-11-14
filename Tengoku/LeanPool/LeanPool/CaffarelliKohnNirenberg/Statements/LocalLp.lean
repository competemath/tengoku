/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Tengoku

/-!
# Local Lp

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section
namespace Tengoku.LeanPool end Tengoku.LeanPool open Tengoku.LeanPool 
open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

namespace CKN

/-- Local scalar `Lp` membership used by paper label `def:sws`. -/
def localLp (E : Set ParabolicPoint) (p : ℝ) (g : ParabolicPoint → ℝ) : Prop :=
  MeasureTheory.MemLp g (ENNReal.ofReal p) (volume.restrict E)

end CKN
-- Tengoku: root names of this library moved to Tengoku.LeanPool so they do not collide with other libraries (generated)

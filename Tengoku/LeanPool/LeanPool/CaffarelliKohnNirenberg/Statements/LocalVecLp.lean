/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Statements.LocalLp

/-!
# Local Vec Lp

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section
namespace Tengoku.LeanPool end Tengoku.LeanPool open Tengoku.LeanPool 
open CKN.Foundation.Parabolic

namespace CKN

/-- Componentwise local vector `Lp` membership used by paper label `def:sws`. -/
def localVecLp (E : Set ParabolicPoint) (p : ℝ)
    (g : ParabolicPoint → Vec3) : Prop :=
  ∀ i : Fin 3, localLp E p (fun z => g z i)

end CKN
-- Tengoku: root names of this library moved to Tengoku.LeanPool so they do not collide with other libraries (generated)

module

public import Tengoku

/-!
# Functions Bounded at Infinity

Auxiliary lemmas about functions bounded at the cusps.
-/

@[expose] public section
namespace Tengoku.SpherePackingOrig end Tengoku.SpherePackingOrig open Tengoku.SpherePackingOrig 
open UpperHalfPlane

theorem _root_.Tengoku.SpherePackingOrig.isBoundedAtImInfty_neg_iff (f : ℍ → ℂ) :
    IsBoundedAtImInfty (-f) ↔ IsBoundedAtImInfty f := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, Pi.neg_apply, norm_neg]

-- The forward direction `IsBoundedAtImInfty.neg` is mathlib's `BoundedAtFilter.neg`; only the
-- `iff` above (used for `simp_rw`) has no mathlib counterpart, so it is kept.
-- Tengoku: root names of this library moved to Tengoku.SpherePackingOrig so they do not collide with other libraries (generated)

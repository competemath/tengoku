/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Calculus.FDeriv.Pi
public import Tengoku.Seed.Analysis.Calculus.Deriv.Basic

/-!
# One-dimensional derivatives on pi-types.
-/

public section

variable {𝕜 ι : Type*} [DecidableEq ι] [NontriviallyNormedField 𝕜]

/--
@isnad1 id=hasderiv.0h5v.s7.7ba620666494 from=seed src=0 shape=34eaf361 vocab=5a77b5e8
-/
theorem hasDerivAt_update (x : ι → 𝕜) (i : ι) (y : 𝕜) :
    HasDerivAt (Function.update x i) (Pi.single i (1 : 𝕜)) y := by
  convert! (hasFDerivAt_update x y).hasDerivAt
  ext z j
  rw [Pi.single, Function.update_apply]
  split_ifs with h
  · simp [h]
  · simp [Pi.single_eq_of_ne h]

/--
@isnad1 id=hasderiv.0h4v.s7.4023c756c145 from=seed src=0 shape=f9aba28c vocab=76015333
-/
theorem hasDerivAt_single (i : ι) (y : 𝕜) :
    HasDerivAt (Pi.single (M := fun _ ↦ 𝕜) i) (Pi.single i (1 : 𝕜)) y :=
  hasDerivAt_update 0 i y

variable [Finite ι]

/--
@isnad1 id=eq.0h5v.s7.6772228dd041 from=seed src=0 shape=0a194c8d vocab=219f01ee
-/
theorem deriv_update (x : ι → 𝕜) (i : ι) (y : 𝕜) :
    deriv (Function.update x i) y = Pi.single i (1 : 𝕜) :=
  have := Fintype.ofFinite ι
  (hasDerivAt_update x i y).deriv

/--
@isnad1 id=eq.0h4v.s7.1c47fc7cacbd from=seed src=0 shape=ee469823 vocab=d8ea2d55
-/
theorem deriv_single (i : ι) (y : 𝕜) :
    deriv (Pi.single (M := fun _ ↦ 𝕜) i) y = Pi.single i (1 : 𝕜) :=
  deriv_update 0 i y

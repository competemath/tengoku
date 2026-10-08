/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Calculus.FDeriv.Prod
public import Tengoku.Seed.Analysis.Calculus.FDeriv.Const

/-!
# Derivatives on pi-types.
-/

public section

variable {𝕜 ι : Type*} [DecidableEq ι] [NontriviallyNormedField 𝕜]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

/--
@isnad1 id=hasfderi.0h6v.s9.388a20e4c8d5 from=seed src=0 shape=0f0e74b5 vocab=ef5d7d54
-/
@[fun_prop]
theorem hasFDerivAt_update (x : ∀ i, E i) {i : ι} (y : E i) :
    HasFDerivAt (Function.update x i) (.pi (Pi.single i (.id 𝕜 (E i)))) y := by
  rw [hasFDerivAt_pi]
  intro j
  rcases eq_or_ne j i with rfl | hij
  · simpa using! hasFDerivAt_id _
  · simpa [hij] using! hasFDerivAt_const _ _

/--
@isnad1 id=hasfderi.0h5v.s9.3ccd977d6f1c from=seed src=0 shape=ba63b41b vocab=17d2b672
-/
@[fun_prop]
theorem hasFDerivAt_single {i : ι} (y : E i) :
    HasFDerivAt (Pi.single i) (.pi (Pi.single i (.id 𝕜 (E i)))) y :=
  hasFDerivAt_update 0 y

/--
@isnad1 id=eq.0h6v.s9.c67d63b7ae6e from=seed src=0 shape=ff823443 vocab=2d4c0671
-/
theorem fderiv_update (x : ∀ i, E i) {i : ι} (y : E i) :
    fderiv 𝕜 (Function.update x i) y = .pi (Pi.single i (.id 𝕜 (E i))) :=
  (hasFDerivAt_update x y).fderiv

/--
@isnad1 id=eq.0h5v.s9.31c1a7a03d1d from=seed src=0 shape=33f6e5fc vocab=e5e9b868
-/
theorem fderiv_single {i : ι} (y : E i) :
    fderiv 𝕜 (Pi.single i) y = .pi (Pi.single i (.id 𝕜 (E i))) :=
  fderiv_update 0 y

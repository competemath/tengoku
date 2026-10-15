/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Tengoku

/-! The existence of smooth bumps, separated from their construction. -/

@[expose] public section

/-- A finite-dimensional real normed space admits smooth bump functions.
This proof can be activated as an instance locally when defining cutoff data.
@isnad1 id=hascontd.0h1v.s5.e230e6f197f1 from=translated src=- shape=e367154d vocab=997156d9
-/
theorem FiniteDimensional.hasContDiffBump (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    HasContDiffBump E := by infer_instance

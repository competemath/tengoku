/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

namespace LeanPoolFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # AtImInfty -/

@[expose] public section

/-
Probably put this at Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean
-/

open UpperHalfPlane Filter Topology

/--
@isnad1 id=iff.0h1v.s4.d27800f01d08 from=translated src=- shape=51b82dae vocab=e7e6bf37
-/
lemma Filter.eventually_atImInfty {p : ℍ → Prop} :
    (∀ᶠ x in atImInfty, p x) ↔ ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im → p z :=
  atImInfty_mem (Set.ofPred p)

/--
@isnad1 id=tendsto.0h0v.s3.1ce7ad19a7be from=translated src=- shape=ee480663 vocab=1a49ad58
-/
lemma Filter.tendsto_im_atImInfty : Tendsto (fun x : ℍ ↦ x.im) atImInfty atTop :=
  tendsto_iff_comap.mpr fun ⦃_⦄ a => a

/-- If f tends to c ≠ 0 at infinity, then f ≠ 0 as a function.

This packages the common argument: if f = 0, then f → 0, but also f → c by hypothesis.
By uniqueness of limits, 0 = c, contradicting c ≠ 0.
@isnad1 id=ne.2h2v.s5.9e0fd112c062 from=translated src=- shape=6e87497d vocab=38341d69
-/
lemma ne_zero_of_tendsto_ne_zero {f : ℍ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hf : Tendsto f atImInfty (nhds c)) : f ≠ 0 := fun h =>
  hc (tendsto_nhds_unique tendsto_const_nhds (h ▸ hf)).symm

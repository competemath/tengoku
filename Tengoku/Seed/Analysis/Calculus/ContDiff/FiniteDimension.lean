/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Calculus.ContDiff.Operations
public import Tengoku.Seed.Analysis.Normed.Module.FiniteDimension

/-!
# Higher differentiability in finite dimensions.

-/

public section


noncomputable section

universe uD uE uF

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {D : Type uD} [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} {f : D → E} {s : Set D}

/-! ### Finite-dimensional results -/

section FiniteDimensional

open Function Module

open scoped ContDiff

variable [CompleteSpace 𝕜]

/-- A family of continuous linear maps is `C^n` at `x` within `s` if and only if all its
  applications are.
@isnad1 id=iff.0h8v.s9.82d7a2253613 from=seed src=0 shape=72357c19 vocab=08bc625b
-/
theorem contDiffWithinAt_clm_apply {f : D → E →L[𝕜] F} {s : Set D} {x : D} [FiniteDimensional 𝕜 E] :
    ContDiffWithinAt 𝕜 n f s x ↔ ∀ y, ContDiffWithinAt 𝕜 n (fun x ↦ f x y) s x := by
  refine ⟨fun h y => h.clm_apply contDiffWithinAt_const, fun h => ?_⟩
  let d := finrank 𝕜 E
  have hd : d = finrank 𝕜 (Fin d → 𝕜) := (finrank_fin_fun 𝕜).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.comp_contDiffWithinAt (contDiffWithinAt_pi.mpr fun i ↦ h _)

/-- A family of continuous linear maps is `C^n` on `s` if and only if all its applications are.
@isnad1 id=iff.0h7v.s9.3dd684a0c9da from=seed src=0 shape=b2a8f195 vocab=c153ffb8
-/
theorem contDiffOn_clm_apply {f : D → E →L[𝕜] F} {s : Set D} [FiniteDimensional 𝕜 E] :
    ContDiffOn 𝕜 n f s ↔ ∀ y, ContDiffOn 𝕜 n (fun x => f x y) s := by
  simp [ContDiffOn, contDiffWithinAt_clm_apply]
  tauto

/--
@isnad1 id=iff.0h6v.s9.ea5ceaf6b51e from=seed src=0 shape=ffa47db1 vocab=faba72f9
-/
theorem contDiff_clm_apply_iff {f : D → E →L[𝕜] F} [FiniteDimensional 𝕜 E] :
    ContDiff 𝕜 n f ↔ ∀ y, ContDiff 𝕜 n fun x => f x y := by
  simp_rw [← contDiffOn_univ, contDiffOn_clm_apply]

/-- This is a useful lemma to prove that a certain operation preserves functions being `C^n`.
When you do induction on `n`, this gives a useful characterization of a function being `C^(n+1)`,
assuming you have already computed the derivative. The advantage of this version over
`contDiff_succ_iff_fderiv` is that both occurrences of `ContDiff` are for functions with the same
domain and codomain (`D` and `E`). This is not the case for `contDiff_succ_iff_fderiv`, which
often requires an inconvenient need to generalize `F`, which results in universe issues
(see the discussion in the section of `ContDiff.comp`).

This lemma avoids these universe issues, but only applies for finite-dimensional `D`.
@isnad1 id=iff.0h5v.s8.fd0b1ee1a1fd from=seed src=0 shape=0913eecd vocab=6890c5a5
-/
theorem contDiff_succ_iff_fderiv_apply [FiniteDimensional 𝕜 D] :
    ContDiff 𝕜 (n + 1) f ↔ Differentiable 𝕜 f ∧
      (n = ω → AnalyticOnNhd 𝕜 f Set.univ) ∧ ∀ y, ContDiff 𝕜 n fun x => fderiv 𝕜 f x y := by
  rw [contDiff_succ_iff_fderiv, contDiff_clm_apply_iff]

/--
@isnad1 id=contdiff.3h6v.s8.ca0b3505d1c1 from=seed src=0 shape=2b447a56 vocab=7e63b32e
-/
theorem contDiffOn_succ_of_fderiv_apply [FiniteDimensional 𝕜 D]
    (hf : DifferentiableOn 𝕜 f s) (h'f : n = ω → AnalyticOn 𝕜 f s)
    (h : ∀ y, ContDiffOn 𝕜 n (fun x => fderivWithin 𝕜 f s x y) s) :
    ContDiffOn 𝕜 (n + 1) f s :=
  contDiffOn_succ_of_fderivWithin hf h'f <| contDiffOn_clm_apply.mpr h

/--
@isnad1 id=iff.1h6v.s8.ac2ab30358a0 from=seed src=0 shape=7574386d vocab=8628da64
-/
theorem contDiffOn_succ_iff_fderiv_apply [FiniteDimensional 𝕜 D] (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 (n + 1) f s ↔
      DifferentiableOn 𝕜 f s ∧ (n = ω → AnalyticOn 𝕜 f s) ∧
      ∀ y, ContDiffOn 𝕜 n (fun x => fderivWithin 𝕜 f s x y) s := by
  rw [contDiffOn_succ_iff_fderivWithin hs, contDiffOn_clm_apply]

end FiniteDimensional

/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Calculus.LocalExtr.Basic
public import Tengoku.Seed.Analysis.Calculus.LineDeriv.Basic

/-!
# Local extremum and line derivatives

If `f` has a local extremum at a point, then the derivative at this point is zero.
In this file we prove several versions of this fact for line derivatives.
-/

public section

open Function Set Filter
open scoped Topology

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → ℝ} {s : Set E} {a b : E} {f' : ℝ}

/--
@isnad1 id=eq.3h6v.s7.24d2b51195d2 from=seed src=0 shape=b8f03ea5 vocab=a1581050
-/
theorem IsExtrFilter.hasLineDerivAt_eq_zero {l : Filter E} (h : IsExtrFilter f l a)
    (hd : HasLineDerivAt ℝ f f' a b) (h' : Tendsto (fun t : ℝ ↦ a + t • b) (𝓝 0) l) : f' = 0 :=
  IsLocalExtr.hasDerivAt_eq_zero (IsExtrFilter.comp_tendsto (by simpa using h) h') hd

/--
@isnad1 id=eq.2h5v.s7.4a1b4d1d9b1c from=seed src=0 shape=4d6cb212 vocab=bf007861
-/
theorem IsExtrFilter.lineDeriv_eq_zero {l : Filter E} (h : IsExtrFilter f l a)
    (h' : Tendsto (fun t : ℝ ↦ a + t • b) (𝓝 0) l) : lineDeriv ℝ f a b = 0 := by
  classical
  exact if hd : LineDifferentiableAt ℝ f a b then
    h.hasLineDerivAt_eq_zero hd.hasLineDerivAt h'
  else
    lineDeriv_zero_of_not_lineDifferentiableAt hd

/--
@isnad1 id=eq.3h6v.s7.6f5fb4751d95 from=seed src=0 shape=ec0af3e4 vocab=c2c162e9
-/
theorem IsExtrOn.hasLineDerivAt_eq_zero (h : IsExtrOn f s a) (hd : HasLineDerivAt ℝ f f' a b)
    (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) : f' = 0 :=
  IsExtrFilter.hasLineDerivAt_eq_zero h hd <| tendsto_principal.2 h'

/--
@isnad1 id=eq.2h5v.s7.5a4fc0622d36 from=seed src=0 shape=978fe04f vocab=8ace9229
-/
theorem IsExtrOn.lineDeriv_eq_zero (h : IsExtrOn f s a) (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) :
    lineDeriv ℝ f a b = 0 :=
  IsExtrFilter.lineDeriv_eq_zero h <| tendsto_principal.2 h'

/--
@isnad1 id=eq.3h6v.s7.286c3c3f7102 from=seed src=0 shape=ec0af3e4 vocab=e89e8c5a
-/
theorem IsMinOn.hasLineDerivAt_eq_zero (h : IsMinOn f s a) (hd : HasLineDerivAt ℝ f f' a b)
    (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) : f' = 0 :=
  h.isExtr.hasLineDerivAt_eq_zero hd h'

/--
@isnad1 id=eq.2h5v.s7.c98100983bdf from=seed src=0 shape=978fe04f vocab=b4bf3195
-/
theorem IsMinOn.lineDeriv_eq_zero (h : IsMinOn f s a) (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) :
    lineDeriv ℝ f a b = 0 :=
  h.isExtr.lineDeriv_eq_zero h'

/--
@isnad1 id=eq.3h6v.s7.98579b93d46e from=seed src=0 shape=ec0af3e4 vocab=e2cad6ac
-/
theorem IsMaxOn.hasLineDerivAt_eq_zero (h : IsMaxOn f s a) (hd : HasLineDerivAt ℝ f f' a b)
    (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) : f' = 0 :=
  h.isExtr.hasLineDerivAt_eq_zero hd h'

/--
@isnad1 id=eq.2h5v.s7.1b3e64907c38 from=seed src=0 shape=978fe04f vocab=d9af07e6
-/
theorem IsMaxOn.lineDeriv_eq_zero (h : IsMaxOn f s a) (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) :
    lineDeriv ℝ f a b = 0 :=
  h.isExtr.lineDeriv_eq_zero h'

/--
@isnad1 id=eq.3h6v.s7.81d04024dd2c from=seed src=0 shape=4e8ce590 vocab=9168a220
-/
theorem IsExtrOn.hasLineDerivWithinAt_eq_zero (h : IsExtrOn f s a)
    (hd : HasLineDerivWithinAt ℝ f f' s a b) (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) : f' = 0 :=
  h.hasLineDerivAt_eq_zero (hd.hasLineDerivAt' h') h'

/--
@isnad1 id=eq.2h5v.s7.adb97f8df388 from=seed src=0 shape=561b4c3c vocab=e8705c5c
-/
theorem IsExtrOn.lineDerivWithin_eq_zero (h : IsExtrOn f s a)
    (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) : lineDerivWithin ℝ f s a b = 0 := by
  classical
  exact if hd : LineDifferentiableWithinAt ℝ f s a b then
    h.hasLineDerivWithinAt_eq_zero hd.hasLineDerivWithinAt h'
  else
    lineDerivWithin_zero_of_not_lineDifferentiableWithinAt hd

/--
@isnad1 id=eq.3h6v.s7.156d2bacb6c5 from=seed src=0 shape=4e8ce590 vocab=fd344770
-/
theorem IsMinOn.hasLineDerivWithinAt_eq_zero (h : IsMinOn f s a)
    (hd : HasLineDerivWithinAt ℝ f f' s a b) (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) : f' = 0 :=
  h.isExtr.hasLineDerivWithinAt_eq_zero hd h'

/--
@isnad1 id=eq.2h5v.s7.563d28341577 from=seed src=0 shape=561b4c3c vocab=931920fd
-/
theorem IsMinOn.lineDerivWithin_eq_zero (h : IsMinOn f s a)
    (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) : lineDerivWithin ℝ f s a b = 0 :=
  h.isExtr.lineDerivWithin_eq_zero h'

/--
@isnad1 id=eq.3h6v.s7.79eb64e6667b from=seed src=0 shape=4e8ce590 vocab=fffac44f
-/
theorem IsMaxOn.hasLineDerivWithinAt_eq_zero (h : IsMaxOn f s a)
    (hd : HasLineDerivWithinAt ℝ f f' s a b) (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) : f' = 0 :=
  h.isExtr.hasLineDerivWithinAt_eq_zero hd h'

/--
@isnad1 id=eq.2h5v.s7.f8369373a5ce from=seed src=0 shape=561b4c3c vocab=357f3fbd
-/
theorem IsMaxOn.lineDerivWithin_eq_zero (h : IsMaxOn f s a)
    (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) : lineDerivWithin ℝ f s a b = 0 :=
  h.isExtr.lineDerivWithin_eq_zero h'
end Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
  {f : E → ℝ} {a b : E} {f' : ℝ}

/--
@isnad1 id=eq.2h5v.s7.43fbf4751c11 from=seed src=0 shape=aa1c0069 vocab=968008c5
-/
theorem IsLocalExtr.hasLineDerivAt_eq_zero (h : IsLocalExtr f a) (hd : HasLineDerivAt ℝ f f' a b) :
    f' = 0 :=
  IsExtrFilter.hasLineDerivAt_eq_zero h hd <| Continuous.tendsto' (by fun_prop) _ _ (by simp)

/--
@isnad1 id=eq.1h3v.s7.768ab7912b7b from=seed src=0 shape=9f9bbf2d vocab=f8acceb3
-/
theorem IsLocalExtr.lineDeriv_eq_zero (h : IsLocalExtr f a) : lineDeriv ℝ f a = 0 :=
  funext fun b ↦ IsExtrFilter.lineDeriv_eq_zero h <| Continuous.tendsto' (by fun_prop) _ _ (by simp)

/--
@isnad1 id=eq.2h5v.s7.66b211e98b80 from=seed src=0 shape=aa1c0069 vocab=adb1143f
-/
theorem IsLocalMin.hasLineDerivAt_eq_zero (h : IsLocalMin f a) (hd : HasLineDerivAt ℝ f f' a b) :
    f' = 0 :=
  IsLocalExtr.hasLineDerivAt_eq_zero (.inl h) hd

/--
@isnad1 id=eq.1h3v.s7.1cb2c8f8de93 from=seed src=0 shape=9f9bbf2d vocab=41770f43
-/
theorem IsLocalMin.lineDeriv_eq_zero (h : IsLocalMin f a) : lineDeriv ℝ f a = 0 :=
  IsLocalExtr.lineDeriv_eq_zero (.inl h)

/--
@isnad1 id=eq.2h5v.s7.df6f5cf99d12 from=seed src=0 shape=aa1c0069 vocab=0e3f3b38
-/
theorem IsLocalMax.hasLineDerivAt_eq_zero (h : IsLocalMax f a) (hd : HasLineDerivAt ℝ f f' a b) :
    f' = 0 :=
  IsLocalExtr.hasLineDerivAt_eq_zero (.inr h) hd

/--
@isnad1 id=eq.1h3v.s7.2a502aaef01a from=seed src=0 shape=9f9bbf2d vocab=6438841c
-/
theorem IsLocalMax.lineDeriv_eq_zero (h : IsLocalMax f a) : lineDeriv ℝ f a = 0 :=
  IsLocalExtr.lineDeriv_eq_zero (.inr h)

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Defs/Profile.lean — a concrete taper profile.
The paper: "Fix once and for all a nondecreasing function ϱ ∈ C³(ℝ) with ϱ = 0 on (−∞,0] and ϱ = 1 on
[1,∞)" [subsec:family]. Mathlib's Real.smoothTransition is such a function (even C^∞), so the
headline theorems need not quantify over ϱ.
-/
import Tengoku.FormalMath.Zeta23.Defs
import Tengoku

noncomputable section

namespace Zeta23

/-- Real.smoothTransition is a taper profile in the paper's sense.
@isnad1 id=taperpro.0h0v.s1.189d49fbdb52 from=translated src=- shape=49959d42 vocab=953ce011
-/
theorem taperProfile_smoothTransition : TaperProfile Real.smoothTransition where
  contDiff := Real.smoothTransition.contDiff
  monotone := Real.smoothTransition.monotone
  eq_zero := fun _ hx => Real.smoothTransition.zero_of_nonpos hx
  eq_one := fun _ hx => Real.smoothTransition.one_of_one_le hx

/-- The canonical profile used for the headline theorems. -/
def stdProfile : ℝ → ℝ := Real.smoothTransition

/--
@isnad1 id=taperpro.0h0v.s1.00dcb845978d from=translated src=- shape=49959d42 vocab=fec4c229
-/
theorem taperProfile_stdProfile : TaperProfile stdProfile := taperProfile_smoothTransition

/-- "such a ϱ exists".
@isnad1 id=ex.0h0v.s3.e59a3cbd74b5 from=translated src=- shape=ebd786ab vocab=79e1fd8a
-/
theorem exists_taperProfile : ∃ ϱ : ℝ → ℝ, TaperProfile ϱ := ⟨_, taperProfile_smoothTransition⟩

end Zeta23

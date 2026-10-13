/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
  Part of the Zeta23 formalization of the paper
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/
import Tengoku.FormalMath.Zeta23.PrimeSideA.Basic
import Tengoku.FormalMath.Zeta23.PrimeSideTemp

/-!
# The concrete prime-side data as an instance of the abstract layer
Small, dependency-light file (imports only `PrimeSideA.Basic` and `PrimeSideTemp`):

* `Params.toSetting P T = ⟨T, λ, w⟩`, `Params.localFun P T = ⟨φ̂|_ℝ, Φ|_ℝ, A_φ, g, a, b⟩(T)` and the
  `rfl` bridges (`trGtA (P.toSetting T) (P.localFun T) = P.trGtilde T`, …);
* `PrimeSide.LocalHypsEventually cϱ P` — "the taper facts `LocalHyps` hold for the concrete data for
  all large `T`" (proved in `Zeta23/PrimeSideA/Bridge.lean`);
* `PrimeSide.evBound_of_eventuallyAt` — an `EventuallyAt`-form result specialised to the concrete
  data is an `EvBound` in `T`.
-/

noncomputable section

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace Zeta23

namespace Params
variable (P : Params) (T : ℝ)

/-- The abstract-layer parameter triple `(T, λ, w)` (`PrimeSide.Setting`). -/
def toSetting : PrimeSide.Setting := ⟨T, P.lam, P.w⟩

/-- The concrete taper data at height `T` as an abstract `PrimeSide.LocalFun`:
`(φ̂|_ℝ, Φ|_ℝ, A_φ, g, a, b)` = `(P.phiHatR T, P.PhiR T, P.Aphi T, P.g T, P.a T, P.b T)`. -/
def localFun : PrimeSide.LocalFun := ⟨P.phiHatR T, P.PhiR T, P.Aphi T, P.g T, P.a T, P.b T⟩

/--
@isnad1 id=eq.0h2v.s3.a2cdd9c94d53 from=translated src=- shape=6021be03 vocab=6e08f170
-/
@[simp] lemma toSetting_T : (P.toSetting T).T = T := rfl
/--
@isnad1 id=eq.0h2v.s3.23dd4705ff97 from=translated src=- shape=130d24bb vocab=6b4e0f0c
-/
@[simp] lemma toSetting_lam : (P.toSetting T).lam = P.lam := rfl
/--
@isnad1 id=eq.0h2v.s3.07946f1663f3 from=translated src=- shape=130d24bb vocab=8fd9b6bf
-/
@[simp] lemma toSetting_w : (P.toSetting T).w = P.w := rfl
/--
@isnad1 id=eq.0h2v.s3.fb9039a80374 from=translated src=- shape=913a1e7f vocab=0c1ad05a
-/
@[simp] lemma toSetting_L : (P.toSetting T).L = P.L T := rfl
/--
@isnad1 id=eq.0h2v.s3.e7ede127727f from=translated src=- shape=913a1e7f vocab=fe322b8a
-/
@[simp] lemma toSetting_X : (P.toSetting T).X = P.X T := rfl
/--
@isnad1 id=eq.0h2v.s3.1223e1a8f65e from=translated src=- shape=6a4f4735 vocab=caa89661
-/
@[simp] lemma toSetting_l : (P.toSetting T).l = l T := rfl
/--
@isnad1 id=eq.0h2v.s3.99acb27fd74a from=translated src=- shape=6a4f4735 vocab=5b87b49b
-/
@[simp] lemma toSetting_ell1 : (P.toSetting T).ell1 = ell1 T := rfl
/--
@isnad1 id=eq.0h2v.s3.1c9dfd73d801 from=translated src=- shape=33e5716c vocab=e3b30417
-/
@[simp] lemma toSetting_d : (P.toSetting T).d = P.d T := rfl
/--
@isnad1 id=eq.0h3v.s4.e32a033e2bd0 from=translated src=- shape=75f90abc vocab=9ca238ac
-/
@[simp] lemma toSetting_tau (k : ℤ) : (P.toSetting T).tau k = P.tau T k := rfl
/--
@isnad1 id=eq.0h2v.s3.1e3913980eab from=translated src=- shape=913a1e7f vocab=d24aa91a
-/
@[simp] lemma localFun_a : (P.localFun T).a = P.a T := rfl
/--
@isnad1 id=eq.0h2v.s3.ddf4a152e7d7 from=translated src=- shape=913a1e7f vocab=708fe22c
-/
@[simp] lemma localFun_b : (P.localFun T).b = P.b T := rfl
/--
@isnad1 id=eq.0h2v.s3.375caafd5f24 from=translated src=- shape=6348335e vocab=bd9f46c0
-/
@[simp] lemma localFun_Phi : (P.localFun T).Phi = P.PhiR T := rfl
/--
@isnad1 id=eq.0h2v.s3.1d01d858acf3 from=translated src=- shape=6348335e vocab=f8195ffb
-/
@[simp] lemma localFun_g : (P.localFun T).g = P.g T := rfl
/--
@isnad1 id=eq.0h2v.s3.9247d7533121 from=translated src=- shape=6348335e vocab=5456be82
-/
@[simp] lemma localFun_phiHat : (P.localFun T).phiHat = P.phiHatR T := rfl

end Params

namespace PrimeSide

variable (P : Params) (T : ℝ)

/-- `GentryA` on the concrete data is `Params.Gentry` ([eq:Gdef], 2nd expression).
@isnad1 id=eq.0h4v.s4.28fe35ed1722 from=translated src=- shape=331b98ef vocab=dd3fb697
-/
lemma GentryA_concrete (k l : ℤ) : GentryA (P.toSetting T) (P.localFun T) k l = P.Gentry T k l := rfl

/-- `tr G̃` of the abstract layer on the concrete data is `Params.trGtilde`.
@isnad1 id=eq.0h2v.s4.b5efbffe0683 from=translated src=- shape=beedc6f6 vocab=6a77b519
-/
lemma trGtA_concrete : trGtA (P.toSetting T) (P.localFun T) = P.trGtilde T := rfl

/-- `tr G̃²` of the abstract layer on the concrete data is `Params.trGtildeSq`.
@isnad1 id=eq.0h2v.s4.02add4ab2cd2 from=translated src=- shape=beedc6f6 vocab=fe711fd8
-/
lemma trGt2A_concrete : trGt2A (P.toSetting T) (P.localFun T) = P.trGtildeSq T := rfl

/-- The taper facts `LocalHyps` hold for the concrete data for all large `T`
(proved in `Zeta23/PrimeSideA/Bridge.lean`; here a named hypothesis). -/
def LocalHypsEventually (cϱ : ℝ) (P : Params) : Prop :=
  ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → LocalHyps cϱ (P.toSetting T) (P.localFun T)

variable {P}

/-- Generic bridge: an `EventuallyAt`-form result of the abstract layer, specialised to the
concrete data, is an `EvBound` in `T` (given the local hypotheses eventually and an eventually
nonnegative majorant).
@isnad1 id=evbound.3h4v.s6.6f1c4cb43f70 from=translated src=- shape=fab25dda vocab=bb46062f
-/
lemma evBound_of_eventuallyAt {cϱ : ℝ} (hLoc : LocalHypsEventually cϱ P)
    {f g : Setting → LocalFun → ℝ}
    (h : ∃ C : ℝ, EventuallyAt cϱ P.lam (fun p F => |f p F| ≤ C * g p F))
    (hg : ∀ᶠ T in atTop, 0 ≤ g (P.toSetting T) (P.localFun T)) :
    EvBound (fun T => f (P.toSetting T) (P.localFun T))
      (fun T => g (P.toSetting T) (P.localFun T)) := by
  obtain ⟨T₀, hT₀⟩ := hLoc
  obtain ⟨C, T₁, hT₁⟩ := h
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp hg
  refine ⟨max C 1, by positivity, max T₀ (max T₁ T₂), fun T hT => ?_⟩
  have h0 : T₀ ≤ T := (le_max_left _ _).trans hT
  have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  calc |f (P.toSetting T) (P.localFun T)| ≤ C * g (P.toSetting T) (P.localFun T) :=
        hT₁ _ _ rfl h1 (hT₀ T h0)
    _ ≤ max C 1 * g (P.toSetting T) (P.localFun T) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (hT₂ T h2)

end PrimeSide

end Zeta23

end

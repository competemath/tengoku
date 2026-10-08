/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# derivatives of the inverse trigonometric functions

Derivatives of `arcsin` and `arccos`.
-/

public section

noncomputable section

open scoped Topology Filter Real ContDiff
open Set

namespace Real

section Arcsin

/--
@isnad1 id=and.2h1v.s7.7f7cc13e29bf from=seed src=0 shape=f56d7d8f vocab=02b577d4
-/
theorem deriv_arcsin_aux {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
    HasStrictDerivAt arcsin (1 / √(1 - x ^ 2)) x ∧ ContDiffAt ℝ ω arcsin x := by
  rcases h₁.lt_or_gt with h₁ | h₁
  · have : 1 - x ^ 2 < 0 := by nlinarith [h₁]
    rw [sqrt_eq_zero'.2 this.le, div_zero]
    have : arcsin =ᶠ[𝓝 x] fun _ => -(π / 2) :=
      (gt_mem_nhds h₁).mono fun y hy => arcsin_of_le_neg_one hy.le
    exact ⟨(hasStrictDerivAt_const x _).congr_of_eventuallyEq this.symm,
      contDiffAt_const.congr_of_eventuallyEq this⟩
  rcases h₂.lt_or_gt with h₂ | h₂
  · have : 0 < √(1 - x ^ 2) := sqrt_pos.2 (by nlinarith [h₁, h₂])
    simp only [← cos_arcsin, one_div] at this ⊢
    exact ⟨sinPartialHomeomorph.hasStrictDerivAt_symm ⟨h₁, h₂⟩ this.ne' (hasStrictDerivAt_sin _),
      sinPartialHomeomorph.contDiffAt_symm_deriv this.ne' ⟨h₁, h₂⟩ (hasDerivAt_sin _)
        contDiff_sin.contDiffAt⟩
  · have : 1 - x ^ 2 < 0 := by nlinarith [h₂]
    rw [sqrt_eq_zero'.2 this.le, div_zero]
    have : arcsin =ᶠ[𝓝 x] fun _ => π / 2 := (lt_mem_nhds h₂).mono fun y hy => arcsin_of_one_le hy.le
    exact ⟨(hasStrictDerivAt_const x _).congr_of_eventuallyEq this.symm,
      contDiffAt_const.congr_of_eventuallyEq this⟩

/--
@isnad1 id=hasstric.2h1v.s6.39c9df14bb68 from=seed src=0 shape=95bb91cd vocab=617e9edf
-/
theorem hasStrictDerivAt_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
    HasStrictDerivAt arcsin (1 / √(1 - x ^ 2)) x :=
  (deriv_arcsin_aux h₁ h₂).1

/--
@isnad1 id=hasderiv.2h1v.s6.724d753d5f7e from=seed src=0 shape=95bb91cd vocab=553b966f
-/
theorem hasDerivAt_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
    HasDerivAt arcsin (1 / √(1 - x ^ 2)) x :=
  (hasStrictDerivAt_arcsin h₁ h₂).hasDerivAt

/--
@isnad1 id=contdiff.2h2v.s5.d452e0cb66b1 from=seed src=0 shape=e176f600 vocab=f2b963a9
-/
theorem contDiffAt_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) {n : ℕ∞ω} :
    ContDiffAt ℝ n arcsin x :=
  (deriv_arcsin_aux h₁ h₂).2.of_le le_top

/--
@isnad1 id=hasderiv.1h1v.s6.a1032a87965e from=seed src=0 shape=bcbc84fa vocab=44e670a2
-/
theorem hasDerivWithinAt_arcsin_Ici {x : ℝ} (h : x ≠ -1) :
    HasDerivWithinAt arcsin (1 / √(1 - x ^ 2)) (Ici x) x := by
  rcases eq_or_ne x 1 with (rfl | h')
  · convert! (hasDerivWithinAt_const (1 : ℝ) _ (π / 2)).congr _ _ <;>
      simp +contextual [arcsin_of_one_le]
  · exact (hasDerivAt_arcsin h h').hasDerivWithinAt

/--
@isnad1 id=hasderiv.1h1v.s6.40b31fc878b2 from=seed src=0 shape=c70c4745 vocab=1cc05968
-/
theorem hasDerivWithinAt_arcsin_Iic {x : ℝ} (h : x ≠ 1) :
    HasDerivWithinAt arcsin (1 / √(1 - x ^ 2)) (Iic x) x := by
  rcases em (x = -1) with (rfl | h')
  · convert! (hasDerivWithinAt_const (-1 : ℝ) _ (-(π / 2))).congr _ _ <;>
      simp +contextual [arcsin_of_le_neg_one]
  · exact (hasDerivAt_arcsin h' h).hasDerivWithinAt

/--
@isnad1 id=iff.0h1v.s6.e87649d337b2 from=seed src=0 shape=413e9f0f vocab=2ff905a6
-/
theorem differentiableWithinAt_arcsin_Ici {x : ℝ} :
    DifferentiableWithinAt ℝ arcsin (Ici x) x ↔ x ≠ -1 := by
  refine ⟨?_, fun h => (hasDerivWithinAt_arcsin_Ici h).differentiableWithinAt⟩
  rintro h rfl
  have : sin ∘ arcsin =ᶠ[𝓝[≥] (-1 : ℝ)] id := by
    filter_upwards [Icc_mem_nhdsGE (neg_lt_self zero_lt_one)] with x using sin_arcsin'
  have := h.hasDerivWithinAt.sin.congr_of_eventuallyEq this.symm (by simp)
  simpa using (uniqueDiffOn_Ici _ _ self_mem_Ici).eq_deriv _ this (hasDerivWithinAt_id _ _)

/--
@isnad1 id=iff.0h1v.s6.202dedf941c4 from=seed src=0 shape=4ce275f3 vocab=c78f4b0f
-/
theorem differentiableWithinAt_arcsin_Iic {x : ℝ} :
    DifferentiableWithinAt ℝ arcsin (Iic x) x ↔ x ≠ 1 := by
  refine ⟨fun h => ?_, fun h => (hasDerivWithinAt_arcsin_Iic h).differentiableWithinAt⟩
  rw [← neg_neg x, ← image_neg_Ici] at h
  have := (h.comp (-x) differentiableWithinAt_id.fun_neg (mapsTo_image _ _)).fun_neg
  simpa [(· ∘ ·), differentiableWithinAt_arcsin_Ici] using this

/--
@isnad1 id=iff.0h1v.s6.22363e6843d4 from=seed src=0 shape=39c36ef0 vocab=a9213e69
-/
theorem differentiableAt_arcsin {x : ℝ} : DifferentiableAt ℝ arcsin x ↔ x ≠ -1 ∧ x ≠ 1 :=
  ⟨fun h => ⟨differentiableWithinAt_arcsin_Ici.1 h.differentiableWithinAt,
      differentiableWithinAt_arcsin_Iic.1 h.differentiableWithinAt⟩,
    fun h => (hasDerivAt_arcsin h.1 h.2).differentiableAt⟩

/--
@isnad1 id=eq.0h0v.s6.d2af949ec77c from=seed src=0 shape=7ac580c2 vocab=050c54e3
-/
@[simp]
theorem deriv_arcsin : deriv arcsin = fun x => 1 / √(1 - x ^ 2) := by
  funext x
  by_cases h : x ≠ -1 ∧ x ≠ 1
  · exact (hasDerivAt_arcsin h.1 h.2).deriv
  · rw [deriv_zero_of_not_differentiableAt (mt differentiableAt_arcsin.1 h)]
    simp only [not_and_or, Ne, Classical.not_not] at h
    rcases h with (rfl | rfl) <;> simp

/--
@isnad1 id=differen.0h0v.s6.78d9e7191fd5 from=seed src=0 shape=6feed8e0 vocab=6229732c
-/
theorem differentiableOn_arcsin : DifferentiableOn ℝ arcsin {-1, 1}ᶜ := fun _x hx =>
  (differentiableAt_arcsin.2
      ⟨fun h => hx (Or.inl h), fun h => hx (Or.inr h)⟩).differentiableWithinAt

/--
@isnad1 id=contdiff.0h1v.s5.a7413385abbb from=seed src=0 shape=bbb0a061 vocab=583f61bb
-/
theorem contDiffOn_arcsin {n : ℕ∞ω} : ContDiffOn ℝ n arcsin {-1, 1}ᶜ := fun _x hx =>
  (contDiffAt_arcsin (mt Or.inl hx) (mt Or.inr hx)).contDiffWithinAt

/--
@isnad1 id=iff.0h2v.s6.f6fcb5511cc4 from=seed src=0 shape=43c947d1 vocab=f2b963a9
-/
theorem contDiffAt_arcsin_iff {x : ℝ} {n : ℕ∞ω} :
    ContDiffAt ℝ n arcsin x ↔ n = 0 ∨ x ≠ -1 ∧ x ≠ 1 :=
  ⟨fun h => or_iff_not_imp_left.2 fun hn => differentiableAt_arcsin.1 <| h.differentiableAt hn,
    fun h => h.elim (fun hn => hn.symm ▸ (contDiff_zero.2 continuous_arcsin).contDiffAt) fun hx =>
      contDiffAt_arcsin hx.1 hx.2⟩

end Arcsin

section Arccos

/--
@isnad1 id=hasstric.2h1v.s6.52c127a22080 from=seed src=0 shape=60ecba4e vocab=4eeac2cd
-/
theorem hasStrictDerivAt_arccos {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
    HasStrictDerivAt arccos (-(1 / √(1 - x ^ 2))) x :=
  (hasStrictDerivAt_arcsin h₁ h₂).const_sub (π / 2)

/--
@isnad1 id=hasderiv.2h1v.s6.7fc32853ab4c from=seed src=0 shape=60ecba4e vocab=11a75915
-/
theorem hasDerivAt_arccos {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
    HasDerivAt arccos (-(1 / √(1 - x ^ 2))) x :=
  (hasDerivAt_arcsin h₁ h₂).const_sub (π / 2)

/--
@isnad1 id=contdiff.2h2v.s5.38e6bf4d752f from=seed src=0 shape=e176f600 vocab=df4b9bcd
-/
theorem contDiffAt_arccos {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) {n : ℕ∞ω} :
    ContDiffAt ℝ n arccos x :=
  contDiffAt_const.sub (contDiffAt_arcsin h₁ h₂)

/--
@isnad1 id=hasderiv.1h1v.s6.abbb17dc289c from=seed src=0 shape=084dfb14 vocab=915d8f03
-/
theorem hasDerivWithinAt_arccos_Ici {x : ℝ} (h : x ≠ -1) :
    HasDerivWithinAt arccos (-(1 / √(1 - x ^ 2))) (Ici x) x :=
  (hasDerivWithinAt_arcsin_Ici h).const_sub _

/--
@isnad1 id=hasderiv.1h1v.s6.e3e3c830b5d3 from=seed src=0 shape=87ee57db vocab=838e36ef
-/
theorem hasDerivWithinAt_arccos_Iic {x : ℝ} (h : x ≠ 1) :
    HasDerivWithinAt arccos (-(1 / √(1 - x ^ 2))) (Iic x) x :=
  (hasDerivWithinAt_arcsin_Iic h).const_sub _

/--
@isnad1 id=iff.0h1v.s6.85992cacc5aa from=seed src=0 shape=413e9f0f vocab=df9ef390
-/
theorem differentiableWithinAt_arccos_Ici {x : ℝ} :
    DifferentiableWithinAt ℝ arccos (Ici x) x ↔ x ≠ -1 :=
  (differentiableWithinAt_const_sub_iff _).trans differentiableWithinAt_arcsin_Ici

/--
@isnad1 id=iff.0h1v.s6.6f9a687a07e4 from=seed src=0 shape=4ce275f3 vocab=6cfd8ff1
-/
theorem differentiableWithinAt_arccos_Iic {x : ℝ} :
    DifferentiableWithinAt ℝ arccos (Iic x) x ↔ x ≠ 1 :=
  (differentiableWithinAt_const_sub_iff _).trans differentiableWithinAt_arcsin_Iic

/--
@isnad1 id=iff.0h1v.s6.1ef7a3be02e1 from=seed src=0 shape=39c36ef0 vocab=e46b975b
-/
theorem differentiableAt_arccos {x : ℝ} : DifferentiableAt ℝ arccos x ↔ x ≠ -1 ∧ x ≠ 1 :=
  (differentiableAt_const _).sub_iff_right.trans differentiableAt_arcsin

/--
@isnad1 id=eq.0h0v.s6.aa6f5c8d3fe2 from=seed src=0 shape=d8ae4cf2 vocab=1c43782a
-/
@[simp]
theorem deriv_arccos : deriv arccos = fun x => -(1 / √(1 - x ^ 2)) :=
  funext fun x => (deriv_const_sub _).trans <| by simp only [deriv_arcsin]

/--
@isnad1 id=differen.0h0v.s6.6ad6eb1271b6 from=seed src=0 shape=6feed8e0 vocab=b724df8b
-/
theorem differentiableOn_arccos : DifferentiableOn ℝ arccos {-1, 1}ᶜ :=
  differentiableOn_arcsin.const_sub _

/--
@isnad1 id=contdiff.0h1v.s5.c5d0427c819f from=seed src=0 shape=bbb0a061 vocab=4b4a8ef4
-/
theorem contDiffOn_arccos {n : ℕ∞ω} : ContDiffOn ℝ n arccos {-1, 1}ᶜ :=
  contDiffOn_const.sub contDiffOn_arcsin

/--
@isnad1 id=iff.0h2v.s6.a6eadf656dde from=seed src=0 shape=43c947d1 vocab=df4b9bcd
-/
theorem contDiffAt_arccos_iff {x : ℝ} {n : ℕ∞ω} :
    ContDiffAt ℝ n arccos x ↔ n = 0 ∨ x ≠ -1 ∧ x ≠ 1 := by
  refine Iff.trans ⟨fun h => ?_, fun h => ?_⟩ contDiffAt_arcsin_iff <;>
    simpa [arccos] using! (contDiffAt_const (c := π / 2)).sub h

end Arccos

end Real

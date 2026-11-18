/-
Adapted from PrimeNumberTheoremAnd by Alex Kontorovich and contributors.
Licensed under the Apache License, Version 2.0; see the upstream LICENSE.
This compatibility port retains the proven declarations used by this project.
-/
import Tengoku.Seed.Analysis.Calculus.Deriv.Support
import Tengoku.Seed.Analysis.Calculus.IteratedDeriv.Lemmas
import Tengoku.Seed.Analysis.Distribution.SchwartzSpace.Deriv
import Tengoku.Seed.Order.Filter.ZeroAndBoundedAtFilter

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.QuasiRiemann end Tengoku.QuasiRiemann open Tengoku.QuasiRiemann
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

structure _root_.Tengoku.QuasiRiemann.CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where

  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun

/--
@isnad1 id=eq.1h4v.s5.a9d7d6717b33 from=translated src=- shape=aabd476f vocab=31109236
-/
@[ext] protected theorem Tengoku.QuasiRiemann.CS.ext {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {x y : CS n E}
    (h : x.toFun = y.toFun) : x = y := by
  cases x
  cases y
  cases h
  rfl

structure _root_.Tengoku.QuasiRiemann.trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1

structure _root_.Tengoku.QuasiRiemann.W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where

  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)

abbrev _root_.Tengoku.QuasiRiemann.W21 := W1 2 ℂ

section lemmas

noncomputable def _root_.Tengoku.QuasiRiemann.funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)

/--
@isnad1 id=contdiff.0h0v.s5.d5a82684315d from=translated src=- shape=352d7a74 vocab=68b11613
-/
theorem _root_.Tengoku.QuasiRiemann.contDiff_ofReal : ContDiff ℝ ∞ ofReal := Complex.ofRealCLM.contDiff

omit [NormedSpace ℝ E] in
/--
@isnad1 id=tendsto.1h3v.s6.fbc11d5d9cf2 from=translated src=- shape=9565e2a5 vocab=fdd32b5e
-/
theorem _root_.Tengoku.QuasiRiemann.tendsto_funscale {f : ℝ → E} (hf : ContinuousAt f 0) (x : ℝ) :
    Tendsto (fun R => funscale f R x) atTop (𝓝 (f 0)) :=
  hf.tendsto.comp (by simpa using tendsto_inv_atTop_zero.mul_const x)

end lemmas

namespace Tengoku.QuasiRiemann.CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun

instance : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨fun x => f x,
  contDiff_ofReal.of_le (mod_cast le_top) |>.comp f.h1, f.h2.comp_left (g := ofReal) rfl⟩

def neg (f : CS n E) : CS n E where
  toFun := -f
  h1 := f.h1.neg
  h2 := f.h2.neg

instance : Neg (CS n E) where neg := neg

/--
@isnad1 id=eq.0h4v.s6.1b8c7d046db4 from=translated src=- shape=c537fee1 vocab=816fa0bf
-/
@[simp] theorem neg_apply {x : ℝ} : (-f) x = - (f x) := rfl

def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.h1.const_smul R, f.h2.smul_left⟩

instance : HSMul ℝ (CS n E) (CS n E) where hSMul := smul

/--
@isnad1 id=eq.0h5v.s7.7de900bd7d89 from=translated src=- shape=e4a84f59 vocab=db10c538
-/
@[simp] theorem smul_apply : (R • f) x = R • f x := rfl

/--
@isnad1 id=continuo.0h3v.s5.1dcbdde3dbfa from=translated src=- shape=3f40b30e vocab=38bf46c6
-/
theorem continuous (f : CS n E) : Continuous f := f.h1.continuous

noncomputable def deriv (f : CS (n + 1) E) : CS n E where
  toFun := _root_.deriv f
  h1 := (contDiff_succ_iff_deriv.mp f.h1).2.2
  h2 := f.h2.deriv

/--
@isnad1 id=hasderiv.0h4v.s6.d8863cf4f19b from=translated src=- shape=42d98e5d vocab=7c90e743
-/
theorem hasDerivAt (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  (f.h1.differentiable (by simp)).differentiableAt.hasDerivAt

/--
@isnad1 id=eq.0h4v.s6.c895b2e0dd01 from=translated src=- shape=8cc87982 vocab=c6f8b7e6
-/
theorem deriv_apply {f : CS (n + 1) E} {x : ℝ} : f.deriv x = _root_.deriv f x := rfl

/--
@isnad1 id=eq.0h4v.s6.19f0450a5bdb from=translated src=- shape=c76897ae vocab=9af5c63d
-/
theorem deriv_smul {f : CS (n + 1) E} : (R • f).deriv = R • f.deriv := by
  ext x ; exact (f.hasDerivAt x |>.const_smul R).deriv

noncomputable def scale (g : CS n E) (R : ℝ) : CS n E := by
  by_cases h : R = 0
  · exact ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  · refine ⟨fun x => funscale g R x, ?_, ?_⟩
    · exact g.h1.comp (contDiff_const_smul R⁻¹)
    · exact g.h2.comp_smul (inv_ne_zero h)

/--
@isnad1 id=tendsto.0h4v.s6.6adae34dcad3 from=translated src=- shape=e3d97ada vocab=33096673
-/
theorem tendsto_scale (f : CS n E) (x : ℝ) : Tendsto (fun R => f.scale R x) atTop (𝓝 (f 0)) := by
  apply (tendsto_funscale f.continuous.continuousAt x).congr'
  filter_upwards [eventually_ne_atTop 0] with R hR ; simp [scale, hR]

/--
@isnad1 id=ex.0h3v.s5.30542b6b5f27 from=translated src=- shape=46d6fbbc vocab=a7caf33a
-/
theorem bounded : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  obtain ⟨x, hx⟩ :=
    (continuous_norm.comp f.continuous).exists_forall_ge_of_hasCompactSupport f.h2.norm
  exact ⟨_, hx⟩

end Tengoku.QuasiRiemann.CS

namespace Tengoku.QuasiRiemann.trunc

instance : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun

instance : Coe trunc (CS 2 ℝ) where coe := trunc.toCS

/--
@isnad1 id=le.0h2v.s5.489ccf486fda from=translated src=- shape=5c2fd3d2 vocab=08012e7a
-/
theorem nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)

/--
@isnad1 id=le.0h2v.s5.d23ab4810d4d from=translated src=- shape=9a11caa4 vocab=08012e7a
-/
theorem le_one (g : trunc) (x : ℝ) : g x ≤ 1 :=
  (g.h4 x).trans <| Set.indicator_le_self' (by simp) x

/--
@isnad1 id=eventual.0h1v.s5.1247f2973d4a from=translated src=- shape=9a1ad55d vocab=02730c61
-/
theorem zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))

/--
@isnad1 id=eq.0h1v.s5.a8b2c6e2da3e from=translated src=- shape=abb3ccc1 vocab=0f1226d9
-/
@[simp] theorem zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds

end Tengoku.QuasiRiemann.trunc

namespace Tengoku.QuasiRiemann.W1

instance : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun

/--
@isnad1 id=continuo.0h3v.s5.bbb269cb917c from=translated src=- shape=3f40b30e vocab=70e1aeb2
-/
theorem continuous (f : W1 n E) : Continuous f := f.smooth.continuous

/--
@isnad1 id=differen.0h3v.s6.83ee6b442f45 from=translated src=- shape=0f825776 vocab=3652f382
-/
theorem differentiable (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)

/--
@isnad1 id=eq.2h4v.s7.18a1be944b4f from=translated src=- shape=8522fc66 vocab=28de6984
-/
theorem iteratedDeriv_sub {f g : ℝ → E} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    iteratedDeriv n (f - g) = iteratedDeriv n f - iteratedDeriv n g := by
  funext x
  exact _root_.iteratedDeriv_sub hf.contDiffAt hg.contDiffAt

noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toFun := _root_.deriv f
  smooth := contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk := by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)

/--
@isnad1 id=hasderiv.0h4v.s6.a4fcdfa17cf8 from=translated src=- shape=42d98e5d vocab=a37add3e
-/
theorem hasDerivAt (f : W1 (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  f.differentiable.differentiableAt.hasDerivAt

def sub (f g : W1 n E) : W1 n E where
  toFun := f - g
  smooth := f.smooth.sub g.smooth
  integrable k hk := by
    have hf : ContDiff ℝ k f := f.smooth.of_le (by simp [hk])
    have hg : ContDiff ℝ k g := g.smooth.of_le (by simp [hk])
    simpa [iteratedDeriv_sub hf hg] using (f.integrable hk).sub (g.integrable hk)

instance : Sub (W1 n E) where sub := sub

/--
@isnad1 id=integrab.0h2v.s7.8abbcdfe9c58 from=translated src=- shape=b922e6e6 vocab=a0a73010
-/
theorem integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hd : (SchwartzMap.derivCLM ℝ ℂ f : ℝ → ℂ) = _root_.deriv f := by
      funext x
      exact SchwartzMap.derivCLM_apply ℝ f x
    rw [← hd]
    exact ih (f := SchwartzMap.derivCLM ℝ ℂ f)

noncomputable def ofSchwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := integrable_iteratedDeriv_Schwarz

end Tengoku.QuasiRiemann.W1

namespace Tengoku.QuasiRiemann.W21

variable {f : W21}

noncomputable def norm (f : ℝ → ℂ) : ℝ :=
    (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)

/--
@isnad1 id=le.0h1v.s3.0230498a4f64 from=translated src=- shape=e456648f vocab=83761510
-/
theorem norm_nonneg {f : ℝ → ℂ} : 0 ≤ norm f :=
  add_nonneg (integral_nonneg (fun t => by simp))
    (mul_nonneg (by positivity) (integral_nonneg (fun t => by simp)))

noncomputable instance : Norm W21 where norm := norm ∘ W1.toFun

noncomputable instance : Coe 𝓢(ℝ, ℂ) W21 where coe := W1.ofSchwartz

def ofCS2 (f : CS 2 ℂ) : W21 := by
  refine ⟨f, f.h1, ?_⟩
  intro k hk
  cases k with
  | zero => exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | succ k =>
    cases k with
    | zero =>
      simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
    | succ k =>
      have hk0 : k = 0 :=
        Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hk))
      subst k
      simpa [iteratedDeriv_succ] using
        (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv

instance : Coe (CS 2 ℂ) W21 where coe := ofCS2

instance : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where
  hMul g f := ⟨g * f, g.h1.mul f.smooth, g.h2.mul_right⟩

instance : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where hMul g f := (g : CS 2 ℂ) * f

/--
@isnad1 id=integrab.0h1v.s5.580f6c3ee5ff from=translated src=- shape=5a0c1598 vocab=0abfe7c3
-/
theorem hf (f : W21) : Integrable f := f.integrable zero_le_two

/--
@isnad1 id=integrab.0h1v.s6.0ea208052fe7 from=translated src=- shape=6c4dcfb3 vocab=b01e0cea
-/
theorem hf' (f : W21) : Integrable (deriv f) := by
  simpa [iteratedDeriv_succ] using f.integrable one_le_two

/--
@isnad1 id=integrab.0h1v.s7.98e5d121ee7c from=translated src=- shape=b36a2061 vocab=b01e0cea
-/
theorem hf'' (f : W21) : Integrable (deriv (deriv f))  := by
  simpa [iteratedDeriv_succ] using f.integrable le_rfl

end Tengoku.QuasiRiemann.W21
-- Tengoku: root names of this library moved to Tengoku.QuasiRiemann so they do not collide with other libraries (generated)

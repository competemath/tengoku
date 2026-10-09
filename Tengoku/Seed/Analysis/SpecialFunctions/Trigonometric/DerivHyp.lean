/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Order.Monotone.Odd
public import Tengoku.Seed.Analysis.Calculus.LogDeriv
public import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv
public import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Basic
public import Tengoku.Seed.Analysis.Calculus.Deriv.MeanValue

/-!
# Differentiability of hyperbolic trigonometric functions

## Main statements

The differentiability of the hyperbolic trigonometric functions is proved, and their derivatives are
computed.

## Tags

sinh, cosh, tanh
-/

public section

noncomputable section

open scoped Asymptotics Topology Filter
open Set

namespace Complex

/-- The complex hyperbolic sine function is everywhere strictly differentiable, with the derivative
`cosh x`.
@isnad1 id=hasstric.0h1v.s5.cbba648e9a3c from=seed src=0 shape=475e04ea vocab=45a27c8e
-/
theorem hasStrictDerivAt_sinh (x : ℂ) : HasStrictDerivAt sinh (cosh x) x := by
  simp only [cosh, div_eq_mul_inv]
  convert!
    ((hasStrictDerivAt_exp x).sub (hasStrictDerivAt_id x).fun_neg.cexp).mul_const (2 : ℂ)⁻¹ using 1
  rw [id, mul_neg_one, sub_eq_add_neg, neg_neg]

/-- The complex hyperbolic sine function is everywhere differentiable, with the derivative
`cosh x`.
@isnad1 id=hasderiv.0h1v.s5.2b3a9f46e431 from=seed src=0 shape=475e04ea vocab=7dcf5519
-/
theorem hasDerivAt_sinh (x : ℂ) : HasDerivAt sinh (cosh x) x :=
  (hasStrictDerivAt_sinh x).hasDerivAt

/--
@isnad1 id=isequiva.0h0v.s5.ce5e1642724f from=seed src=0 shape=8a0c861d vocab=3912b85c
-/
theorem isEquivalent_sinh : sinh ~[𝓝 0] id := by simpa using! (hasDerivAt_sinh 0).isLittleO

/--
@isnad1 id=contdiff.0h1v.s4.63f18b528e23 from=seed src=0 shape=99645fbc vocab=94a5f869
-/
@[fun_prop]
theorem contDiff_sinh {n} : ContDiff ℂ n sinh :=
  (contDiff_exp.sub contDiff_neg.cexp).div_const _

/--
@isnad1 id=differen.0h0v.s6.94ca59865139 from=seed src=0 shape=aa9fb30a vocab=54297246
-/
@[simp]
theorem differentiable_sinh : Differentiable ℂ sinh := fun x => (hasDerivAt_sinh x).differentiableAt

/--
@isnad1 id=differen.0h1v.s6.1a2c935f7c48 from=seed src=0 shape=1111aaa7 vocab=9daa69e5
-/
@[simp]
theorem differentiableAt_sinh {x : ℂ} : DifferentiableAt ℂ sinh x :=
  differentiable_sinh x

/-- The function `Complex.sinh` is complex analytic.
@isnad1 id=analytic.0h1v.s4.b3c7ab5fe680 from=seed src=0 shape=1111aaa7 vocab=a4e49852
-/
@[fun_prop]
lemma analyticAt_sinh {x : ℂ} : AnalyticAt ℂ sinh x :=
  contDiff_sinh.contDiffAt.analyticAt

/-- The function `Complex.sinh` is complex analytic.
@isnad1 id=analytic.0h2v.s4.2ecd2898e666 from=seed src=0 shape=611a48d1 vocab=ea273f6f
-/
lemma analyticWithinAt_sinh {x : ℂ} {s : Set ℂ} : AnalyticWithinAt ℂ sinh s x :=
  contDiff_sinh.contDiffWithinAt.analyticWithinAt

/-- The function `Complex.sinh` is complex analytic.
@isnad1 id=analytic.0h1v.s4.343af4dd2da9 from=seed src=0 shape=1543c05a vocab=81106712
-/
@[fun_prop]
theorem analyticOnNhd_sinh {s : Set ℂ} : AnalyticOnNhd ℂ sinh s :=
  fun _ _ ↦ analyticAt_sinh

/-- The function `Complex.sinh` is complex analytic.
@isnad1 id=analytic.0h1v.s4.e49840092ab6 from=seed src=0 shape=1543c05a vocab=d7e78aaa
-/
lemma analyticOn_sinh {s : Set ℂ} : AnalyticOn ℂ sinh s :=
  contDiff_sinh.contDiffOn.analyticOn

/--
@isnad1 id=eq.0h0v.s5.eac1b0d6e1d2 from=seed src=0 shape=1142214a vocab=57839600
-/
@[simp]
theorem deriv_sinh : deriv sinh = cosh :=
  funext fun x => (hasDerivAt_sinh x).deriv

/-- The complex hyperbolic cosine function is everywhere strictly differentiable, with the
derivative `sinh x`.
@isnad1 id=hasstric.0h1v.s5.dce2654b419f from=seed src=0 shape=475e04ea vocab=45a27c8e
-/
theorem hasStrictDerivAt_cosh (x : ℂ) : HasStrictDerivAt cosh (sinh x) x := by
  simp only [sinh, div_eq_mul_inv]
  convert!
    ((hasStrictDerivAt_exp x).add (hasStrictDerivAt_id x).fun_neg.cexp).mul_const (2 : ℂ)⁻¹ using 1
  rw [id, mul_neg_one, sub_eq_add_neg]

/-- The complex hyperbolic cosine function is everywhere differentiable, with the derivative
`sinh x`.
@isnad1 id=hasderiv.0h1v.s5.819ff2b6acb8 from=seed src=0 shape=475e04ea vocab=7dcf5519
-/
theorem hasDerivAt_cosh (x : ℂ) : HasDerivAt cosh (sinh x) x :=
  (hasStrictDerivAt_cosh x).hasDerivAt

/--
@isnad1 id=contdiff.0h1v.s4.19d0ad4ee3af from=seed src=0 shape=99645fbc vocab=db511359
-/
@[fun_prop]
theorem contDiff_cosh {n} : ContDiff ℂ n cosh :=
  (contDiff_exp.add contDiff_neg.cexp).div_const _

/--
@isnad1 id=differen.0h0v.s6.e5e7aa0631dd from=seed src=0 shape=aa9fb30a vocab=431e2263
-/
@[simp]
theorem differentiable_cosh : Differentiable ℂ cosh := fun x => (hasDerivAt_cosh x).differentiableAt

/--
@isnad1 id=differen.0h1v.s6.d9342f526ae3 from=seed src=0 shape=1111aaa7 vocab=22be422d
-/
@[simp]
theorem differentiableAt_cosh {x : ℂ} : DifferentiableAt ℂ cosh x :=
  differentiable_cosh x

/-- The function `Complex.cosh` is complex analytic.
@isnad1 id=analytic.0h1v.s4.4d56811b2326 from=seed src=0 shape=1111aaa7 vocab=e9c378a5
-/
@[fun_prop]
lemma analyticAt_cosh {x : ℂ} : AnalyticAt ℂ cosh x :=
  contDiff_cosh.contDiffAt.analyticAt

/-- The function `Complex.cosh` is complex analytic.
@isnad1 id=analytic.0h2v.s4.4ab04142910c from=seed src=0 shape=611a48d1 vocab=316964c4
-/
lemma analyticWithinAt_cosh {x : ℂ} {s : Set ℂ} : AnalyticWithinAt ℂ cosh s x :=
  contDiff_cosh.contDiffWithinAt.analyticWithinAt

/-- The function `Complex.cosh` is complex analytic.
@isnad1 id=analytic.0h1v.s4.7d44b99616ee from=seed src=0 shape=1543c05a vocab=48ac536e
-/
@[fun_prop]
theorem analyticOnNhd_cosh {s : Set ℂ} : AnalyticOnNhd ℂ cosh s :=
  fun _ _ ↦ analyticAt_cosh

/-- The function `Complex.cosh` is complex analytic.
@isnad1 id=analytic.0h1v.s4.df2cbe2cac50 from=seed src=0 shape=1543c05a vocab=0f65a6d9
-/
lemma analyticOn_cosh {s : Set ℂ} : AnalyticOn ℂ cosh s :=
  contDiff_cosh.contDiffOn.analyticOn

/--
@isnad1 id=eq.0h0v.s5.55e4b5723c7d from=seed src=0 shape=1142214a vocab=57839600
-/
@[simp]
theorem deriv_cosh : deriv cosh = sinh :=
  funext fun x => (hasDerivAt_cosh x).deriv

end Complex

section

/-! ### Simp lemmas for derivatives of `fun x => Complex.cos (f x)` etc., `f : ℂ → ℂ` -/

variable {f : ℂ → ℂ} {f' x : ℂ} {s : Set ℂ}

/-! #### `Complex.cosh` -/

/--
@isnad1 id=hasstric.1h3v.s6.1a2546f379f6 from=seed src=0 shape=eadbc56d vocab=47f1ee58
-/
theorem HasStrictDerivAt.ccosh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') x :=
  (Complex.hasStrictDerivAt_cosh (f x)).comp x hf

/--
@isnad1 id=hasderiv.1h3v.s6.b4c735daad44 from=seed src=0 shape=eadbc56d vocab=1a19230e
-/
theorem HasDerivAt.ccosh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') x :=
  (Complex.hasDerivAt_cosh (f x)).comp x hf

/--
@isnad1 id=hasderiv.1h4v.s6.252fad1d52b8 from=seed src=0 shape=070abf00 vocab=27d9fbb3
-/
theorem HasDerivWithinAt.ccosh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') s x :=
  (Complex.hasDerivAt_cosh (f x)).comp_hasDerivWithinAt x hf

/--
@isnad1 id=eq.2h3v.s7.f60ba2e00756 from=seed src=0 shape=157b391a vocab=09d7c011
-/
theorem derivWithin_ccosh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.cosh (f x)) s x = Complex.sinh (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.ccosh.derivWithin hxs

/--
@isnad1 id=eq.1h2v.s7.c66725c9995c from=seed src=0 shape=3c2f1879 vocab=03fa4a76
-/
@[simp]
theorem deriv_ccosh (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.cosh (f x)) x = Complex.sinh (f x) * deriv f x :=
  hc.hasDerivAt.ccosh.deriv

/-! #### `Complex.sinh` -/

/--
@isnad1 id=hasstric.1h3v.s6.bbabc11e0b14 from=seed src=0 shape=eadbc56d vocab=47f1ee58
-/
theorem HasStrictDerivAt.csinh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') x :=
  (Complex.hasStrictDerivAt_sinh (f x)).comp x hf

/--
@isnad1 id=hasderiv.1h3v.s6.eb78a7f9f107 from=seed src=0 shape=eadbc56d vocab=1a19230e
-/
theorem HasDerivAt.csinh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') x :=
  (Complex.hasDerivAt_sinh (f x)).comp x hf

/--
@isnad1 id=hasderiv.1h4v.s6.6910036c481a from=seed src=0 shape=070abf00 vocab=27d9fbb3
-/
theorem HasDerivWithinAt.csinh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') s x :=
  (Complex.hasDerivAt_sinh (f x)).comp_hasDerivWithinAt x hf

/--
@isnad1 id=eq.2h3v.s7.b50d24eec3a3 from=seed src=0 shape=157b391a vocab=09d7c011
-/
theorem derivWithin_csinh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.sinh (f x)) s x = Complex.cosh (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.csinh.derivWithin hxs

/--
@isnad1 id=eq.1h2v.s7.ec1575b0feea from=seed src=0 shape=3c2f1879 vocab=03fa4a76
-/
@[simp]
theorem deriv_csinh (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.sinh (f x)) x = Complex.cosh (f x) * deriv f x :=
  hc.hasDerivAt.csinh.deriv

end

section

/-! ### Simp lemmas for derivatives of `fun x => Complex.cos (f x)` etc., `f : E → ℂ` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ} {f' : StrongDual ℂ E}
  {x : E} {s : Set E}

/-! #### `Complex.cosh` -/

/--
@isnad1 id=hasstric.1h4v.s8.4005259f8328 from=seed src=0 shape=b933ca5d vocab=fc32b527
-/
theorem HasStrictFDerivAt.ccosh (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') x :=
  (Complex.hasStrictDerivAt_cosh (f x)).comp_hasStrictFDerivAt x hf

/--
@isnad1 id=hasfderi.1h4v.s8.e34b818fd962 from=seed src=0 shape=b933ca5d vocab=b86d7c02
-/
theorem HasFDerivAt.ccosh (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') x :=
  (Complex.hasDerivAt_cosh (f x)).comp_hasFDerivAt x hf

/--
@isnad1 id=hasfderi.1h5v.s8.f42bf57539ee from=seed src=0 shape=7a76a57a vocab=6fc5b47a
-/
theorem HasFDerivWithinAt.ccosh (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') s x :=
  (Complex.hasDerivAt_cosh (f x)).comp_hasFDerivWithinAt x hf

/--
@isnad1 id=differen.1h4v.s7.555329928a2f from=seed src=0 shape=7b9f6adc vocab=4428623d
-/
theorem DifferentiableWithinAt.ccosh (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.cosh (f x)) s x :=
  hf.hasFDerivWithinAt.ccosh.differentiableWithinAt

/--
@isnad1 id=differen.1h3v.s7.0df526ad3944 from=seed src=0 shape=5aea9e37 vocab=85f53dce
-/
@[simp, fun_prop]
theorem DifferentiableAt.ccosh (hc : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun x => Complex.cosh (f x)) x :=
  hc.hasFDerivAt.ccosh.differentiableAt

/--
@isnad1 id=differen.1h3v.s7.2573e352e3c1 from=seed src=0 shape=f10b1b92 vocab=27a6713a
-/
theorem DifferentiableOn.ccosh (hc : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (fun x => Complex.cosh (f x)) s := fun x h => (hc x h).ccosh

/--
@isnad1 id=differen.1h2v.s7.1fd4baa3e842 from=seed src=0 shape=b96fd126 vocab=d9a86bba
-/
@[simp, fun_prop]
theorem Differentiable.ccosh (hc : Differentiable ℂ f) :
    Differentiable ℂ fun x => Complex.cosh (f x) := fun x => (hc x).ccosh

/--
@isnad1 id=eq.2h4v.s9.e9c7323bcd8c from=seed src=0 shape=39c3def1 vocab=68d8acc3
-/
theorem fderivWithin_ccosh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.cosh (f x)) s x = Complex.sinh (f x) • fderivWithin ℂ f s x :=
  hf.hasFDerivWithinAt.ccosh.fderivWithin hxs

/--
@isnad1 id=eq.1h3v.s9.c9e9215c6c18 from=seed src=0 shape=492bcbaf vocab=f5aa5b06
-/
@[simp]
theorem fderiv_ccosh (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.cosh (f x)) x = Complex.sinh (f x) • fderiv ℂ f x :=
  hc.hasFDerivAt.ccosh.fderiv

/--
@isnad1 id=contdiff.1h3v.s6.3834b886bc10 from=seed src=0 shape=3a9d16d9 vocab=0203c75e
-/
theorem ContDiff.ccosh {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.cosh (f x) :=
  Complex.contDiff_cosh.comp h

/--
@isnad1 id=contdiff.1h4v.s6.03703faa511d from=seed src=0 shape=337315c5 vocab=1c4a11cf
-/
theorem ContDiffAt.ccosh {n} (hf : ContDiffAt ℂ n f x) :
    ContDiffAt ℂ n (fun x => Complex.cosh (f x)) x :=
  Complex.contDiff_cosh.contDiffAt.comp x hf

/--
@isnad1 id=contdiff.1h4v.s6.f6e57e957069 from=seed src=0 shape=c910d4e3 vocab=81331b85
-/
theorem ContDiffOn.ccosh {n} (hf : ContDiffOn ℂ n f s) :
    ContDiffOn ℂ n (fun x => Complex.cosh (f x)) s :=
  Complex.contDiff_cosh.comp_contDiffOn hf

/--
@isnad1 id=contdiff.1h5v.s6.f8389e9c7e36 from=seed src=0 shape=78794890 vocab=a5b9dcf5
-/
theorem ContDiffWithinAt.ccosh {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.cosh (f x)) s x :=
  Complex.contDiff_cosh.contDiffAt.comp_contDiffWithinAt x hf

/-! #### `Complex.sinh` -/

/--
@isnad1 id=hasstric.1h4v.s8.c3180d0fc348 from=seed src=0 shape=b933ca5d vocab=fc32b527
-/
theorem HasStrictFDerivAt.csinh (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') x :=
  (Complex.hasStrictDerivAt_sinh (f x)).comp_hasStrictFDerivAt x hf

/--
@isnad1 id=hasfderi.1h4v.s8.e5eca7cddbc8 from=seed src=0 shape=b933ca5d vocab=b86d7c02
-/
theorem HasFDerivAt.csinh (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') x :=
  (Complex.hasDerivAt_sinh (f x)).comp_hasFDerivAt x hf

/--
@isnad1 id=hasfderi.1h5v.s8.0929069371b2 from=seed src=0 shape=7a76a57a vocab=6fc5b47a
-/
theorem HasFDerivWithinAt.csinh (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') s x :=
  (Complex.hasDerivAt_sinh (f x)).comp_hasFDerivWithinAt x hf

/--
@isnad1 id=differen.1h4v.s7.8cc80c02f24a from=seed src=0 shape=7b9f6adc vocab=5de9097f
-/
theorem DifferentiableWithinAt.csinh (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.sinh (f x)) s x :=
  hf.hasFDerivWithinAt.csinh.differentiableWithinAt

/--
@isnad1 id=differen.1h3v.s7.56ef8e39e531 from=seed src=0 shape=5aea9e37 vocab=504b1bab
-/
@[simp, fun_prop]
theorem DifferentiableAt.csinh (hc : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun x => Complex.sinh (f x)) x :=
  hc.hasFDerivAt.csinh.differentiableAt

/--
@isnad1 id=differen.1h3v.s7.8ca7d3d56ec3 from=seed src=0 shape=f10b1b92 vocab=617315ab
-/
theorem DifferentiableOn.csinh (hc : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (fun x => Complex.sinh (f x)) s := fun x h => (hc x h).csinh

/--
@isnad1 id=differen.1h2v.s7.e8cb2457c7d3 from=seed src=0 shape=b96fd126 vocab=a3c2912a
-/
@[simp, fun_prop]
theorem Differentiable.csinh (hc : Differentiable ℂ f) :
    Differentiable ℂ fun x => Complex.sinh (f x) := fun x => (hc x).csinh

/--
@isnad1 id=eq.2h4v.s9.cc3138a004a8 from=seed src=0 shape=39c3def1 vocab=68d8acc3
-/
theorem fderivWithin_csinh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.sinh (f x)) s x = Complex.cosh (f x) • fderivWithin ℂ f s x :=
  hf.hasFDerivWithinAt.csinh.fderivWithin hxs

/--
@isnad1 id=eq.1h3v.s9.775e85556d52 from=seed src=0 shape=492bcbaf vocab=f5aa5b06
-/
@[simp]
theorem fderiv_csinh (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.sinh (f x)) x = Complex.cosh (f x) • fderiv ℂ f x :=
  hc.hasFDerivAt.csinh.fderiv

/--
@isnad1 id=contdiff.1h3v.s6.5ba7bb64d139 from=seed src=0 shape=3a9d16d9 vocab=cbef34ec
-/
theorem ContDiff.csinh {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.sinh (f x) :=
  Complex.contDiff_sinh.comp h

/--
@isnad1 id=contdiff.1h4v.s6.6870f2c3e8ff from=seed src=0 shape=337315c5 vocab=b28c45f5
-/
theorem ContDiffAt.csinh {n} (hf : ContDiffAt ℂ n f x) :
    ContDiffAt ℂ n (fun x => Complex.sinh (f x)) x :=
  Complex.contDiff_sinh.contDiffAt.comp x hf

/--
@isnad1 id=contdiff.1h4v.s6.9523a74aa5db from=seed src=0 shape=c910d4e3 vocab=e8b33c06
-/
theorem ContDiffOn.csinh {n} (hf : ContDiffOn ℂ n f s) :
    ContDiffOn ℂ n (fun x => Complex.sinh (f x)) s :=
  Complex.contDiff_sinh.comp_contDiffOn hf

/--
@isnad1 id=contdiff.1h5v.s6.694da9ee7ff7 from=seed src=0 shape=78794890 vocab=42c430e7
-/
theorem ContDiffWithinAt.csinh {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.sinh (f x)) s x :=
  Complex.contDiff_sinh.contDiffAt.comp_contDiffWithinAt x hf

end

namespace Real

variable {x y : ℝ}

/--
@isnad1 id=hasstric.0h1v.s5.cd6034db9630 from=seed src=0 shape=475e04ea vocab=aa981b08
-/
theorem hasStrictDerivAt_sinh (x : ℝ) : HasStrictDerivAt sinh (cosh x) x :=
  (Complex.hasStrictDerivAt_sinh x).real_of_complex

/--
@isnad1 id=hasderiv.0h1v.s5.ff30d9d71a19 from=seed src=0 shape=475e04ea vocab=128e8fee
-/
theorem hasDerivAt_sinh (x : ℝ) : HasDerivAt sinh (cosh x) x :=
  (Complex.hasDerivAt_sinh x).real_of_complex

/--
@isnad1 id=isequiva.0h0v.s4.e15e06d006c0 from=seed src=0 shape=8a0c861d vocab=803e9b14
-/
theorem isEquivalent_sinh : sinh ~[𝓝 0] id := by simpa using! (hasDerivAt_sinh 0).isLittleO

/--
@isnad1 id=contdiff.0h1v.s4.9fa12893d97a from=seed src=0 shape=99645fbc vocab=fcce748b
-/
@[fun_prop]
theorem contDiff_sinh {n} : ContDiff ℝ n sinh :=
  Complex.contDiff_sinh.real_of_complex

/--
@isnad1 id=differen.0h0v.s5.80c125ec9f9d from=seed src=0 shape=aa9fb30a vocab=7e2b5c25
-/
@[simp]
theorem differentiable_sinh : Differentiable ℝ sinh := fun x => (hasDerivAt_sinh x).differentiableAt

/--
@isnad1 id=differen.0h1v.s5.24d40b018ef7 from=seed src=0 shape=1111aaa7 vocab=cfc5e5c0
-/
@[simp]
theorem differentiableAt_sinh : DifferentiableAt ℝ sinh x :=
  differentiable_sinh x

/-- The function `Real.sinh` is real analytic.
@isnad1 id=analytic.0h1v.s4.695bc93b4356 from=seed src=0 shape=1111aaa7 vocab=b47778aa
-/
@[fun_prop]
lemma analyticAt_sinh : AnalyticAt ℝ sinh x :=
  contDiff_sinh.contDiffAt.analyticAt

/-- The function `Real.sinh` is real analytic.
@isnad1 id=analytic.0h2v.s4.ee4335d5739c from=seed src=0 shape=611a48d1 vocab=664ee209
-/
lemma analyticWithinAt_sinh {s : Set ℝ} : AnalyticWithinAt ℝ sinh s x :=
  contDiff_sinh.contDiffWithinAt.analyticWithinAt

/-- The function `Real.sinh` is real analytic.
@isnad1 id=analytic.0h1v.s4.68ebc9b86300 from=seed src=0 shape=1543c05a vocab=61788dc0
-/
@[fun_prop]
theorem analyticOnNhd_sinh {s : Set ℝ} : AnalyticOnNhd ℝ sinh s :=
  fun _ _ ↦ analyticAt_sinh

/-- The function `Real.sinh` is real analytic.
@isnad1 id=analytic.0h1v.s4.be0e7a4a75d1 from=seed src=0 shape=1543c05a vocab=7cdec9a5
-/
lemma analyticOn_sinh {s : Set ℝ} : AnalyticOn ℝ sinh s :=
  contDiff_sinh.contDiffOn.analyticOn

/--
@isnad1 id=eq.0h0v.s5.2ff073bf0ee6 from=seed src=0 shape=1142214a vocab=a70f9fa5
-/
@[simp]
theorem deriv_sinh : deriv sinh = cosh :=
  funext fun x => (hasDerivAt_sinh x).deriv

/--
@isnad1 id=hasstric.0h1v.s5.ae5115167b6c from=seed src=0 shape=475e04ea vocab=aa981b08
-/
theorem hasStrictDerivAt_cosh (x : ℝ) : HasStrictDerivAt cosh (sinh x) x :=
  (Complex.hasStrictDerivAt_cosh x).real_of_complex

/--
@isnad1 id=hasderiv.0h1v.s5.5430e95c9daf from=seed src=0 shape=475e04ea vocab=128e8fee
-/
theorem hasDerivAt_cosh (x : ℝ) : HasDerivAt cosh (sinh x) x :=
  (Complex.hasDerivAt_cosh x).real_of_complex

/--
@isnad1 id=contdiff.0h1v.s4.72270b7852bc from=seed src=0 shape=99645fbc vocab=d60510ff
-/
@[fun_prop]
theorem contDiff_cosh {n} : ContDiff ℝ n cosh :=
  Complex.contDiff_cosh.real_of_complex

/--
@isnad1 id=differen.0h0v.s5.26fdc1ba0ecc from=seed src=0 shape=aa9fb30a vocab=8705516d
-/
@[simp]
theorem differentiable_cosh : Differentiable ℝ cosh := fun x => (hasDerivAt_cosh x).differentiableAt

/--
@isnad1 id=differen.0h1v.s5.bd8d5f4e74a4 from=seed src=0 shape=1111aaa7 vocab=3f0b6a52
-/
@[simp]
theorem differentiableAt_cosh : DifferentiableAt ℝ cosh x :=
  differentiable_cosh x

/-- The function `Real.cosh` is real analytic.
@isnad1 id=analytic.0h1v.s4.b01afa9cb584 from=seed src=0 shape=1111aaa7 vocab=7539c29d
-/
@[fun_prop]
lemma analyticAt_cosh : AnalyticAt ℝ cosh x :=
  contDiff_cosh.contDiffAt.analyticAt

/-- The function `Real.cosh` is real analytic.
@isnad1 id=analytic.0h2v.s4.386c9af0a351 from=seed src=0 shape=611a48d1 vocab=1ac2e7b2
-/
lemma analyticWithinAt_cosh {s : Set ℝ} : AnalyticWithinAt ℝ cosh s x :=
  contDiff_cosh.contDiffWithinAt.analyticWithinAt

/-- The function `Real.cosh` is real analytic.
@isnad1 id=analytic.0h1v.s4.ebaf14334906 from=seed src=0 shape=1543c05a vocab=f4b4ce1c
-/
@[fun_prop]
theorem analyticOnNhd_cosh {s : Set ℝ} : AnalyticOnNhd ℝ cosh s :=
  fun _ _ ↦ analyticAt_cosh

/-- The function `Real.cosh` is real analytic.
@isnad1 id=analytic.0h1v.s4.8e51913bbeac from=seed src=0 shape=1543c05a vocab=e73d2446
-/
lemma analyticOn_cosh {s : Set ℝ} : AnalyticOn ℝ cosh s :=
  contDiff_cosh.contDiffOn.analyticOn

/--
@isnad1 id=eq.0h0v.s5.4327f2f0cec3 from=seed src=0 shape=1142214a vocab=a70f9fa5
-/
@[simp]
theorem deriv_cosh : deriv cosh = sinh :=
  funext fun x => (hasDerivAt_cosh x).deriv

/-- `sinh` is strictly monotone.
@isnad1 id=strictmo.0h0v.s2.bdbb8aae0cd4 from=seed src=0 shape=e3d48bcb vocab=bd087bbc
-/
theorem sinh_strictMono : StrictMono sinh :=
  strictMono_of_deriv_pos <| by rw [Real.deriv_sinh]; exact cosh_pos

/-- `sinh` is injective, `∀ a b, sinh a = sinh b → a = b`.
@isnad1 id=injectiv.0h0v.s2.9c2f13d8a2f3 from=seed src=0 shape=e3d48bcb vocab=0dec2566
-/
theorem sinh_injective : Function.Injective sinh :=
  sinh_strictMono.injective

/--
@isnad1 id=iff.0h2v.s3.f92ba4271039 from=seed src=0 shape=486d9771 vocab=6c052bca
-/
@[simp]
theorem sinh_inj : sinh x = sinh y ↔ x = y :=
  sinh_injective.eq_iff

/--
@isnad1 id=iff.0h2v.s4.0c01c4d74809 from=seed src=0 shape=486d9771 vocab=53c08a82
-/
@[simp]
theorem sinh_le_sinh : sinh x ≤ sinh y ↔ x ≤ y :=
  sinh_strictMono.le_iff_le

/--
@isnad1 id=iff.0h2v.s4.f8c9bc00ed55 from=seed src=0 shape=486d9771 vocab=171f1dc8
-/
@[simp]
theorem sinh_lt_sinh : sinh x < sinh y ↔ x < y :=
  sinh_strictMono.lt_iff_lt

/--
@isnad1 id=iff.0h1v.s4.40970fb0a605 from=seed src=0 shape=1317a4e0 vocab=6c052bca
-/
@[simp] lemma sinh_eq_zero : sinh x = 0 ↔ x = 0 := by rw [← @sinh_inj x, sinh_zero]

/--
@isnad1 id=iff.0h1v.s4.8c903e10df4a from=seed src=0 shape=1317a4e0 vocab=6c052bca
-/
lemma sinh_ne_zero : sinh x ≠ 0 ↔ x ≠ 0 := sinh_eq_zero.not

/--
@isnad1 id=iff.0h1v.s4.444c9b7d6f9f from=seed src=0 shape=57f73327 vocab=171f1dc8
-/
@[simp]
theorem sinh_pos_iff : 0 < sinh x ↔ 0 < x := by simpa only [sinh_zero] using @sinh_lt_sinh 0 x

/--
@isnad1 id=iff.0h1v.s4.be55709282a7 from=seed src=0 shape=1317a4e0 vocab=53c08a82
-/
@[simp]
theorem sinh_nonpos_iff : sinh x ≤ 0 ↔ x ≤ 0 := by simpa only [sinh_zero] using @sinh_le_sinh x 0

/--
@isnad1 id=iff.0h1v.s4.e9a1baee96c3 from=seed src=0 shape=1317a4e0 vocab=171f1dc8
-/
@[simp]
theorem sinh_neg_iff : sinh x < 0 ↔ x < 0 := by simpa only [sinh_zero] using @sinh_lt_sinh x 0

/--
@isnad1 id=iff.0h1v.s4.755d314f2acd from=seed src=0 shape=57f73327 vocab=53c08a82
-/
@[simp]
theorem sinh_nonneg_iff : 0 ≤ sinh x ↔ 0 ≤ x := by simpa only [sinh_zero] using @sinh_le_sinh 0 x

/--
@isnad1 id=eq.0h1v.s4.db883dcb90e5 from=seed src=0 shape=d62e2955 vocab=10c10939
-/
theorem abs_sinh (x : ℝ) : |sinh x| = sinh |x| := by
  cases le_total x 0 <;> simp [abs_of_nonneg, abs_of_nonpos, *]

/--
@isnad1 id=strictmo.0h0v.s3.c1a29a0a2888 from=seed src=0 shape=f2a09be3 vocab=6f09177d
-/
theorem cosh_strictMonoOn : StrictMonoOn cosh (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici _) continuous_cosh.continuousOn fun x hx => by
    rw [interior_Ici, mem_Ioi] at hx; rwa [deriv_cosh, sinh_pos_iff]

/--
@isnad1 id=iff.0h2v.s4.276c7c59b71c from=seed src=0 shape=77712aaf vocab=ec0b6bc8
-/
@[simp]
theorem cosh_le_cosh : cosh x ≤ cosh y ↔ |x| ≤ |y| :=
  cosh_abs x ▸ cosh_abs y ▸ cosh_strictMonoOn.le_iff_le (abs_nonneg x) (abs_nonneg y)

/--
@isnad1 id=iff.0h2v.s4.0ce7c497ca19 from=seed src=0 shape=77712aaf vocab=22122332
-/
@[simp]
theorem cosh_lt_cosh : cosh x < cosh y ↔ |x| < |y| :=
  lt_iff_lt_of_le_iff_le cosh_le_cosh

/--
@isnad1 id=le.0h1v.s3.527b718838b4 from=seed src=0 shape=8a62b088 vocab=b26caafc
-/
@[simp]
theorem one_le_cosh (x : ℝ) : 1 ≤ cosh x :=
  cosh_zero ▸ cosh_le_cosh.2 (by simp only [_root_.abs_zero, _root_.abs_nonneg])

/--
@isnad1 id=iff.0h1v.s4.29942416d647 from=seed src=0 shape=58257f7d vocab=b38ff8ae
-/
@[simp]
theorem one_lt_cosh : 1 < cosh x ↔ x ≠ 0 :=
  cosh_zero ▸ cosh_lt_cosh.trans (by simp only [_root_.abs_zero, abs_pos])

/--
@isnad1 id=strictmo.0h0v.s4.86dffee3d88f from=seed src=0 shape=5dc881e2 vocab=e7647e3d
-/
theorem sinh_sub_id_strictMono : StrictMono fun x => sinh x - x := by
  refine strictMono_of_odd_strictMonoOn_nonneg (fun x => by simp; abel) ?_
  refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ fun x hx => ?_
  · exact (continuous_sinh.sub continuous_id).continuousOn
  · rw [interior_Ici, mem_Ioi] at hx
    rw [deriv_fun_sub, deriv_sinh, deriv_id'', sub_pos, one_lt_cosh]
    exacts [hx.ne', differentiableAt_sinh, differentiableAt_id]

/--
@isnad1 id=iff.0h1v.s4.3bc3940c4fda from=seed src=0 shape=5ebe8d67 vocab=53c08a82
-/
@[simp]
theorem self_le_sinh_iff : x ≤ sinh x ↔ 0 ≤ x :=
  calc
    x ≤ sinh x ↔ sinh 0 - 0 ≤ sinh x - x := by simp
    _ ↔ 0 ≤ x := sinh_sub_id_strictMono.le_iff_le

/--
@isnad1 id=iff.0h1v.s4.18da4672fbd5 from=seed src=0 shape=79e03a20 vocab=53c08a82
-/
@[simp]
theorem sinh_le_self_iff : sinh x ≤ x ↔ x ≤ 0 :=
  calc
    sinh x ≤ x ↔ sinh x - x ≤ sinh 0 - 0 := by simp
    _ ↔ x ≤ 0 := sinh_sub_id_strictMono.le_iff_le

/--
@isnad1 id=iff.0h1v.s4.35d7e5ebde45 from=seed src=0 shape=5ebe8d67 vocab=171f1dc8
-/
@[simp]
theorem self_lt_sinh_iff : x < sinh x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le sinh_le_self_iff

/--
@isnad1 id=iff.0h1v.s4.de047f852b0a from=seed src=0 shape=79e03a20 vocab=171f1dc8
-/
@[simp]
theorem sinh_lt_self_iff : sinh x < x ↔ x < 0 :=
  lt_iff_lt_of_le_iff_le self_le_sinh_iff

end Real

section iteratedDeriv

/-! ### Simp lemmas for iterated derivatives of `sinh` and `cosh`. -/

namespace Complex

/--
@isnad1 id=eq.0h1v.s5.60fd5dba19c9 from=seed src=0 shape=adc35206 vocab=1ad8586c
-/
@[simp]
theorem iteratedDeriv_add_one_sinh (n : ℕ) :
    iteratedDeriv (n + 1) sinh = iteratedDeriv n cosh := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]

/--
@isnad1 id=eq.0h1v.s5.e0d2ac6497e5 from=seed src=0 shape=adc35206 vocab=1ad8586c
-/
@[simp]
theorem iteratedDeriv_add_one_cosh (n : ℕ) :
    iteratedDeriv (n + 1) cosh = iteratedDeriv n sinh := by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]

/--
@isnad1 id=eq.0h1v.s5.66ad90d22dd3 from=seed src=0 shape=52315cb2 vocab=9e90e657
-/
@[simp]
theorem iteratedDeriv_even_sinh (n : ℕ) :
    iteratedDeriv (2 * n) sinh = sinh := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

/--
@isnad1 id=eq.0h1v.s5.99d52c7e2ce2 from=seed src=0 shape=52315cb2 vocab=35a91378
-/
@[simp]
theorem iteratedDeriv_even_cosh (n : ℕ) :
    iteratedDeriv (2 * n) cosh = cosh := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

/--
@isnad1 id=eq.0h1v.s5.9a2eceebc521 from=seed src=0 shape=b2c4737a vocab=113aa3f8
-/
theorem iteratedDeriv_odd_sinh (n : ℕ) :
    iteratedDeriv (2 * n + 1) sinh = cosh := by simp

/--
@isnad1 id=eq.0h1v.s5.1f386782470b from=seed src=0 shape=b2c4737a vocab=113aa3f8
-/
theorem iteratedDeriv_odd_cosh (n : ℕ) :
    iteratedDeriv (2 * n + 1) cosh = sinh := by simp

/--
@isnad1 id=differen.0h1v.s6.638450a39d23 from=seed src=0 shape=9141b19d vocab=fe0bb9d6
-/
theorem differentiable_iteratedDeriv_sinh (n : ℕ) :
    Differentiable ℂ (iteratedDeriv n sinh) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sinh]

/--
@isnad1 id=differen.0h1v.s6.63673109ab47 from=seed src=0 shape=9141b19d vocab=5cc6dd40
-/
theorem differentiable_iteratedDeriv_cosh (n : ℕ) :
    Differentiable ℂ (iteratedDeriv n cosh) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cosh]

end Complex

namespace Real

/--
@isnad1 id=eq.0h1v.s5.03dcb3440646 from=seed src=0 shape=adc35206 vocab=b8d55e20
-/
@[simp]
theorem iteratedDeriv_add_one_sinh (n : ℕ) :
    iteratedDeriv (n + 1) sinh = iteratedDeriv n cosh := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]

/--
@isnad1 id=eq.0h1v.s5.66d02674cb20 from=seed src=0 shape=adc35206 vocab=b8d55e20
-/
@[simp]
theorem iteratedDeriv_add_one_cosh (n : ℕ) :
    iteratedDeriv (n + 1) cosh = iteratedDeriv n sinh := by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]

/--
@isnad1 id=eq.0h1v.s5.628a846abd86 from=seed src=0 shape=52315cb2 vocab=a1eac41f
-/
@[simp]
theorem iteratedDeriv_even_sinh (n : ℕ) :
    iteratedDeriv (2 * n) sinh = sinh := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

/--
@isnad1 id=eq.0h1v.s5.f5dbda4e8fa6 from=seed src=0 shape=52315cb2 vocab=f279b8c5
-/
@[simp]
theorem iteratedDeriv_even_cosh (n : ℕ) :
    iteratedDeriv (2 * n) cosh = cosh := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

/--
@isnad1 id=eq.0h1v.s5.1435f2c6d208 from=seed src=0 shape=b2c4737a vocab=4b79c3d3
-/
theorem iteratedDeriv_odd_sinh (n : ℕ) :
    iteratedDeriv (2 * n + 1) sinh = cosh := by simp

/--
@isnad1 id=eq.0h1v.s5.1c50bc03e205 from=seed src=0 shape=b2c4737a vocab=4b79c3d3
-/
theorem iteratedDeriv_odd_cosh (n : ℕ) :
    iteratedDeriv (2 * n + 1) cosh = sinh := by simp

/--
@isnad1 id=differen.0h1v.s6.2fbbeccc2f1d from=seed src=0 shape=9141b19d vocab=b4b9f229
-/
theorem differentiable_iteratedDeriv_sinh (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n sinh) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sinh]

/--
@isnad1 id=differen.0h1v.s6.81c32da5a989 from=seed src=0 shape=9141b19d vocab=1b886c9c
-/
theorem differentiable_iteratedDeriv_cosh (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n cosh) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cosh]

/--
@isnad1 id=eq.2h4v.s6.23b6ce1ed34c from=seed src=0 shape=d58724db vocab=f77dafc7
-/
@[simp]
theorem iteratedDerivWithin_sinh_Icc (n : ℕ) {a b : ℝ} (h : a < b) {x : ℝ} (hx : x ∈ Icc a b) :
    iteratedDerivWithin n sinh (Icc a b) x = iteratedDeriv n sinh x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_sinh.contDiffAt hx

/--
@isnad1 id=eq.2h4v.s6.e77e62397432 from=seed src=0 shape=d58724db vocab=18c47601
-/
@[simp]
theorem iteratedDerivWithin_cosh_Icc (n : ℕ) {a b : ℝ} (h : a < b) {x : ℝ} (hx : x ∈ Icc a b) :
    iteratedDerivWithin n cosh (Icc a b) x = iteratedDeriv n cosh x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_cosh.contDiffAt hx

/--
@isnad1 id=eq.1h4v.s5.fc48e1377909 from=seed src=0 shape=10256091 vocab=de73b421
-/
@[simp]
theorem iteratedDerivWithin_sinh_Ioo (n : ℕ) {a b x : ℝ} (hx : x ∈ Ioo a b) :
    iteratedDerivWithin n sinh (Ioo a b) x = iteratedDeriv n sinh x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_sinh.contDiffAt hx

/--
@isnad1 id=eq.1h4v.s5.5b31441345da from=seed src=0 shape=10256091 vocab=9e10f8ea
-/
@[simp]
theorem iteratedDerivWithin_cosh_Ioo (n : ℕ) {a b x : ℝ} (hx : x ∈ Ioo a b) :
    iteratedDerivWithin n cosh (Ioo a b) x = iteratedDeriv n cosh x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_cosh.contDiffAt hx

end Real

end iteratedDeriv

section

/-! ### Simp lemmas for derivatives of `fun x => Real.cos (f x)` etc., `f : ℝ → ℝ` -/

variable {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}

/-! #### `Real.cosh` -/

/--
@isnad1 id=hasstric.1h3v.s6.4fdf7e0886aa from=seed src=0 shape=eadbc56d vocab=e7238845
-/
theorem HasStrictDerivAt.cosh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') x :=
  (Real.hasStrictDerivAt_cosh (f x)).comp x hf

/--
@isnad1 id=hasderiv.1h3v.s6.3eede9148986 from=seed src=0 shape=eadbc56d vocab=7875f51a
-/
theorem HasDerivAt.cosh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') x :=
  (Real.hasDerivAt_cosh (f x)).comp x hf

/--
@isnad1 id=hasderiv.1h4v.s6.e20e925bd164 from=seed src=0 shape=070abf00 vocab=c58004ae
-/
theorem HasDerivWithinAt.cosh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') s x :=
  (Real.hasDerivAt_cosh (f x)).comp_hasDerivWithinAt x hf

/--
@isnad1 id=eq.2h3v.s7.fc46f02b2e03 from=seed src=0 shape=157b391a vocab=430e2bb8
-/
theorem derivWithin_cosh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.cosh (f x)) s x = Real.sinh (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.cosh.derivWithin hxs

/--
@isnad1 id=eq.1h2v.s7.7b1f2453feba from=seed src=0 shape=3c2f1879 vocab=e6e1a521
-/
@[simp]
theorem deriv_cosh (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.cosh (f x)) x = Real.sinh (f x) * deriv f x :=
  hc.hasDerivAt.cosh.deriv

/-! #### `Real.sinh` -/

/--
@isnad1 id=hasstric.1h3v.s6.ebef8976d894 from=seed src=0 shape=eadbc56d vocab=e7238845
-/
theorem HasStrictDerivAt.sinh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') x :=
  (Real.hasStrictDerivAt_sinh (f x)).comp x hf

/--
@isnad1 id=hasderiv.1h3v.s6.768fffd7dff7 from=seed src=0 shape=eadbc56d vocab=7875f51a
-/
theorem HasDerivAt.sinh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') x :=
  (Real.hasDerivAt_sinh (f x)).comp x hf

/--
@isnad1 id=hasderiv.1h4v.s6.2edbedb2ab0a from=seed src=0 shape=070abf00 vocab=c58004ae
-/
theorem HasDerivWithinAt.sinh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') s x :=
  (Real.hasDerivAt_sinh (f x)).comp_hasDerivWithinAt x hf

/--
@isnad1 id=eq.2h3v.s7.2643744c2e56 from=seed src=0 shape=157b391a vocab=430e2bb8
-/
theorem derivWithin_sinh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.sinh (f x)) s x = Real.cosh (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.sinh.derivWithin hxs

/--
@isnad1 id=eq.1h2v.s7.e84db06156e8 from=seed src=0 shape=3c2f1879 vocab=e6e1a521
-/
@[simp]
theorem deriv_sinh (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.sinh (f x)) x = Real.cosh (f x) * deriv f x :=
  hc.hasDerivAt.sinh.deriv

end

section

/-! ### Simp lemmas for derivatives of `fun x => Real.cos (f x)` etc., `f : E → ℝ` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {f' : StrongDual ℝ E}
  {x : E} {s : Set E}

/-! #### `Real.cosh` -/

/--
@isnad1 id=hasstric.1h4v.s8.506cf7b7f479 from=seed src=0 shape=b933ca5d vocab=4cb4e632
-/
theorem HasStrictFDerivAt.cosh (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') x :=
  (Real.hasStrictDerivAt_cosh (f x)).comp_hasStrictFDerivAt x hf

/--
@isnad1 id=hasfderi.1h4v.s8.6b6552fea1cd from=seed src=0 shape=b933ca5d vocab=d4d766af
-/
theorem HasFDerivAt.cosh (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') x :=
  (Real.hasDerivAt_cosh (f x)).comp_hasFDerivAt x hf

/--
@isnad1 id=hasfderi.1h5v.s8.01ff0974907f from=seed src=0 shape=7a76a57a vocab=e681cb5b
-/
theorem HasFDerivWithinAt.cosh (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') s x :=
  (Real.hasDerivAt_cosh (f x)).comp_hasFDerivWithinAt x hf

/--
@isnad1 id=differen.1h4v.s7.cef7880075c1 from=seed src=0 shape=7b9f6adc vocab=c88400e7
-/
theorem DifferentiableWithinAt.cosh (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.cosh (f x)) s x :=
  hf.hasFDerivWithinAt.cosh.differentiableWithinAt

/--
@isnad1 id=differen.1h3v.s6.6d2f40c70139 from=seed src=0 shape=5aea9e37 vocab=11dc069b
-/
@[simp, fun_prop]
theorem DifferentiableAt.cosh (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => Real.cosh (f x)) x :=
  hc.hasFDerivAt.cosh.differentiableAt

/--
@isnad1 id=differen.1h3v.s6.edfae9f3d0cc from=seed src=0 shape=f10b1b92 vocab=24c2b50a
-/
theorem DifferentiableOn.cosh (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => Real.cosh (f x)) s := fun x h => (hc x h).cosh

/--
@isnad1 id=differen.1h2v.s6.650dc5bbae4d from=seed src=0 shape=b96fd126 vocab=f18f6113
-/
@[simp, fun_prop]
theorem Differentiable.cosh (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.cosh (f x) :=
  fun x => (hc x).cosh

/--
@isnad1 id=eq.2h4v.s9.facdd204f5ae from=seed src=0 shape=39c3def1 vocab=5dc22a82
-/
theorem fderivWithin_cosh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.cosh (f x)) s x = Real.sinh (f x) • fderivWithin ℝ f s x :=
  hf.hasFDerivWithinAt.cosh.fderivWithin hxs

/--
@isnad1 id=eq.1h3v.s9.134cf8e60d33 from=seed src=0 shape=492bcbaf vocab=6be580f8
-/
@[simp]
theorem fderiv_cosh (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.cosh (f x)) x = Real.sinh (f x) • fderiv ℝ f x :=
  hc.hasFDerivAt.cosh.fderiv

/--
@isnad1 id=contdiff.1h3v.s6.53c7647c8f28 from=seed src=0 shape=3a9d16d9 vocab=2041fe4d
-/
theorem ContDiff.cosh {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.cosh (f x) :=
  Real.contDiff_cosh.comp h

/--
@isnad1 id=contdiff.1h4v.s6.cbc9ced36fc5 from=seed src=0 shape=337315c5 vocab=cb1bde88
-/
theorem ContDiffAt.cosh {n} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun x => Real.cosh (f x)) x :=
  Real.contDiff_cosh.contDiffAt.comp x hf

/--
@isnad1 id=contdiff.1h4v.s6.dd33a330f86f from=seed src=0 shape=c910d4e3 vocab=66966c32
-/
theorem ContDiffOn.cosh {n} (hf : ContDiffOn ℝ n f s) :
    ContDiffOn ℝ n (fun x => Real.cosh (f x)) s :=
  Real.contDiff_cosh.comp_contDiffOn hf

/--
@isnad1 id=contdiff.1h5v.s6.a2e717f97e06 from=seed src=0 shape=78794890 vocab=f289782a
-/
theorem ContDiffWithinAt.cosh {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.cosh (f x)) s x :=
  Real.contDiff_cosh.contDiffAt.comp_contDiffWithinAt x hf

/-! #### `Real.sinh` -/

/--
@isnad1 id=hasstric.1h4v.s8.d937b6627045 from=seed src=0 shape=b933ca5d vocab=4cb4e632
-/
theorem HasStrictFDerivAt.sinh (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') x :=
  (Real.hasStrictDerivAt_sinh (f x)).comp_hasStrictFDerivAt x hf

/--
@isnad1 id=hasfderi.1h4v.s8.b24a8ac62f82 from=seed src=0 shape=b933ca5d vocab=d4d766af
-/
theorem HasFDerivAt.sinh (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') x :=
  (Real.hasDerivAt_sinh (f x)).comp_hasFDerivAt x hf

/--
@isnad1 id=hasfderi.1h5v.s8.15d09fb8b29d from=seed src=0 shape=7a76a57a vocab=e681cb5b
-/
theorem HasFDerivWithinAt.sinh (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') s x :=
  (Real.hasDerivAt_sinh (f x)).comp_hasFDerivWithinAt x hf

/--
@isnad1 id=differen.1h4v.s7.852e74dea835 from=seed src=0 shape=7b9f6adc vocab=5796af4d
-/
theorem DifferentiableWithinAt.sinh (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.sinh (f x)) s x :=
  hf.hasFDerivWithinAt.sinh.differentiableWithinAt

/--
@isnad1 id=differen.1h3v.s6.6fe2959f85c1 from=seed src=0 shape=5aea9e37 vocab=58fafeb1
-/
@[simp, fun_prop]
theorem DifferentiableAt.sinh (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => Real.sinh (f x)) x :=
  hc.hasFDerivAt.sinh.differentiableAt

/--
@isnad1 id=differen.1h3v.s6.d5bac20be106 from=seed src=0 shape=f10b1b92 vocab=b25601e9
-/
theorem DifferentiableOn.sinh (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => Real.sinh (f x)) s := fun x h => (hc x h).sinh

/--
@isnad1 id=differen.1h2v.s6.8c8c3f2701b8 from=seed src=0 shape=b96fd126 vocab=27a5b264
-/
@[simp, fun_prop]
theorem Differentiable.sinh (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.sinh (f x) :=
  fun x => (hc x).sinh

/--
@isnad1 id=eq.2h4v.s9.199d7319a5db from=seed src=0 shape=39c3def1 vocab=5dc22a82
-/
theorem fderivWithin_sinh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.sinh (f x)) s x = Real.cosh (f x) • fderivWithin ℝ f s x :=
  hf.hasFDerivWithinAt.sinh.fderivWithin hxs

/--
@isnad1 id=eq.1h3v.s9.20ed581faeb4 from=seed src=0 shape=492bcbaf vocab=6be580f8
-/
@[simp]
theorem fderiv_sinh (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.sinh (f x)) x = Real.cosh (f x) • fderiv ℝ f x :=
  hc.hasFDerivAt.sinh.fderiv

/--
@isnad1 id=contdiff.1h3v.s6.935ddc105116 from=seed src=0 shape=3a9d16d9 vocab=26066023
-/
theorem ContDiff.sinh {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.sinh (f x) :=
  Real.contDiff_sinh.comp h

/--
@isnad1 id=contdiff.1h4v.s6.64916db45856 from=seed src=0 shape=337315c5 vocab=bdc13f4f
-/
theorem ContDiffAt.sinh {n} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun x => Real.sinh (f x)) x :=
  Real.contDiff_sinh.contDiffAt.comp x hf

/--
@isnad1 id=contdiff.1h4v.s6.2c7f07d5411a from=seed src=0 shape=c910d4e3 vocab=1a6d014f
-/
theorem ContDiffOn.sinh {n} (hf : ContDiffOn ℝ n f s) :
    ContDiffOn ℝ n (fun x => Real.sinh (f x)) s :=
  Real.contDiff_sinh.comp_contDiffOn hf

/--
@isnad1 id=contdiff.1h5v.s6.98decf97b751 from=seed src=0 shape=78794890 vocab=50da0450
-/
theorem ContDiffWithinAt.sinh {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.sinh (f x)) s x :=
  Real.contDiff_sinh.contDiffAt.comp_contDiffWithinAt x hf

section LogDeriv

/--
@isnad1 id=eq.0h0v.s4.4e07a57bdd1d from=seed src=0 shape=1142214a vocab=c60fed1a
-/
@[simp]
theorem Complex.logDeriv_cosh : logDeriv (Complex.cosh) = Complex.tanh := by
  ext
  rw [logDeriv, Complex.deriv_cosh, Pi.div_apply, Complex.tanh]

/--
@isnad1 id=eq.0h0v.s4.2ea0fb10a59a from=seed src=0 shape=1142214a vocab=233d4465
-/
@[simp]
theorem Real.logDeriv_cosh : logDeriv (Real.cosh) = Real.tanh := by
  ext
  rw [logDeriv, Real.deriv_cosh, Pi.div_apply, Real.tanh_eq_sinh_div_cosh]

end LogDeriv

end

namespace Mathlib.Meta.Positivity
open Lean Qq

/--
@isnad1 id=lt.1h1v.s4.179d9b327e64 from=seed src=0 shape=35bd48ee vocab=171f1dc8
-/
alias ⟨_, sinh_pos_of_pos⟩ := Real.sinh_pos_iff
/--
@isnad1 id=le.1h1v.s4.14295c423f18 from=seed src=0 shape=35bd48ee vocab=53c08a82
-/
alias ⟨_, sinh_nonneg_of_nonneg⟩ := Real.sinh_nonneg_iff
/--
@isnad1 id=ne.1h1v.s4.1ef4c0782705 from=seed src=0 shape=5aedd577 vocab=6c052bca
-/
alias ⟨_, sinh_ne_zero_of_ne_zero⟩ := Real.sinh_ne_zero

/-- Extension for the `positivity` tactic: `Real.sinh` is positive/nonnegative/nonzero if its input
is. -/
@[positivity Real.sinh _]
meta def evalSinh : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  let zα : Q(Zero ℝ) := q(inferInstance)
  let pα : Q(PartialOrder ℝ) := q(inferInstance)
  match u, α, e with
  | 0, ~q(ℝ), ~q(Real.sinh $a) =>
    assumeInstancesCommute
    match ← core zα pα a with
    | .positive pa => return .positive q(sinh_pos_of_pos $pa)
    | .nonnegative pa => return .nonnegative q(sinh_nonneg_of_nonneg $pa)
    | .nonzero pa => return .nonzero q(sinh_ne_zero_of_ne_zero $pa)
    | _ => return .none
  | _, _, _ => throwError "not Real.sinh"

example (x : ℝ) (hx : 0 < x) : 0 < x.sinh := by positivity
example (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x.sinh := by positivity
example (x : ℝ) (hx : x ≠ 0) : x.sinh ≠ 0 := by positivity

end Mathlib.Meta.Positivity

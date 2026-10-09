/-
Copyright (c) 2020 James Arthur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Arthur, Chris Hughes, Shing Tak Lam
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic

/-!
# Inverse of the sinh function

In this file we prove that sinh is bijective and hence has an
inverse, arsinh.

## Main definitions

- `Real.arsinh`: The inverse function of `Real.sinh`.

- `Real.sinhEquiv`, `Real.sinhOrderIso`, `Real.sinhHomeomorph`: `Real.sinh` as an `Equiv`,
  `OrderIso`, and `Homeomorph`, respectively.

## Main Results

- `Real.sinh_surjective`, `Real.sinh_bijective`: `Real.sinh` is surjective and bijective;

- `Real.arsinh_injective`, `Real.arsinh_surjective`, `Real.arsinh_bijective`: `Real.arsinh` is
  injective, surjective, and bijective;

- `Real.continuous_arsinh`, `Real.differentiable_arsinh`, `Real.contDiff_arsinh`: `Real.arsinh` is
  continuous, differentiable, and continuously differentiable; we also provide dot notation
  convenience lemmas like `Filter.Tendsto.arsinh` and `ContDiffAt.arsinh`.

## Tags

arsinh, arcsinh, argsinh, asinh, sinh injective, sinh bijective, sinh surjective
-/

@[expose] public section

noncomputable section

open Function Filter Set

open scoped Topology

namespace Real

variable {x y : ℝ}

/-- `arsinh` is defined using a logarithm, `arsinh x = log (x + √(1 + x^2))`. -/
@[pp_nodot]
def arsinh (x : ℝ) :=
  log (x + √(1 + x ^ 2))

/--
@isnad1 id=eq.0h1v.s5.dacae3513e69 from=seed src=0 shape=9e3dac79 vocab=08e6e327
-/
theorem exp_arsinh (x : ℝ) : exp (arsinh x) = x + √(1 + x ^ 2) := by
  apply exp_log
  rw [← neg_lt_iff_pos_add']
  apply lt_sqrt_of_sq_lt
  simp

/--
@isnad1 id=eq.0h0v.s3.4cf08abcbebc from=seed src=0 shape=3c26ae4f vocab=3787b2fa
-/
@[simp]
theorem arsinh_zero : arsinh 0 = 0 := by simp [arsinh]

/--
@isnad1 id=eq.0h1v.s3.4062a26d2406 from=seed src=0 shape=c7188113 vocab=db1cc774
-/
@[simp]
theorem arsinh_neg (x : ℝ) : arsinh (-x) = -arsinh x := by
  rw [← exp_eq_exp, exp_arsinh, exp_neg, exp_arsinh]
  apply eq_inv_of_mul_eq_one_left
  rw [neg_sq, neg_add_eq_sub, add_comm x, mul_comm, ← sq_sub_sq, sq_sqrt, add_sub_cancel_right]
  exact add_nonneg zero_le_one (sq_nonneg _)

/-- `arsinh` is the right inverse of `sinh`.
@isnad1 id=eq.0h1v.s3.f723b0e026a0 from=seed src=0 shape=47dcad53 vocab=98269a4b
-/
@[simp]
theorem sinh_arsinh (x : ℝ) : sinh (arsinh x) = x := by
  rw [sinh_eq, ← arsinh_neg, exp_arsinh, exp_arsinh, neg_sq]; simp

/--
@isnad1 id=eq.0h1v.s5.4da53c510596 from=seed src=0 shape=42be39c8 vocab=fd117db1
-/
@[simp]
theorem cosh_arsinh (x : ℝ) : cosh (arsinh x) = √(1 + x ^ 2) := by
  rw [← sqrt_sq (cosh_pos _).le, cosh_sq', sinh_arsinh]

/--
@isnad1 id=eq.0h1v.s5.75c8347001ea from=seed src=0 shape=d0235f7b vocab=2089ec13
-/
@[simp]
theorem tanh_arsinh (x : ℝ) : tanh (arsinh x) = x / √(1 + x ^ 2) := by
  rw [tanh_eq_sinh_div_cosh, sinh_arsinh, cosh_arsinh]

/-- `sinh` is surjective, `∀ b, ∃ a, sinh a = b`. In this case, we use `a = arsinh b`.
@isnad1 id=surjecti.0h0v.s2.f2c93ee69f60 from=seed src=0 shape=e3d48bcb vocab=a160188a
-/
theorem sinh_surjective : Surjective sinh :=
  LeftInverse.surjective sinh_arsinh

/-- `sinh` is bijective, both injective and surjective.
@isnad1 id=bijectiv.0h0v.s2.d1d4e764946e from=seed src=0 shape=e3d48bcb vocab=e6ffca1c
-/
theorem sinh_bijective : Bijective sinh :=
  ⟨sinh_injective, sinh_surjective⟩

/-- `arsinh` is the left inverse of `sinh`.
@isnad1 id=eq.0h1v.s3.545314862156 from=seed src=0 shape=47dcad53 vocab=98269a4b
-/
@[simp]
theorem arsinh_sinh (x : ℝ) : arsinh (sinh x) = x :=
  rightInverse_of_injective_of_leftInverse sinh_injective sinh_arsinh x

/-- `Real.sinh` as an `Equiv`. -/
@[simps]
def sinhEquiv : ℝ ≃ ℝ where
  toFun := sinh
  invFun := arsinh
  left_inv := arsinh_sinh
  right_inv := sinh_arsinh

/-- `Real.sinh` as an `OrderIso`. -/
@[simps! -fullyApplied]
def sinhOrderIso : ℝ ≃o ℝ where
  toEquiv := sinhEquiv
  map_rel_iff' := @sinh_le_sinh

/-- `Real.sinh` as a `Homeomorph`. -/
@[simps! -fullyApplied]
def sinhHomeomorph : ℝ ≃ₜ ℝ :=
  sinhOrderIso.toHomeomorph

/--
@isnad1 id=bijectiv.0h0v.s2.d47126d36af1 from=seed src=0 shape=e3d48bcb vocab=cca4d110
-/
theorem arsinh_bijective : Bijective arsinh :=
  sinhEquiv.symm.bijective

/--
@isnad1 id=injectiv.0h0v.s2.4469001b085a from=seed src=0 shape=e3d48bcb vocab=8d25a55c
-/
theorem arsinh_injective : Injective arsinh :=
  sinhEquiv.symm.injective

/--
@isnad1 id=surjecti.0h0v.s2.76f4384424c3 from=seed src=0 shape=e3d48bcb vocab=b90e3703
-/
theorem arsinh_surjective : Surjective arsinh :=
  sinhEquiv.symm.surjective

/--
@isnad1 id=strictmo.0h0v.s2.7b815255926b from=seed src=0 shape=e3d48bcb vocab=da01048d
-/
theorem arsinh_strictMono : StrictMono arsinh :=
  sinhOrderIso.symm.strictMono

/--
@isnad1 id=iff.0h2v.s3.f75f4ce74be0 from=seed src=0 shape=486d9771 vocab=3787b2fa
-/
@[simp]
theorem arsinh_inj : arsinh x = arsinh y ↔ x = y :=
  arsinh_injective.eq_iff

/--
@isnad1 id=iff.0h2v.s4.93460c22d579 from=seed src=0 shape=486d9771 vocab=e00c788d
-/
@[simp, gcongr]
theorem arsinh_le_arsinh : arsinh x ≤ arsinh y ↔ x ≤ y :=
  sinhOrderIso.symm.le_iff_le

/--
@isnad1 id=iff.0h2v.s4.f7bf15d1f1bb from=seed src=0 shape=486d9771 vocab=a9c5e3c5
-/
@[simp]
theorem arsinh_lt_arsinh : arsinh x < arsinh y ↔ x < y :=
  sinhOrderIso.symm.lt_iff_lt

/--
@isnad1 id=iff.0h1v.s4.8dc12c8ee8d3 from=seed src=0 shape=1317a4e0 vocab=3787b2fa
-/
@[simp]
theorem arsinh_eq_zero_iff : arsinh x = 0 ↔ x = 0 :=
  arsinh_injective.eq_iff' arsinh_zero

/--
@isnad1 id=iff.0h1v.s4.4e6870294516 from=seed src=0 shape=57f73327 vocab=e00c788d
-/
@[simp]
theorem arsinh_nonneg_iff : 0 ≤ arsinh x ↔ 0 ≤ x := by rw [← sinh_le_sinh, sinh_zero, sinh_arsinh]

/--
@isnad1 id=iff.0h1v.s4.3e476eb6bee7 from=seed src=0 shape=1317a4e0 vocab=e00c788d
-/
@[simp]
theorem arsinh_nonpos_iff : arsinh x ≤ 0 ↔ x ≤ 0 := by rw [← sinh_le_sinh, sinh_zero, sinh_arsinh]

/--
@isnad1 id=iff.0h1v.s4.b88ecfb4ecb2 from=seed src=0 shape=57f73327 vocab=a9c5e3c5
-/
@[simp]
theorem arsinh_pos_iff : 0 < arsinh x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le arsinh_nonpos_iff

/--
@isnad1 id=iff.0h1v.s4.ae26ebd4d409 from=seed src=0 shape=1317a4e0 vocab=a9c5e3c5
-/
@[simp]
theorem arsinh_neg_iff : arsinh x < 0 ↔ x < 0 :=
  lt_iff_lt_of_le_iff_le arsinh_nonneg_iff

/--
@isnad1 id=hasstric.0h1v.s6.ec05570cf64e from=seed src=0 shape=970b15ed vocab=17f5b123
-/
theorem hasStrictDerivAt_arsinh (x : ℝ) : HasStrictDerivAt arsinh (√(1 + x ^ 2))⁻¹ x := by
  convert!
    sinhHomeomorph.toOpenPartialHomeomorph.hasStrictDerivAt_symm (mem_univ x) (cosh_pos _).ne'
      (hasStrictDerivAt_sinh _) using 2
  exact (cosh_arsinh _).symm

/--
@isnad1 id=hasderiv.0h1v.s6.7f106d9c1dbc from=seed src=0 shape=970b15ed vocab=0261c2b0
-/
theorem hasDerivAt_arsinh (x : ℝ) : HasDerivAt arsinh (√(1 + x ^ 2))⁻¹ x :=
  (hasStrictDerivAt_arsinh x).hasDerivAt

/--
@isnad1 id=differen.0h0v.s5.a49cfec52d5c from=seed src=0 shape=aa9fb30a vocab=6e3ce449
-/
@[fun_prop]
theorem differentiable_arsinh : Differentiable ℝ arsinh := fun x =>
  (hasDerivAt_arsinh x).differentiableAt

/--
@isnad1 id=contdiff.0h1v.s4.ce8584edbe41 from=seed src=0 shape=99645fbc vocab=abd09594
-/
@[fun_prop]
theorem contDiff_arsinh {n : WithTop ℕ∞} : ContDiff ℝ n arsinh :=
  sinhHomeomorph.contDiff_symm_deriv (fun x => (cosh_pos x).ne') hasDerivAt_sinh contDiff_sinh

/--
@isnad1 id=continuo.0h0v.s3.f7bd8b2455b2 from=seed src=0 shape=e3d48bcb vocab=b97fef08
-/
@[continuity]
theorem continuous_arsinh : Continuous arsinh :=
  sinhHomeomorph.symm.continuous

/-- The function `Real.arsinh` is real analytic.
@isnad1 id=analytic.0h1v.s4.55704fefb815 from=seed src=0 shape=1111aaa7 vocab=1c638048
-/
@[fun_prop]
lemma analyticAt_arsinh : AnalyticAt ℝ arsinh x :=
  contDiff_arsinh.contDiffAt.analyticAt

/-- The function `Real.arsinh` is real analytic.
@isnad1 id=analytic.0h2v.s4.5f15d6d1d0fe from=seed src=0 shape=611a48d1 vocab=41b14381
-/
lemma analyticWithinAt_arsinh {s : Set ℝ} : AnalyticWithinAt ℝ arsinh s x :=
  contDiff_arsinh.contDiffWithinAt.analyticWithinAt

/-- The function `Real.arsinh` is real analytic.
@isnad1 id=analytic.0h1v.s4.baf9936b1f93 from=seed src=0 shape=1543c05a vocab=b2bbcd53
-/
theorem analyticOnNhd_arsinh {s : Set ℝ} : AnalyticOnNhd ℝ arsinh s :=
  fun _ _ ↦ analyticAt_arsinh

/-- The function `Real.arsinh` is real analytic.
@isnad1 id=analytic.0h1v.s4.ba928b4fa070 from=seed src=0 shape=1543c05a vocab=8cf012ea
-/
lemma analyticOn_arsinh {s : Set ℝ} : AnalyticOn ℝ arsinh s :=
  contDiff_arsinh.contDiffOn.analyticOn

end Real

open Real

/--
@isnad1 id=tendsto.1h4v.s5.396ad781543a from=seed src=0 shape=104782f6 vocab=cd2410cd
-/
theorem Filter.Tendsto.arsinh {α : Type*} {l : Filter α} {f : α → ℝ} {a : ℝ}
    (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => arsinh (f x)) l (𝓝 (arsinh a)) :=
  (continuous_arsinh.tendsto _).comp h

section Continuous

variable {X : Type*} [TopologicalSpace X] {f : X → ℝ} {s : Set X} {a : X}

/--
@isnad1 id=continuo.1h3v.s5.a639a32191f2 from=seed src=0 shape=f3f7d4a1 vocab=1d2037c7
-/
nonrec theorem ContinuousAt.arsinh (h : ContinuousAt f a) :
    ContinuousAt (fun x => arsinh (f x)) a :=
  h.arsinh

/--
@isnad1 id=continuo.1h4v.s5.bc9a42452d0c from=seed src=0 shape=5d130993 vocab=395240c5
-/
nonrec theorem ContinuousWithinAt.arsinh (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => arsinh (f x)) s a :=
  h.arsinh

/--
@isnad1 id=continuo.1h3v.s5.09e43b020a44 from=seed src=0 shape=00e61124 vocab=e476deda
-/
theorem ContinuousOn.arsinh (h : ContinuousOn f s) : ContinuousOn (fun x => arsinh (f x)) s :=
  fun x hx => (h x hx).arsinh

/--
@isnad1 id=continuo.1h2v.s5.0c837d722413 from=seed src=0 shape=5a8ed934 vocab=3bc5c0b7
-/
theorem Continuous.arsinh (h : Continuous f) : Continuous fun x => arsinh (f x) :=
  continuous_arsinh.comp h

end Continuous

section fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {s : Set E} {a : E}
  {f' : StrongDual ℝ E} {n : ℕ∞}

/--
@isnad1 id=hasstric.1h4v.s8.23d6e85e6777 from=seed src=0 shape=813326df vocab=936a19fb
-/
theorem HasStrictFDerivAt.arsinh (hf : HasStrictFDerivAt f f' a) :
    HasStrictFDerivAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') a :=
  (hasStrictDerivAt_arsinh _).comp_hasStrictFDerivAt a hf

/--
@isnad1 id=hasfderi.1h4v.s8.2e56fa54c1f3 from=seed src=0 shape=813326df vocab=442c71c4
-/
theorem HasFDerivAt.arsinh (hf : HasFDerivAt f f' a) :
    HasFDerivAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') a :=
  (hasDerivAt_arsinh _).comp_hasFDerivAt a hf

/--
@isnad1 id=hasfderi.1h5v.s8.7c18b1d99dc8 from=seed src=0 shape=def0c2aa vocab=38c8f699
-/
theorem HasFDerivWithinAt.arsinh (hf : HasFDerivWithinAt f f' s a) :
    HasFDerivWithinAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') s a :=
  (hasDerivAt_arsinh _).comp_hasFDerivWithinAt a hf

/--
@isnad1 id=differen.1h3v.s6.ebac3c0d6ed2 from=seed src=0 shape=5aea9e37 vocab=114fd1d4
-/
@[fun_prop]
theorem DifferentiableAt.arsinh (h : DifferentiableAt ℝ f a) :
    DifferentiableAt ℝ (fun x => arsinh (f x)) a :=
  (differentiable_arsinh _).comp a h

/--
@isnad1 id=differen.1h4v.s7.a29f10597977 from=seed src=0 shape=d57c519f vocab=610da755
-/
@[fun_prop]
theorem DifferentiableWithinAt.arsinh (h : DifferentiableWithinAt ℝ f s a) :
    DifferentiableWithinAt ℝ (fun x => arsinh (f x)) s a :=
  (differentiable_arsinh _).comp_differentiableWithinAt a h

/--
@isnad1 id=differen.1h3v.s6.16d1c8ef5dec from=seed src=0 shape=f10b1b92 vocab=1fb58aa3
-/
@[fun_prop]
theorem DifferentiableOn.arsinh (h : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => arsinh (f x)) s := fun x hx => (h x hx).arsinh

/--
@isnad1 id=differen.1h2v.s6.eb44ed650b06 from=seed src=0 shape=b96fd126 vocab=db3c8dc9
-/
@[fun_prop]
theorem Differentiable.arsinh (h : Differentiable ℝ f) : Differentiable ℝ fun x => arsinh (f x) :=
  differentiable_arsinh.comp h

/--
@isnad1 id=contdiff.1h4v.s6.f76332375504 from=seed src=0 shape=9cff270b vocab=44963574
-/
@[fun_prop]
theorem ContDiffAt.arsinh (h : ContDiffAt ℝ n f a) : ContDiffAt ℝ n (fun x => arsinh (f x)) a :=
  contDiff_arsinh.contDiffAt.comp a h

/--
@isnad1 id=contdiff.1h5v.s6.6ba81951c953 from=seed src=0 shape=5bb726d4 vocab=4368da10
-/
@[fun_prop]
theorem ContDiffWithinAt.arsinh (h : ContDiffWithinAt ℝ n f s a) :
    ContDiffWithinAt ℝ n (fun x => arsinh (f x)) s a :=
  contDiff_arsinh.contDiffAt.comp_contDiffWithinAt a h

/--
@isnad1 id=contdiff.1h3v.s6.55ec10667ec6 from=seed src=0 shape=bd1c7137 vocab=5d881e8c
-/
@[fun_prop]
theorem ContDiff.arsinh (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => arsinh (f x) :=
  contDiff_arsinh.comp h

/--
@isnad1 id=contdiff.1h4v.s6.d9dfd34bd392 from=seed src=0 shape=070d3183 vocab=7d05d829
-/
@[fun_prop]
theorem ContDiffOn.arsinh (h : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => arsinh (f x)) s :=
  fun x hx => (h x hx).arsinh

end fderiv

section deriv

variable {f : ℝ → ℝ} {s : Set ℝ} {a f' : ℝ}

/--
@isnad1 id=hasstric.1h3v.s6.ca9e7f677d27 from=seed src=0 shape=88eb567d vocab=77704d99
-/
theorem HasStrictDerivAt.arsinh (hf : HasStrictDerivAt f f' a) :
    HasStrictDerivAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') a :=
  (hasStrictDerivAt_arsinh _).comp a hf

/--
@isnad1 id=hasderiv.1h3v.s6.0bf3ea3c8c1c from=seed src=0 shape=88eb567d vocab=f1c624f0
-/
theorem HasDerivAt.arsinh (hf : HasDerivAt f f' a) :
    HasDerivAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') a :=
  (hasDerivAt_arsinh _).comp a hf

/--
@isnad1 id=hasderiv.1h4v.s7.5ae18e65f228 from=seed src=0 shape=0fecf91d vocab=07af7d3c
-/
theorem HasDerivWithinAt.arsinh (hf : HasDerivWithinAt f f' s a) :
    HasDerivWithinAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') s a :=
  (hasDerivAt_arsinh _).comp_hasDerivWithinAt a hf

end deriv

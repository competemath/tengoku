/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Calculus.Deriv.Add
public import Tengoku.Seed.Analysis.InnerProductSpace.Calculus

/-!
# Derivative of the absolute value

This file compiles basic derivability properties of the absolute value, and is largely inspired from
`Mathlib/Analysis/InnerProductSpace/Calculus.lean`, which is the analogous file for norms derived
from an inner product space.

## Tags

absolute value, derivative
-/

public section

open Real Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ∞} {f : E → ℝ} {f' : StrongDual ℝ E} {s : Set E} {x : E}

/--
@isnad1 id=contdiff.1h2v.s5.533946f6fa7b from=seed src=0 shape=6011fa9c vocab=ca71bc21
-/
theorem contDiffAt_abs {x : ℝ} (hx : x ≠ 0) : ContDiffAt ℝ n (|·|) x := contDiffAt_norm ℝ hx

/--
@isnad1 id=contdiff.2h4v.s6.57fe23b938cd from=seed src=0 shape=75b81402 vocab=0ef7f541
-/
theorem ContDiffAt.abs (hf : ContDiffAt ℝ n f x) (h₀ : f x ≠ 0) :
    ContDiffAt ℝ n (fun x ↦ |f x|) x := hf.norm ℝ h₀

/--
@isnad1 id=contdiff.1h3v.s5.29b05af88d62 from=seed src=0 shape=9c184aab vocab=00fb8114
-/
theorem contDiffWithinAt_abs {x : ℝ} (hx : x ≠ 0) (s : Set ℝ) :
    ContDiffWithinAt ℝ n (|·|) s x := (contDiffAt_abs hx).contDiffWithinAt

/--
@isnad1 id=contdiff.2h5v.s6.c1128f7700ec from=seed src=0 shape=3a4dd802 vocab=233b0a1f
-/
theorem ContDiffWithinAt.abs (hf : ContDiffWithinAt ℝ n f s x) (h₀ : f x ≠ 0) :
    ContDiffWithinAt ℝ n (fun y ↦ |f y|) s x :=
  (contDiffAt_abs h₀).comp_contDiffWithinAt x hf

/--
@isnad1 id=contdiff.1h2v.s6.bf72974dfa0b from=seed src=0 shape=497c3591 vocab=4ddd8bc9
-/
theorem contDiffOn_abs {s : Set ℝ} (hs : ∀ x ∈ s, x ≠ 0) :
    ContDiffOn ℝ n (|·|) s := fun x hx ↦ contDiffWithinAt_abs (hs x hx) s

/--
@isnad1 id=contdiff.2h4v.s6.45535c18a519 from=seed src=0 shape=31231435 vocab=395c8b62
-/
theorem ContDiffOn.abs (hf : ContDiffOn ℝ n f s) (h₀ : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun y ↦ |f y|) s := fun x hx ↦ (hf x hx).abs (h₀ x hx)

/--
@isnad1 id=contdiff.2h3v.s6.d7b92c6fce14 from=seed src=0 shape=8aab6b8d vocab=b589be7f
-/
theorem ContDiff.abs (hf : ContDiff ℝ n f) (h₀ : ∀ x, f x ≠ 0) : ContDiff ℝ n fun y ↦ |f y| :=
  contDiff_iff_contDiffAt.2 fun x ↦ hf.contDiffAt.abs (h₀ x)

/--
@isnad1 id=hasstric.1h1v.s5.4fa08ff45e52 from=seed src=0 shape=6cdb2cbf vocab=3393f14e
-/
theorem hasStrictDerivAt_abs_neg {x : ℝ} (hx : x < 0) :
    HasStrictDerivAt (|·|) (-1) x :=
  (hasStrictDerivAt_neg x).congr_of_eventuallyEq <|
    EqOn.eventuallyEq_of_mem (fun _ hy ↦ (abs_of_neg (mem_Iio.1 hy)).symm) (Iio_mem_nhds hx)

/--
@isnad1 id=hasderiv.1h1v.s5.33d01ae5b7f9 from=seed src=0 shape=6cdb2cbf vocab=8d2e4a9c
-/
theorem hasDerivAt_abs_neg {x : ℝ} (hx : x < 0) :
    HasDerivAt (|·|) (-1) x := (hasStrictDerivAt_abs_neg hx).hasDerivAt

/--
@isnad1 id=hasstric.1h1v.s5.3446eb3d8e4b from=seed src=0 shape=7c376b05 vocab=dd7b6c59
-/
theorem hasStrictDerivAt_abs_pos {x : ℝ} (hx : 0 < x) :
    HasStrictDerivAt (|·|) 1 x :=
  (hasStrictDerivAt_id x).congr_of_eventuallyEq <|
    EqOn.eventuallyEq_of_mem (fun _ hy ↦ (abs_of_pos (mem_Iio.1 hy)).symm) (Ioi_mem_nhds hx)

/--
@isnad1 id=hasderiv.1h1v.s5.2dcbcd88205c from=seed src=0 shape=7c376b05 vocab=760933d4
-/
theorem hasDerivAt_abs_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt (|·|) 1 x := (hasStrictDerivAt_abs_pos hx).hasDerivAt

/--
@isnad1 id=hasstric.1h1v.s6.890ef703bd96 from=seed src=0 shape=55c21b16 vocab=836a6fe2
-/
theorem hasStrictDerivAt_abs {x : ℝ} (hx : x ≠ 0) :
    HasStrictDerivAt (|·|) (SignType.sign x : ℝ) x := by
  obtain hx | hx := hx.lt_or_gt
  · simpa [hx] using hasStrictDerivAt_abs_neg hx
  · simpa [hx] using hasStrictDerivAt_abs_pos hx

/--
@isnad1 id=hasderiv.1h1v.s6.3f8430780493 from=seed src=0 shape=55c21b16 vocab=3d661cc1
-/
theorem hasDerivAt_abs {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (|·|) (SignType.sign x : ℝ) x := (hasStrictDerivAt_abs hx).hasDerivAt

/--
@isnad1 id=hasstric.2h4v.s7.d579230d0d98 from=seed src=0 shape=03124e7d vocab=c103f394
-/
theorem HasStrictFDerivAt.abs_of_neg (hf : HasStrictFDerivAt f f' x)
    (h₀ : f x < 0) : HasStrictFDerivAt (fun x ↦ |f x|) (-f') x := by
  convert! (hasStrictDerivAt_abs_neg h₀).hasStrictFDerivAt.comp x hf using 1
  ext y
  simp

/--
@isnad1 id=hasfderi.2h4v.s7.a797e3dff952 from=seed src=0 shape=03124e7d vocab=e8ea4b9f
-/
theorem HasFDerivAt.abs_of_neg (hf : HasFDerivAt f f' x)
    (h₀ : f x < 0) : HasFDerivAt (fun x ↦ |f x|) (-f') x := by
  convert! (hasDerivAt_abs_neg h₀).hasFDerivAt.comp x hf using 1
  ext y
  simp

/--
@isnad1 id=hasstric.2h4v.s7.6c40fc7dfc5b from=seed src=0 shape=d8396d54 vocab=bf1167aa
-/
theorem HasStrictFDerivAt.abs_of_pos (hf : HasStrictFDerivAt f f' x)
    (h₀ : 0 < f x) : HasStrictFDerivAt (fun x ↦ |f x|) f' x := by
  convert! (hasStrictDerivAt_abs_pos h₀).hasStrictFDerivAt.comp x hf using 1
  ext y
  simp

/--
@isnad1 id=hasfderi.2h4v.s7.f23424b9578d from=seed src=0 shape=d8396d54 vocab=86324865
-/
theorem HasFDerivAt.abs_of_pos (hf : HasFDerivAt f f' x)
    (h₀ : 0 < f x) : HasFDerivAt (fun x ↦ |f x|) f' x := by
  convert! (hasDerivAt_abs_pos h₀).hasFDerivAt.comp x hf using 1
  ext y
  simp

/--
@isnad1 id=hasstric.2h4v.s8.c1fa2f586199 from=seed src=0 shape=4c6ff5aa vocab=18472ef7
-/
theorem HasStrictFDerivAt.abs (hf : HasStrictFDerivAt f f' x)
    (h₀ : f x ≠ 0) : HasStrictFDerivAt (fun x ↦ |f x|) ((SignType.sign (f x) : ℝ) • f') x := by
  convert! (hasStrictDerivAt_abs h₀).hasStrictFDerivAt.comp x hf using 1
  ext y
  simp [mul_comm]

/--
@isnad1 id=hasfderi.2h4v.s8.dc7dcd82ee47 from=seed src=0 shape=4c6ff5aa vocab=86ce808c
-/
theorem HasFDerivAt.abs (hf : HasFDerivAt f f' x)
    (h₀ : f x ≠ 0) : HasFDerivAt (fun x ↦ |f x|) ((SignType.sign (f x) : ℝ) • f') x := by
  convert! (hasDerivAt_abs h₀).hasFDerivAt.comp x hf using 1
  ext y
  simp [mul_comm]

/--
@isnad1 id=hasderiv.1h2v.s5.64ed53e34a5d from=seed src=0 shape=d0bc7a93 vocab=7da67159
-/
theorem hasDerivWithinAt_abs_neg (s : Set ℝ) {x : ℝ} (hx : x < 0) :
    HasDerivWithinAt (|·|) (-1) s x := (hasDerivAt_abs_neg hx).hasDerivWithinAt

/--
@isnad1 id=hasderiv.1h2v.s5.51bb2b393fd3 from=seed src=0 shape=c41beb20 vocab=a8d88eaf
-/
theorem hasDerivWithinAt_abs_pos (s : Set ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivWithinAt (|·|) 1 s x := (hasDerivAt_abs_pos hx).hasDerivWithinAt

/--
@isnad1 id=hasderiv.1h2v.s6.20bd9aa9efcb from=seed src=0 shape=03f2ac42 vocab=024f9c9a
-/
theorem hasDerivWithinAt_abs (s : Set ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivWithinAt (|·|) (SignType.sign x : ℝ) s x := (hasDerivAt_abs hx).hasDerivWithinAt

/--
@isnad1 id=hasfderi.2h5v.s7.e6fd00819342 from=seed src=0 shape=697c96e0 vocab=ac076805
-/
theorem HasFDerivWithinAt.abs_of_neg (hf : HasFDerivWithinAt f f' s x)
    (h₀ : f x < 0) : HasFDerivWithinAt (fun x ↦ |f x|) (-f') s x := by
  convert! (hasDerivAt_abs_neg h₀).comp_hasFDerivWithinAt x hf using 1
  simp

/--
@isnad1 id=hasfderi.2h5v.s7.5337c99462cb from=seed src=0 shape=002a4271 vocab=85452718
-/
theorem HasFDerivWithinAt.abs_of_pos (hf : HasFDerivWithinAt f f' s x)
    (h₀ : 0 < f x) : HasFDerivWithinAt (fun x ↦ |f x|) f' s x := by
  convert! (hasDerivAt_abs_pos h₀).comp_hasFDerivWithinAt x hf using 1
  simp

/--
@isnad1 id=hasfderi.2h5v.s8.848967726b2f from=seed src=0 shape=003dc718 vocab=d5a2e091
-/
theorem HasFDerivWithinAt.abs (hf : HasFDerivWithinAt f f' s x)
    (h₀ : f x ≠ 0) : HasFDerivWithinAt (fun x ↦ |f x|) ((SignType.sign (f x) : ℝ) • f') s x :=
  (hasDerivAt_abs h₀).comp_hasFDerivWithinAt x hf

/--
@isnad1 id=differen.1h1v.s6.f649ae862478 from=seed src=0 shape=51ad046d vocab=0509f81e
-/
theorem differentiableAt_abs_neg {x : ℝ} (hx : x < 0) :
    DifferentiableAt ℝ (|·|) x := (hasDerivAt_abs_neg hx).differentiableAt

/--
@isnad1 id=differen.1h1v.s6.6f24ec79ce06 from=seed src=0 shape=d00cf4ab vocab=0509f81e
-/
theorem differentiableAt_abs_pos {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (|·|) x := (hasDerivAt_abs_pos hx).differentiableAt

/--
@isnad1 id=differen.1h1v.s6.c9e048477645 from=seed src=0 shape=51ad046d vocab=aac02992
-/
theorem differentiableAt_abs {x : ℝ} (hx : x ≠ 0) :
    DifferentiableAt ℝ (|·|) x := (hasDerivAt_abs hx).differentiableAt

/--
@isnad1 id=differen.2h3v.s7.fd8674659b99 from=seed src=0 shape=0bd4d30a vocab=e3b5f0f2
-/
theorem DifferentiableAt.abs_of_neg (hf : DifferentiableAt ℝ f x) (h₀ : f x < 0) :
    DifferentiableAt ℝ (fun x ↦ |f x|) x := (differentiableAt_abs_neg h₀).comp x hf

/--
@isnad1 id=differen.2h3v.s7.47578eac7d0c from=seed src=0 shape=582f0e8c vocab=e3b5f0f2
-/
theorem DifferentiableAt.abs_of_pos (hf : DifferentiableAt ℝ f x) (h₀ : 0 < f x) :
    DifferentiableAt ℝ (fun x ↦ |f x|) x := (differentiableAt_abs_pos h₀).comp x hf

/--
@isnad1 id=differen.2h3v.s7.83b3f7f59392 from=seed src=0 shape=0bd4d30a vocab=89c3eec4
-/
theorem DifferentiableAt.abs (hf : DifferentiableAt ℝ f x) (h₀ : f x ≠ 0) :
    DifferentiableAt ℝ (fun x ↦ |f x|) x := (differentiableAt_abs h₀).comp x hf

/--
@isnad1 id=differen.1h2v.s6.2f72a28eadd9 from=seed src=0 shape=00afd683 vocab=023904c5
-/
theorem differentiableWithinAt_abs_neg (s : Set ℝ) {x : ℝ} (hx : x < 0) :
    DifferentiableWithinAt ℝ (|·|) s x := (differentiableAt_abs_neg hx).differentiableWithinAt

/--
@isnad1 id=differen.1h2v.s6.eda4005a7cf8 from=seed src=0 shape=a3864e8d vocab=023904c5
-/
theorem differentiableWithinAt_abs_pos (s : Set ℝ) {x : ℝ} (hx : 0 < x) :
    DifferentiableWithinAt ℝ (|·|) s x := (differentiableAt_abs_pos hx).differentiableWithinAt

/--
@isnad1 id=differen.1h2v.s6.65900c73ecd7 from=seed src=0 shape=00afd683 vocab=7b692b69
-/
theorem differentiableWithinAt_abs (s : Set ℝ) {x : ℝ} (hx : x ≠ 0) :
    DifferentiableWithinAt ℝ (|·|) s x := (differentiableAt_abs hx).differentiableWithinAt

/--
@isnad1 id=differen.2h4v.s7.a865298b470c from=seed src=0 shape=688f723a vocab=d0d0edee
-/
theorem DifferentiableWithinAt.abs_of_neg (hf : DifferentiableWithinAt ℝ f s x) (h₀ : f x < 0) :
    DifferentiableWithinAt ℝ (fun x ↦ |f x|) s x :=
  (differentiableAt_abs_neg h₀).comp_differentiableWithinAt x hf

/--
@isnad1 id=differen.2h4v.s7.3dea2a9f2abc from=seed src=0 shape=fd6cbb30 vocab=d0d0edee
-/
theorem DifferentiableWithinAt.abs_of_pos (hf : DifferentiableWithinAt ℝ f s x) (h₀ : 0 < f x) :
    DifferentiableWithinAt ℝ (fun x ↦ |f x|) s x :=
  (differentiableAt_abs_pos h₀).comp_differentiableWithinAt x hf

/--
@isnad1 id=differen.2h4v.s7.5b19d559cff5 from=seed src=0 shape=688f723a vocab=4a3b6c81
-/
theorem DifferentiableWithinAt.abs (hf : DifferentiableWithinAt ℝ f s x) (h₀ : f x ≠ 0) :
    DifferentiableWithinAt ℝ (fun x ↦ |f x|) s x :=
  (differentiableAt_abs h₀).comp_differentiableWithinAt x hf

/--
@isnad1 id=differen.1h1v.s6.4cae345760e5 from=seed src=0 shape=f8b0559c vocab=58b55570
-/
theorem differentiableOn_abs {s : Set ℝ} (hs : ∀ x ∈ s, x ≠ 0) : DifferentiableOn ℝ (|·|) s :=
  fun x hx ↦ differentiableWithinAt_abs s (hs x hx)

/--
@isnad1 id=differen.2h3v.s7.b2882c55bb68 from=seed src=0 shape=8595ece1 vocab=10390e66
-/
theorem DifferentiableOn.abs (hf : DifferentiableOn ℝ f s) (h₀ : ∀ x ∈ s, f x ≠ 0) :
    DifferentiableOn ℝ (fun x ↦ |f x|) s :=
  fun x hx ↦ (hf x hx).abs (h₀ x hx)

/--
@isnad1 id=differen.2h2v.s7.eb59f59c50b4 from=seed src=0 shape=7b014985 vocab=b1c3e937
-/
theorem Differentiable.abs (hf : Differentiable ℝ f) (h₀ : ∀ x, f x ≠ 0) :
    Differentiable ℝ (fun x ↦ |f x|) := fun x ↦ (hf x).abs (h₀ x)

/--
@isnad1 id=not.0h0v.s5.a6c1252c14b7 from=seed src=0 shape=ea1cdf93 vocab=aac02992
-/
theorem not_differentiableAt_abs_zero : ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 := by
  intro h
  have h₁ : deriv abs (0 : ℝ) = 1 :=
    (uniqueDiffOn_Ici _ _ Set.self_mem_Ici).eq_deriv _ h.hasDerivAt.hasDerivWithinAt <|
      (hasDerivWithinAt_id _ _).congr_of_mem (fun _ h ↦ abs_of_nonneg h) Set.self_mem_Ici
  have h₂ : deriv abs (0 : ℝ) = -1 :=
    (uniqueDiffOn_Iic _ _ Set.self_mem_Iic).eq_deriv _ h.hasDerivAt.hasDerivWithinAt <|
      (hasDerivWithinAt_neg _ _).congr_of_mem (fun _ h ↦ abs_of_nonpos h) Set.self_mem_Iic
  linarith

/--
@isnad1 id=eq.1h1v.s5.ac3ff4c0433a from=seed src=0 shape=f2f68604 vocab=6d64fc6d
-/
theorem deriv_abs_neg {x : ℝ} (hx : x < 0) : deriv (|·|) x = -1 := (hasDerivAt_abs_neg hx).deriv

/--
@isnad1 id=eq.1h1v.s5.73b6dabe9bf5 from=seed src=0 shape=38f57b2e vocab=c66e67db
-/
theorem deriv_abs_pos {x : ℝ} (hx : 0 < x) : deriv (|·|) x = 1 := (hasDerivAt_abs_pos hx).deriv

/--
@isnad1 id=eq.0h0v.s5.f848ea7e1e02 from=seed src=0 shape=34eac94b vocab=617e2a6b
-/
theorem deriv_abs_zero : deriv (|·|) (0 : ℝ) = 0 :=
  deriv_zero_of_not_differentiableAt not_differentiableAt_abs_zero

/--
@isnad1 id=eq.0h1v.s6.92f64d20aeab from=seed src=0 shape=f3eed4ee vocab=6774fcd1
-/
theorem deriv_abs (x : ℝ) : deriv (|·|) x = SignType.sign x := by
  obtain rfl | hx := eq_or_ne x 0
  · simpa using deriv_abs_zero
  · simpa [hx] using (hasDerivAt_abs hx).deriv

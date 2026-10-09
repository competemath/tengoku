/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-! # Interactions of the continuous functional calculus with the real and imaginary part -/

public section

open Complex ComplexStarModule

variable {A : Type*} [TopologicalSpace A]

section NonUnital

variable [NonUnitalRing A] [StarRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [StarModule ℂ A] [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal]

/--
@isnad1 id=eq.0h3v.s10.dc7de95e2447 from=seed src=0 shape=67979e4a vocab=ce432c21
-/
lemma cfcₙ_re_id (a : A) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ (re · : ℂ → ℂ) a = ℜ a := by
  conv_rhs => rw [realPart_apply_coe, ← cfcₙ_id' ℂ a, ← cfcₙ_star, ← cfcₙ_add .., ← cfcₙ_smul ..]
  refine cfcₙ_congr fun x hx ↦ ?_
  rw [Complex.re_eq_add_conj, ← smul_one_smul ℂ 2⁻¹]
  simp [div_eq_inv_mul]

/--
@isnad1 id=eq.0h3v.s10.cd9e11c3fffc from=seed src=0 shape=67979e4a vocab=938a72e6
-/
lemma cfcₙ_im_id (a : A) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ (im · : ℂ → ℂ) a = ℑ a := by
  suffices cfcₙ (fun z : ℂ ↦ re z + I * im z) a = ℜ a + I • ℑ a by
    rw [cfcₙ_add .., cfcₙ_const_mul .., cfcₙ_re_id a] at this
    simpa
  simp [mul_comm I, re_add_im, cfcₙ_id' .., realPart_add_I_smul_imaginaryPart]

/--
@isnad1 id=eq.0h3v.s10.35cd0e429513 from=seed src=0 shape=2926ab17 vocab=a656db59
-/
lemma quasispectrum_realPart (a : A) (ha : IsStarNormal a := by cfc_tac) :
    quasispectrum ℂ (ℜ a : A) = (fun x ↦ (re x : ℂ)) '' (quasispectrum ℂ a) := by
  rw [← cfcₙ_re_id a, cfcₙ_map_quasispectrum ..]

-- fails to find `IsScalarTower ℝ ℂ A`.
/--
@isnad1 id=eq.0h3v.s10.f093044c30c0 from=seed src=0 shape=339b2da2 vocab=e6f8e98f
-/
lemma quasispectrum_realPart' (a : A) (ha : IsStarNormal a := by cfc_tac) :
    quasispectrum ℝ (ℜ a : A) = re '' (quasispectrum ℂ a) := by
  simp [← (ℜ a).2.quasispectrumRestricts.image, quasispectrum_realPart a, Set.image_image]

/--
@isnad1 id=eq.0h3v.s10.e54b682a4e3f from=seed src=0 shape=2926ab17 vocab=9e5b082c
-/
lemma quasispectrum_imaginaryPart (a : A) (ha : IsStarNormal a := by cfc_tac) :
    quasispectrum ℂ (ℑ a : A) = (fun x ↦ (im x : ℂ)) '' (quasispectrum ℂ a) := by
  rw [← cfcₙ_im_id a, cfcₙ_map_quasispectrum ..]

-- fails to find `IsScalarTower ℝ ℂ A`.
/--
@isnad1 id=eq.0h3v.s10.e5fc35d668f6 from=seed src=0 shape=339b2da2 vocab=babe0a3a
-/
lemma quasispectrum_imaginaryPart' (a : A) (ha : IsStarNormal a := by cfc_tac) :
    quasispectrum ℝ (ℑ a : A) = im '' (quasispectrum ℂ a) := by
  simp [← (ℑ a).2.quasispectrumRestricts.image, quasispectrum_imaginaryPart a, Set.image_image]

variable [ContinuousMapZero.UniqueHom ℂ A]

/--
@isnad1 id=eq.0h6v.s10.a70f968cb97f from=seed src=0 shape=d42e8eb8 vocab=c8fc7cd1
-/
lemma cfcₙ_realPart (f : ℂ → ℂ) (a : A)
    (hf : ContinuousOn f (quasispectrum ℂ (ℜ a : A)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ f (ℜ a : A) = cfcₙ (fun x ↦ f (re x)) a := by
  rw [quasispectrum_realPart a] at hf
  rw [← cfcₙ_re_id a, ← cfcₙ_comp' ..]

/--
@isnad1 id=eq.0h6v.s10.e6c1df427117 from=seed src=0 shape=d42e8eb8 vocab=b9ed0336
-/
lemma cfcₙ_imaginaryPart (f : ℂ → ℂ) (a : A)
    (hf : ContinuousOn f (quasispectrum ℂ (ℑ a : A)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ f (ℑ a : A) = cfcₙ (fun x ↦ f (im x)) a := by
  rw [quasispectrum_imaginaryPart a] at hf
  rw [← cfcₙ_im_id a, ← cfcₙ_comp' ..]

variable [T2Space A]

/--
@isnad1 id=eq.0h6v.s10.083474e51d85 from=seed src=0 shape=e6bc86bb vocab=b931a7f4
-/
lemma cfcₙ_comp_re (f : ℝ → ℝ) (a : A)
    (hf : ContinuousOn f (quasispectrum ℝ (ℜ a : A)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ (fun x : ℂ ↦ f (re x)) a = cfcₙ f (ℜ a : A) := by
  have : ContinuousOn (fun x ↦ (f x.re) : ℂ → ℂ) ((re · : ℂ → ℂ) '' quasispectrum ℂ a) := by
    rw [quasispectrum_realPart' a] at hf
    refine continuous_ofReal.comp_continuousOn <| hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.mapsTo_image ..
  conv_rhs =>
    rw [cfcₙ_real_eq_complex, ← cfcₙ_re_id a, ← cfcₙ_comp' ..]
    simp

/--
@isnad1 id=eq.0h6v.s10.7ab7cf62d7ca from=seed src=0 shape=e6bc86bb vocab=64460a14
-/
lemma cfcₙ_comp_im (f : ℝ → ℝ) (a : A)
    (hf : ContinuousOn f (quasispectrum ℝ (ℑ a : A)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ (fun x : ℂ ↦ f (im x)) a = cfcₙ f (ℑ a : A) := by
  have : ContinuousOn (fun x ↦ (f x.re) : ℂ → ℂ) ((im · : ℂ → ℂ) '' quasispectrum ℂ a) := by
    rw [quasispectrum_imaginaryPart' a] at hf
    refine continuous_ofReal.comp_continuousOn <| hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.mapsTo_image ..
  conv_rhs =>
    rw [cfcₙ_real_eq_complex, ← cfcₙ_im_id a, ← cfcₙ_comp' ..]
    simp

end NonUnital

section Unital

variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  [ContinuousFunctionalCalculus ℂ A IsStarNormal]

/--
@isnad1 id=eq.0h3v.s9.505629b9064c from=seed src=0 shape=1ee238d1 vocab=0215835b
-/
lemma cfc_re_id (a : A) (hp : IsStarNormal a := by cfc_tac) :
    cfc (re · : ℂ → ℂ) a = ℜ a := by
  conv_rhs => rw [realPart_apply_coe, ← cfc_id' ℂ a, ← cfc_star, ← cfc_add .., ← cfc_smul ..]
  refine cfc_congr fun x hx ↦ ?_
  rw [Complex.re_eq_add_conj, ← smul_one_smul ℂ 2⁻¹]
  simp [div_eq_inv_mul]

/--
@isnad1 id=eq.0h3v.s9.9d65a875ffe6 from=seed src=0 shape=1ee238d1 vocab=469400b5
-/
lemma cfc_im_id (a : A) (hp : IsStarNormal a := by cfc_tac) :
    cfc (im · : ℂ → ℂ) a = ℑ a := by
  suffices cfc (fun z : ℂ ↦ re z + I * im z) a = ℜ a + I • ℑ a by
    rw [cfc_add .., cfc_const_mul .., cfc_re_id a] at this
    simpa
  simp [mul_comm I, re_add_im, cfc_id' .., realPart_add_I_smul_imaginaryPart]

/--
@isnad1 id=eq.0h3v.s9.cb2b7ec15d1f from=seed src=0 shape=5c589017 vocab=d7765ad1
-/
lemma spectrum_realPart (a : A) (ha : IsStarNormal a := by cfc_tac) :
    spectrum ℂ (ℜ a : A) = (fun x ↦ (re x : ℂ)) '' (spectrum ℂ a) := by
  rw [← cfc_re_id a, cfc_map_spectrum ..]

/--
@isnad1 id=eq.0h3v.s9.de9868e7a24e from=seed src=0 shape=c9cde131 vocab=ee3d221e
-/
lemma spectrum_realPart' (a : A) (ha : IsStarNormal a := by cfc_tac) :
    spectrum ℝ (ℜ a : A) = re '' (spectrum ℂ a) := by
  simp [← (ℜ a).2.spectrumRestricts.image, spectrum_realPart a, Set.image_image]

/--
@isnad1 id=eq.0h3v.s9.31822fa4734c from=seed src=0 shape=5c589017 vocab=760b202a
-/
lemma spectrum_imaginaryPart (a : A) (ha : IsStarNormal a := by cfc_tac) :
    spectrum ℂ (ℑ a : A) = (fun x ↦ (im x : ℂ)) '' (spectrum ℂ a) := by
  rw [← cfc_im_id a, cfc_map_spectrum ..]

/--
@isnad1 id=eq.0h3v.s9.f1f4c091733f from=seed src=0 shape=c9cde131 vocab=8f9b0668
-/
lemma spectrum_imaginaryPart' (a : A) (ha : IsStarNormal a := by cfc_tac) :
    spectrum ℝ (ℑ a : A) = im '' (spectrum ℂ a) := by
  simp [← (ℑ a).2.spectrumRestricts.image, spectrum_imaginaryPart a, Set.image_image]

variable [ContinuousMap.UniqueHom ℂ A]

/--
@isnad1 id=eq.0h5v.s10.25472f073125 from=seed src=0 shape=18f6ecf6 vocab=66374044
-/
lemma cfc_realPart (f : ℂ → ℂ) (a : A) (hf : ContinuousOn f (spectrum ℂ (ℜ a : A)) := by cfc_tac)
    (ha : IsStarNormal a := by cfc_tac) :
    cfc f (ℜ a : A) = cfc (fun x ↦ f (re x)) a := by
  rw [spectrum_realPart a] at hf
  rw [← cfc_re_id a, ← cfc_comp' ..]

/--
@isnad1 id=eq.0h5v.s10.c112d26e953b from=seed src=0 shape=18f6ecf6 vocab=aae0d630
-/
lemma cfc_imaginaryPart (f : ℂ → ℂ) (a : A)
    (hf : ContinuousOn f (spectrum ℂ (ℑ a : A)) := by cfc_tac)
    (ha : IsStarNormal a := by cfc_tac) :
    cfc f (ℑ a : A) = cfc (fun x ↦ f (im x)) a := by
  rw [spectrum_imaginaryPart a] at hf
  rw [← cfc_im_id a, ← cfc_comp' ..]

variable [T2Space A]

/--
@isnad1 id=eq.0h5v.s10.82d09d1bd943 from=seed src=0 shape=84625781 vocab=8df78826
-/
lemma cfc_comp_re (f : ℝ → ℝ) (a : A)
    (hf : ContinuousOn f (spectrum ℝ (ℜ a : A)) := by cfc_tac)
    (ha : IsStarNormal a := by cfc_tac) :
    cfc (fun x : ℂ ↦ f (re x)) a = cfc f (ℜ a : A) := by
  have : ContinuousOn (fun x ↦ (f x.re) : ℂ → ℂ) ((re · : ℂ → ℂ) '' spectrum ℂ a) := by
    rw [spectrum_realPart' a] at hf
    refine continuous_ofReal.comp_continuousOn <| hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.mapsTo_image ..
  conv_rhs =>
    rw [cfc_real_eq_complex, ← cfc_re_id a, ← cfc_comp' ..]
    simp

/--
@isnad1 id=eq.1h4v.s10.8b455e0aef2c from=seed src=0 shape=be96ede6 vocab=6fc7bf4a
-/
lemma cfc_comp_im (f : ℝ → ℝ) (a : A) (hf : ContinuousOn f (spectrum ℝ (ℑ a : A)))
    (ha : IsStarNormal a := by cfc_tac) :
    cfc (fun x : ℂ ↦ f (im x)) a = cfc f (ℑ a : A) := by
  have : ContinuousOn (fun x ↦ (f x.re) : ℂ → ℂ) ((im · : ℂ → ℂ) '' spectrum ℂ a) := by
    rw [spectrum_imaginaryPart' a] at hf
    refine continuous_ofReal.comp_continuousOn <| hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.mapsTo_image ..
  conv_rhs =>
    rw [cfc_real_eq_complex, ← cfc_im_id a, ← cfc_comp' ..]
    simp

end Unital

/-
Adapted from PrimeNumberTheoremAnd by Alex Kontorovich and contributors.
Licensed under the Apache License, Version 2.0; see the upstream LICENSE.
This compatibility port retains the proven declarations used by this project.
-/
import Tengoku.Seed.Topology.ContinuousMap.Bounded.Basic
import Tengoku.Seed.Analysis.Fourier.FourierTransformDeriv
import Tengoku.QuasiRiemann.PrimeNumberTheoremAnd.Sobolev

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.QuasiRiemann end Tengoku.QuasiRiemann open Tengoku.QuasiRiemann
open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

section lemmas

/--
@isnad1 id=eq.0h2v.s6.a58700f78571 from=translated src=- shape=05dd30d2 vocab=d7c4ecc7
-/
@[simp] theorem _root_.Tengoku.QuasiRiemann.F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

/--
@isnad1 id=eq.2h3v.s7.7df4670bf119 from=translated src=- shape=fe75e4ea vocab=094613bf
-/
@[simp] theorem _root_.Tengoku.QuasiRiemann.F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  exact congr_fun (fourierIntegral_add continuous_fourierChar continuous_inner hf hg) x

/--
@isnad1 id=eq.2h3v.s7.b4f493763f26 from=translated src=- shape=fe75e4ea vocab=23f75e69
-/
@[simp] theorem _root_.Tengoku.QuasiRiemann.F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

/--
@isnad1 id=eq.0h3v.s6.d3d6175992ca from=translated src=- shape=2f75aeda vocab=acba9ad2
-/
@[simp] theorem _root_.Tengoku.QuasiRiemann.F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas

/--
@isnad1 id=eq.0h2v.s8.686659ef4e25 from=translated src=- shape=ab29156b vocab=4cd90dc9
-/
theorem _root_.Tengoku.QuasiRiemann.fourierIntegral_self_add_deriv_deriv (f : W21) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 (f : ℝ → ℂ) u =
      𝓕 (fun u : ℝ => (f u - (1 / (4 * π ^ 2)) * deriv^[2] f u : ℂ)) u := by
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
    apply Integrable.const_mul ; simpa [iteratedDeriv_succ] using f.integrable le_rfl
  have l4 : Differentiable ℝ f := f.differentiable
  have l5 : Differentiable ℝ (deriv f) := f.deriv.differentiable
  simp [f.hf, l1, add_mul, Real.fourier_deriv f.hf' l5 f.hf'', Real.fourier_deriv f.hf l4 f.hf']
  field_simp [pi_ne_zero] ; ring_nf ; simp

/--
@isnad1 id=eq.0h0v.s6.7a1f5e3bc900 from=translated src=- shape=dcdef0ad vocab=f2ab5641
-/
@[simp] theorem _root_.Tengoku.QuasiRiemann.deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv
-- Tengoku: root names of this library moved to Tengoku.QuasiRiemann so they do not collide with other libraries (generated)

import Tengoku.Leancert.LeanCert.Analysis.DBN.HeatKernel
import Tengoku.Seed.NumberTheory.LSeries.HurwitzZetaEven
import Tengoku.Seed.Analysis.Complex.RealDeriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The theta primitive for the DBN integral

This connects the positive-index exponential series to Mathlib's theta kernel.
The symmetrized lift is even, which fixes the nonzero endpoint derivative
of the primitive. No xi integral identity or zero-strip theorem is assumed.
-/

namespace LeanCert.Analysis.DBN
open HurwitzZeta

/-- A summand of the theta primitive, with the same positive-index convention as `Phi`. -/
noncomputable def thetaTerm (u : ℝ) (n : ℕ) : ℝ :=
  Real.exp u * Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * Real.exp (4*u))

/-- The theta primitive `exp u * sum (exp (-pi*n^2*exp(4*u)))`. -/
noncomputable def thetaPrimitive (u : ℝ) : ℝ :=
  Real.exp u * (cosKernel 0 (Real.exp (4*u)) - 1) / 2

/-- The full symmetrized theta lift, including the constant theta term. -/
noncomputable def thetaLift (u : ℝ) : ℝ :=
  Real.exp u * cosKernel 0 (Real.exp (4*u))

/--
@isnad1 id=hassum.0h1v.s4.73860c7f2590 from=translated src=- shape=a3943c8c vocab=bd4f78e5
-/
theorem hasSum_thetaTerm (u : ℝ) : HasSum (thetaTerm u) (thetaPrimitive u) := by
  have h := (hasSum_nat_cosKernel₀ 0 (Real.exp_pos (4*u))).div_const 2
  have h' : HasSum (fun n : ℕ => Real.exp
      (-Real.pi * ((n : ℝ)+1)^2 * Real.exp (4*u)))
      ((cosKernel 0 (Real.exp (4*u)) - 1)/2) := by
    simpa using h
  change HasSum (fun n => thetaTerm u n) (thetaPrimitive u)
  simpa [thetaTerm, thetaPrimitive, mul_div_assoc] using h'.mul_left (Real.exp u)

/--
@isnad1 id=eq.0h1v.s4.0e1286395067 from=translated src=- shape=695f06d6 vocab=50bc0efb
-/
theorem thetaPrimitive_eq_tsum (u : ℝ) : thetaPrimitive u = ∑' n, thetaTerm u n :=
  (hasSum_thetaTerm u).tsum_eq.symm

/--
@isnad1 id=eq.0h1v.s5.8f6e4fc0524a from=translated src=- shape=0f46a4e6 vocab=f904102e
-/
theorem thetaLift_eq (u : ℝ) : thetaLift u = Real.exp u + 2 * thetaPrimitive u := by
  unfold thetaLift thetaPrimitive
  ring

/-- Theta inversion becomes reflection after the logarithmic change of variables.
@isnad1 id=eq.0h1v.s3.88ff26f125d1 from=translated src=- shape=cd419dad vocab=e506b0c9
-/
theorem thetaLift_even (u : ℝ) : thetaLift (-u) = thetaLift u := by
  have h := evenKernel_functional_equation 0 (Real.exp (4*u))
  rw [evenKernel_eq_cosKernel_of_zero] at h
  have hp : Real.exp (4*u) ^ (1/2 : ℝ) = Real.exp (2*u) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [hp, one_div, ← Real.exp_neg, one_div, ← Real.exp_neg] at h
  unfold thetaLift
  rw [h]
  have he : Real.exp u * Real.exp (-(2*u)) = Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, he]
  rw [mul_neg]

private theorem differentiableAt_cosKernel_zero {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (cosKernel 0) x := by
  have h : DifferentiableAt ℂ (fun w : ℂ => jacobiTheta₂ 0 (Complex.I * w))
      (x : ℂ) :=
    (differentiableAt_jacobiTheta₂_snd 0 (by simpa using hx)).comp _
      (differentiableAt_const _ |>.mul differentiableAt_id)
  have he : (fun y : ℝ => (jacobiTheta₂ 0 (Complex.I * (y : ℂ))).re) =
      cosKernel 0 := by
    funext y
    have hh := cosKernel_def 0 y
    simpa using congrArg Complex.re hh.symm
  rw [← he]
  exact h.hasDerivAt.real_of_complex.differentiableAt

/--
@isnad1 id=differen.0h0v.s5.93db5da45236 from=translated src=- shape=aa9fb30a vocab=08240a7e
-/
theorem differentiable_thetaLift : Differentiable ℝ thetaLift := by
  intro u
  apply Real.differentiableAt_exp.mul
  exact (differentiableAt_cosKernel_zero (Real.exp_pos (4*u))).comp u (by fun_prop)

/--
@isnad1 id=differen.0h0v.s5.a9184f613a78 from=translated src=- shape=aa9fb30a vocab=17602071
-/
theorem differentiable_thetaPrimitive : Differentiable ℝ thetaPrimitive := by
  have he : thetaPrimitive = fun u => (thetaLift u - Real.exp u) / 2 := by
    funext u
    rw [thetaLift_eq]
    ring
  rw [he]
  exact (differentiable_thetaLift.sub Real.differentiable_exp).div_const 2

/-- Evenness forces the full lift to have zero derivative at the origin.
@isnad1 id=hasderiv.0h0v.s5.48c46e0ecd3b from=translated src=- shape=c9cd68ae vocab=a46cc29f
-/
theorem hasDerivAt_thetaLift_zero : HasDerivAt thetaLift 0 0 := by
  have h := (differentiable_thetaLift 0).hasDerivAt
  have h0 : HasDerivAt thetaLift (deriv thetaLift 0) (-0) := by simpa using h
  have hn := h0.comp 0 (hasDerivAt_neg (0 : ℝ))
  have he : (fun x => thetaLift (-x)) = thetaLift := funext thetaLift_even
  change HasDerivAt (fun x => thetaLift (-x)) (deriv thetaLift 0 * -1) 0 at hn
  rw [he, mul_neg_one] at hn
  have hd := h.unique hn
  have hz : deriv thetaLift 0 = 0 := by linarith
  simpa [hz] using h

/-- The endpoint term needed in the twice-integrated DBN cosine transform.
@isnad1 id=hasderiv.0h0v.s5.c421a8d74706 from=translated src=- shape=9abcc922 vocab=60913667
-/
theorem hasDerivAt_thetaPrimitive_zero : HasDerivAt thetaPrimitive (-1/2) 0 := by
  have he : thetaPrimitive = fun u => (thetaLift u - Real.exp u) / 2 := by
    funext u
    rw [thetaLift_eq]
    ring
  rw [he]
  simpa using (hasDerivAt_thetaLift_zero.sub (Real.hasDerivAt_exp 0)).div_const 2

end LeanCert.Analysis.DBN

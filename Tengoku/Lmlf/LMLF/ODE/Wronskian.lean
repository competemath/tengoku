import Tengoku.Seed.Analysis.Calculus.MeanValue
import Tengoku.Lmlf.LMLF.ODE.LinearFirstOrder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Wronskians for second-order ordinary differential equations

Abel's identity for complex-valued solutions of a second-order ODE with real
independent variable, together with its real-valued specialization.
-/

open MeasureTheory Set
open scoped Interval

namespace LMLF.ODE

/-- The pointwise Wronskian determinant of two phase pairs.-/
def wronskian {X R : Type*} [Mul R] [Sub R]
    (y₁ v₁ y₂ v₂ : X → R) (x : X) : R :=
  y₁ x * v₂ x - y₂ x * v₁ x

/-- Compatibility name for the Wronskian of two real-valued phase pairs.-/
abbrev realWronskian (y₁ v₁ y₂ v₂ : ℝ → ℝ) (x : ℝ) : ℝ :=
  wronskian y₁ v₁ y₂ v₂ x

/-- A1: the Wronskian of two complex phase-pair solutions satisfies `W' = -f W`.
@isnad1 id=hasderiv.5h8v.s8.6fb65e3baa08 from=translated src=- shape=24db7f28 vocab=467b7f43
-/
theorem hasDerivAt_wronskian {I : Set ℝ} {f g y₁ v₁ y₂ v₂ : ℝ → ℂ} {x : ℝ}
    (hx : x ∈ I)
    (hy₁ : ∀ z ∈ I, HasDerivAt y₁ (v₁ z) z)
    (hv₁ : ∀ z ∈ I, HasDerivAt v₁ (-f z * v₁ z - g z * y₁ z) z)
    (hy₂ : ∀ z ∈ I, HasDerivAt y₂ (v₂ z) z)
    (hv₂ : ∀ z ∈ I, HasDerivAt v₂ (-f z * v₂ z - g z * y₂ z) z) :
    HasDerivAt (wronskian y₁ v₁ y₂ v₂)
      (-f x * wronskian y₁ v₁ y₂ v₂ x) x := by
  have h := ((hy₁ x hx).mul (hv₂ x hx)).sub ((hy₂ x hx).mul (hv₁ x hx))
  exact h.congr_deriv (by simp only [wronskian]; ring)

/-- A2: Abel's basepoint formula for complex-valued solutions.
@isnad1 id=eq.9h9v.s8.e27094f571c6 from=translated src=- shape=e3fbe5bc vocab=f9d93eaa
-/
theorem wronskian_eq_mul_cexp_integral {I : Set ℝ} {f g y₁ v₁ y₂ v₂ : ℝ → ℂ}
    (hI : IsOpen I) (hIc : IsPreconnected I) (hf : ContinuousOn f I)
    (hy₁ : ∀ z ∈ I, HasDerivAt y₁ (v₁ z) z)
    (hv₁ : ∀ z ∈ I, HasDerivAt v₁ (-f z * v₁ z - g z * y₁ z) z)
    (hy₂ : ∀ z ∈ I, HasDerivAt y₂ (v₂ z) z)
    (hv₂ : ∀ z ∈ I, HasDerivAt v₂ (-f z * v₂ z - g z * y₂ z) z)
    {x₀ x : ℝ} (hx₀ : x₀ ∈ I) (hx : x ∈ I) :
    wronskian y₁ v₁ y₂ v₂ x = wronskian y₁ v₁ y₂ v₂ x₀ *
      Complex.exp (-∫ t in x₀..x, f t) := by
  exact eqOn_const_mul_cexp_neg_integral_of_hasDerivAt hI hIc hf
    (fun z hz ↦ hasDerivAt_wronskian hz hy₁ hv₁ hy₂ hv₂) hx₀ hx

/-- A3, pointwise form: a complex Wronskian vanishes at one point iff it vanishes at another.
@isnad1 id=iff.9h9v.s8.fec1bddf479a from=translated src=- shape=dbf784d1 vocab=d5c4dfc6
-/
theorem wronskian_eq_zero_iff {I : Set ℝ} {f g y₁ v₁ y₂ v₂ : ℝ → ℂ}
    (hI : IsOpen I) (hIc : IsPreconnected I) (hf : ContinuousOn f I)
    (hy₁ : ∀ z ∈ I, HasDerivAt y₁ (v₁ z) z)
    (hv₁ : ∀ z ∈ I, HasDerivAt v₁ (-f z * v₁ z - g z * y₁ z) z)
    (hy₂ : ∀ z ∈ I, HasDerivAt y₂ (v₂ z) z)
    (hv₂ : ∀ z ∈ I, HasDerivAt v₂ (-f z * v₂ z - g z * y₂ z) z)
    {x₀ x : ℝ} (hx₀ : x₀ ∈ I) (hx : x ∈ I) :
    wronskian y₁ v₁ y₂ v₂ x = 0 ↔ wronskian y₁ v₁ y₂ v₂ x₀ = 0 := by
  rw [wronskian_eq_mul_cexp_integral hI hIc hf hy₁ hv₁ hy₂ hv₂ hx₀ hx,
    mul_eq_zero]
  simp [Complex.exp_ne_zero]

/-- A3: a complex Wronskian is identically zero or nowhere zero on a nonempty interval.
@isnad1 id=or.8h7v.s8.9ca48e1527ed from=translated src=- shape=9cd9eb55 vocab=79b381ff
-/
theorem wronskian_zero_or_nowhere_zero {I : Set ℝ} {f g y₁ v₁ y₂ v₂ : ℝ → ℂ}
    (hIne : I.Nonempty) (hI : IsOpen I) (hIc : IsPreconnected I) (hf : ContinuousOn f I)
    (hy₁ : ∀ z ∈ I, HasDerivAt y₁ (v₁ z) z)
    (hv₁ : ∀ z ∈ I, HasDerivAt v₁ (-f z * v₁ z - g z * y₁ z) z)
    (hy₂ : ∀ z ∈ I, HasDerivAt y₂ (v₂ z) z)
    (hv₂ : ∀ z ∈ I, HasDerivAt v₂ (-f z * v₂ z - g z * y₂ z) z) :
    (∀ x ∈ I, wronskian y₁ v₁ y₂ v₂ x = 0) ∨
      (∀ x ∈ I, wronskian y₁ v₁ y₂ v₂ x ≠ 0) := by
  obtain ⟨x₀, hx₀⟩ := hIne
  by_cases hzero : wronskian y₁ v₁ y₂ v₂ x₀ = 0
  · left
    intro x hx
    exact (wronskian_eq_zero_iff hI hIc hf hy₁ hv₁ hy₂ hv₂ hx₀ hx).2 hzero
  · right
    intro x hx hxzero
    exact hzero ((wronskian_eq_zero_iff hI hIc hf hy₁ hv₁ hy₂ hv₂ hx₀ hx).1 hxzero)

/-- A3, exclusive form: exactly one complex Wronskian alternative holds.
@isnad1 id=xor.8h7v.s8.6c0e3c50f073 from=translated src=- shape=9cd9eb55 vocab=98ed8404
-/
theorem wronskian_zero_xor_nowhere_zero {I : Set ℝ} {f g y₁ v₁ y₂ v₂ : ℝ → ℂ}
    (hIne : I.Nonempty) (hI : IsOpen I) (hIc : IsPreconnected I) (hf : ContinuousOn f I)
    (hy₁ : ∀ z ∈ I, HasDerivAt y₁ (v₁ z) z)
    (hv₁ : ∀ z ∈ I, HasDerivAt v₁ (-f z * v₁ z - g z * y₁ z) z)
    (hy₂ : ∀ z ∈ I, HasDerivAt y₂ (v₂ z) z)
    (hv₂ : ∀ z ∈ I, HasDerivAt v₂ (-f z * v₂ z - g z * y₂ z) z) :
    Xor (∀ x ∈ I, wronskian y₁ v₁ y₂ v₂ x = 0)
      (∀ x ∈ I, wronskian y₁ v₁ y₂ v₂ x ≠ 0) := by
  rcases wronskian_zero_or_nowhere_zero hIne hI hIc hf hy₁ hv₁ hy₂ hv₂ with hzero | hne
  · left
    refine ⟨hzero, ?_⟩
    intro hnowhere
    obtain ⟨x, hx⟩ := hIne
    exact hnowhere x hx (hzero x hx)
  · right
    refine ⟨hne, ?_⟩
    intro hzero
    obtain ⟨x, hx⟩ := hIne
    exact hne x hx (hzero x hx)

/-- A4: if the first-derivative coefficient vanishes, the complex Wronskian is constant.
@isnad1 id=eq.9h9v.s8.503c4e0b9bf7 from=translated src=- shape=17fdcb54 vocab=7d361ed0
-/
theorem wronskian_eq_of_f_eq_zero {I : Set ℝ} {f g y₁ v₁ y₂ v₂ : ℝ → ℂ}
    (hI : IsOpen I) (hIc : IsPreconnected I) (hf : ∀ z ∈ I, f z = 0)
    (hy₁ : ∀ z ∈ I, HasDerivAt y₁ (v₁ z) z)
    (hv₁ : ∀ z ∈ I, HasDerivAt v₁ (-f z * v₁ z - g z * y₁ z) z)
    (hy₂ : ∀ z ∈ I, HasDerivAt y₂ (v₂ z) z)
    (hv₂ : ∀ z ∈ I, HasDerivAt v₂ (-f z * v₂ z - g z * y₂ z) z)
    {x₀ x : ℝ} (hx₀ : x₀ ∈ I) (hx : x ∈ I) :
    wronskian y₁ v₁ y₂ v₂ x = wronskian y₁ v₁ y₂ v₂ x₀ := by
  apply hI.is_const_of_deriv_eq_zero hIc
    (fun z hz ↦
      (hasDerivAt_wronskian hz hy₁ hv₁ hy₂ hv₂).differentiableAt.differentiableWithinAt)
    (fun z hz ↦ ?_) hx hx₀
  simpa [hf z hz] using (hasDerivAt_wronskian hz hy₁ hv₁ hy₂ hv₂).deriv

/-- Real A1: the Wronskian of two real phase-pair solutions satisfies `W' = -f W`.
@isnad1 id=hasderiv.5h8v.s8.d4bf142a0193 from=translated src=- shape=ddf073c9 vocab=1fcbd408
-/
theorem hasDerivAt_realWronskian {I : Set ℝ} {f g y₁ v₁ y₂ v₂ : ℝ → ℝ} {x : ℝ}
    (hx : x ∈ I)
    (hy₁ : ∀ z ∈ I, HasDerivAt y₁ (v₁ z) z)
    (hv₁ : ∀ z ∈ I, HasDerivAt v₁ (-f z * v₁ z - g z * y₁ z) z)
    (hy₂ : ∀ z ∈ I, HasDerivAt y₂ (v₂ z) z)
    (hv₂ : ∀ z ∈ I, HasDerivAt v₂ (-f z * v₂ z - g z * y₂ z) z) :
    HasDerivAt (realWronskian y₁ v₁ y₂ v₂)
      (-f x * realWronskian y₁ v₁ y₂ v₂ x) x := by
  have h := ((hy₁ x hx).mul (hv₂ x hx)).sub ((hy₂ x hx).mul (hv₁ x hx))
  exact h.congr_deriv (by simp only [realWronskian, wronskian]; ring)

/-- Real A2: Abel's basepoint formula for real-valued solutions.
@isnad1 id=eq.9h9v.s8.63cef4a9d284 from=translated src=- shape=f64d2aec vocab=db7a528e
-/
theorem realWronskian_eq_mul_exp_integral {I : Set ℝ} {f g y₁ v₁ y₂ v₂ : ℝ → ℝ}
    (hI : IsOpen I) (hIc : IsPreconnected I) (hf : ContinuousOn f I)
    (hy₁ : ∀ z ∈ I, HasDerivAt y₁ (v₁ z) z)
    (hv₁ : ∀ z ∈ I, HasDerivAt v₁ (-f z * v₁ z - g z * y₁ z) z)
    (hy₂ : ∀ z ∈ I, HasDerivAt y₂ (v₂ z) z)
    (hv₂ : ∀ z ∈ I, HasDerivAt v₂ (-f z * v₂ z - g z * y₂ z) z)
    {x₀ x : ℝ} (hx₀ : x₀ ∈ I) (hx : x ∈ I) :
    realWronskian y₁ v₁ y₂ v₂ x = realWronskian y₁ v₁ y₂ v₂ x₀ *
      Real.exp (-∫ t in x₀..x, f t) := by
  exact eqOn_const_mul_exp_neg_integral_of_hasDerivAt hI hIc hf
    (fun z hz ↦ hasDerivAt_realWronskian hz hy₁ hv₁ hy₂ hv₂) hx₀ hx

/-- Real A3, pointwise form.
@isnad1 id=iff.9h9v.s8.d4b6a7dfa2d4 from=translated src=- shape=10b08465 vocab=341b5dcb
-/
theorem realWronskian_eq_zero_iff {I : Set ℝ} {f g y₁ v₁ y₂ v₂ : ℝ → ℝ}
    (hI : IsOpen I) (hIc : IsPreconnected I) (hf : ContinuousOn f I)
    (hy₁ : ∀ z ∈ I, HasDerivAt y₁ (v₁ z) z)
    (hv₁ : ∀ z ∈ I, HasDerivAt v₁ (-f z * v₁ z - g z * y₁ z) z)
    (hy₂ : ∀ z ∈ I, HasDerivAt y₂ (v₂ z) z)
    (hv₂ : ∀ z ∈ I, HasDerivAt v₂ (-f z * v₂ z - g z * y₂ z) z)
    {x₀ x : ℝ} (hx₀ : x₀ ∈ I) (hx : x ∈ I) :
    realWronskian y₁ v₁ y₂ v₂ x = 0 ↔ realWronskian y₁ v₁ y₂ v₂ x₀ = 0 := by
  rw [realWronskian_eq_mul_exp_integral hI hIc hf hy₁ hv₁ hy₂ hv₂ hx₀ hx,
    mul_eq_zero]
  simp [Real.exp_ne_zero]

/-- Real A3: a real Wronskian is identically zero or nowhere zero.
@isnad1 id=or.8h7v.s8.79bbfd72dca8 from=translated src=- shape=7b5d5e99 vocab=60f9c54a
-/
theorem realWronskian_zero_or_nowhere_zero {I : Set ℝ} {f g y₁ v₁ y₂ v₂ : ℝ → ℝ}
    (hIne : I.Nonempty) (hI : IsOpen I) (hIc : IsPreconnected I) (hf : ContinuousOn f I)
    (hy₁ : ∀ z ∈ I, HasDerivAt y₁ (v₁ z) z)
    (hv₁ : ∀ z ∈ I, HasDerivAt v₁ (-f z * v₁ z - g z * y₁ z) z)
    (hy₂ : ∀ z ∈ I, HasDerivAt y₂ (v₂ z) z)
    (hv₂ : ∀ z ∈ I, HasDerivAt v₂ (-f z * v₂ z - g z * y₂ z) z) :
    (∀ x ∈ I, realWronskian y₁ v₁ y₂ v₂ x = 0) ∨
      (∀ x ∈ I, realWronskian y₁ v₁ y₂ v₂ x ≠ 0) := by
  obtain ⟨x₀, hx₀⟩ := hIne
  by_cases hzero : realWronskian y₁ v₁ y₂ v₂ x₀ = 0
  · left
    intro x hx
    exact (realWronskian_eq_zero_iff hI hIc hf hy₁ hv₁ hy₂ hv₂ hx₀ hx).2 hzero
  · right
    intro x hx hxzero
    exact hzero ((realWronskian_eq_zero_iff hI hIc hf hy₁ hv₁ hy₂ hv₂ hx₀ hx).1 hxzero)

/-- Real A3, exclusive form: exactly one real Wronskian alternative holds.
@isnad1 id=xor.8h7v.s8.d793d403b953 from=translated src=- shape=7b5d5e99 vocab=1e4bb1a9
-/
theorem realWronskian_zero_xor_nowhere_zero {I : Set ℝ} {f g y₁ v₁ y₂ v₂ : ℝ → ℝ}
    (hIne : I.Nonempty) (hI : IsOpen I) (hIc : IsPreconnected I) (hf : ContinuousOn f I)
    (hy₁ : ∀ z ∈ I, HasDerivAt y₁ (v₁ z) z)
    (hv₁ : ∀ z ∈ I, HasDerivAt v₁ (-f z * v₁ z - g z * y₁ z) z)
    (hy₂ : ∀ z ∈ I, HasDerivAt y₂ (v₂ z) z)
    (hv₂ : ∀ z ∈ I, HasDerivAt v₂ (-f z * v₂ z - g z * y₂ z) z) :
    Xor (∀ x ∈ I, realWronskian y₁ v₁ y₂ v₂ x = 0)
      (∀ x ∈ I, realWronskian y₁ v₁ y₂ v₂ x ≠ 0) := by
  rcases realWronskian_zero_or_nowhere_zero hIne hI hIc hf hy₁ hv₁ hy₂ hv₂ with hzero | hne
  · left
    refine ⟨hzero, ?_⟩
    intro hnowhere
    obtain ⟨x, hx⟩ := hIne
    exact hnowhere x hx (hzero x hx)
  · right
    refine ⟨hne, ?_⟩
    intro hzero
    obtain ⟨x, hx⟩ := hIne
    exact hne x hx (hzero x hx)

/-- Real A4: if the first-derivative coefficient vanishes, the real Wronskian is constant.
@isnad1 id=eq.9h9v.s8.147f4ad16283 from=translated src=- shape=049b3378 vocab=35138929
-/
theorem realWronskian_eq_of_f_eq_zero {I : Set ℝ} {f g y₁ v₁ y₂ v₂ : ℝ → ℝ}
    (hI : IsOpen I) (hIc : IsPreconnected I) (hf : ∀ z ∈ I, f z = 0)
    (hy₁ : ∀ z ∈ I, HasDerivAt y₁ (v₁ z) z)
    (hv₁ : ∀ z ∈ I, HasDerivAt v₁ (-f z * v₁ z - g z * y₁ z) z)
    (hy₂ : ∀ z ∈ I, HasDerivAt y₂ (v₂ z) z)
    (hv₂ : ∀ z ∈ I, HasDerivAt v₂ (-f z * v₂ z - g z * y₂ z) z)
    {x₀ x : ℝ} (hx₀ : x₀ ∈ I) (hx : x ∈ I) :
    realWronskian y₁ v₁ y₂ v₂ x = realWronskian y₁ v₁ y₂ v₂ x₀ := by
  apply hI.is_const_of_deriv_eq_zero hIc
    (fun z hz ↦
      (hasDerivAt_realWronskian hz hy₁ hv₁ hy₂ hv₂).differentiableAt.differentiableWithinAt)
    (fun z hz ↦ ?_) hx hx₀
  simpa [hf z hz] using (hasDerivAt_realWronskian hz hy₁ hv₁ hy₂ hv₂).deriv

end LMLF.ODE

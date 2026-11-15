import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_TateLocalZeta

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

open Complex Real MeasureTheory LanglandsTunnell.TateLocal

namespace LanglandsTunnell.ArchPlace

def psiComplex : AddChar ℂ ℂ where
  toFun z := Complex.exp (-(2 * π * Complex.I * (z + starRingEnd ℂ z)))
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    rw [← Complex.exp_add, map_add]; ring_nf

/--
@isnad1 id=eq.0h1v.s6.ba7b797aa72c from=translated src=- shape=cbe1327c vocab=316e3ffe
-/
theorem psiComplex_apply (z : ℂ) :
    psiComplex z = Complex.exp (-(2 * π * Complex.I * (z + starRingEnd ℂ z))) := rfl

def anglePhase (z : ℂˣ) : ℂ := (z : ℂ) / (‖(z : ℂ)‖ : ℂ)

/--
@isnad1 id=eq.0h1v.s4.3b600e2292fc from=translated src=- shape=3ef63426 vocab=ce2a879a
-/
@[simp] theorem norm_anglePhase (z : ℂˣ) : ‖anglePhase z‖ = 1 := by
  rw [anglePhase, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr z.ne_zero)]

/--
@isnad1 id=ne.0h1v.s4.f106a84ad658 from=translated src=- shape=505c726b vocab=8e340220
-/
theorem anglePhase_ne_zero (z : ℂˣ) : anglePhase z ≠ 0 := fun h => by
  have := norm_anglePhase z; rw [h, norm_zero] at this; exact one_ne_zero this.symm

/--
@isnad1 id=eq.0h2v.s5.a46e0e3ac56b from=translated src=- shape=22876443 vocab=f4b9f28b
-/
theorem anglePhase_mul (z w : ℂˣ) : anglePhase (z * w) = anglePhase z * anglePhase w := by
  simp only [anglePhase, Units.val_mul, norm_mul, Complex.ofReal_mul, div_eq_mul_inv, mul_inv]
  ring

def complexCharFun (u : ℂ) (k : ℤ) : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 (((‖(z : ℂ)‖ : ℂ) ^ (2 * u)) * anglePhase z ^ k)
    (mul_ne_zero
      (Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr z.ne_zero))))
      (zpow_ne_zero _ (anglePhase_ne_zero z)))
  map_one' := by ext; simp [anglePhase]
  map_mul' z w := by
    ext
    simp only [Units.val_mul, Units.val_mk0]
    push_cast [norm_mul, anglePhase_mul, mul_zpow]
    rw [Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
    ring

/--
@isnad1 id=eq.0h3v.s7.b62c9200345b from=translated src=- shape=140b55fd vocab=81991740
-/
theorem complexCharFun_apply (u : ℂ) (k : ℤ) (z : ℂˣ) :
    ((complexCharFun u k z : ℂˣ) : ℂ) = (‖(z : ℂ)‖ : ℂ) ^ (2 * u) * anglePhase z ^ k := rfl

def complexTestFun (k : ℤ) : ℂ → ℂ :=
  fun z => (starRingEnd ℂ z) ^ k.toNat * z ^ (-k).toNat * Complex.exp (-(2 * π * ‖z‖ ^ 2))

/--
@isnad1 id=eq.0h1v.s5.ccac123892fb from=translated src=- shape=25f2642b vocab=b5d710e9
-/
@[simp] theorem complexTestFun_zero_apply (z : ℂ) :
    complexTestFun 0 z = Complex.exp (-(2 * π * ‖z‖ ^ 2)) := by
  simp [complexTestFun]

/--
@isnad1 id=eq.0h0v.s4.3a5001a105a0 from=translated src=- shape=11536466 vocab=a97fdf18
-/
theorem complexTestFun_zero_at_zero : complexTestFun 0 0 = 1 := by simp

/--
@isnad1 id=ne.0h0v.s4.52bdaa08112e from=translated src=- shape=b60f58fc vocab=a97fdf18
-/
theorem complexTestFun_zero_ne_zero : complexTestFun 0 ≠ 0 := by
  intro h; have := congrFun h 0; simp at this

def complexZeta (μ : Measure ℂ) (f : ℂ → ℂ) (χ : ℂˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ z, f z * charExt χ z * ((‖z‖ : ℂ) ^ ((2 : ℂ) * s - 2)) ∂μ

def complexGammaAt (μ : Measure ℂ) (ψ : AddChar ℂ ℂ) (f₀ : ℂ → ℂ) (χ : ℂˣ →* ℂˣ) (s : ℂ) : ℂ :=
  complexZeta μ (tateFourier ψ μ f₀) χ⁻¹ (1 - s) / complexZeta μ f₀ χ s

/--
@isnad1 id=eq.0h2v.s7.8efe370c1b00 from=translated src=- shape=016c7705 vocab=316e3ffe
-/
theorem psiComplex_mul_eq (z w : ℂ) :
    psiComplex (z * w)
      = Complex.exp (-(2 * π * Complex.I * (z * w + starRingEnd ℂ z * starRingEnd ℂ w))) := by
  rw [psiComplex_apply, map_mul]

def psiReal : AddChar ℝ ℂ where
  toFun x := Complex.exp (-(2 * π * Complex.I * x))
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by push_cast; rw [← Complex.exp_add]; ring_nf

/--
@isnad1 id=eq.0h1v.s5.3a45ad2962df from=translated src=- shape=493a654a vocab=239c5035
-/
theorem psiReal_apply (x : ℝ) : psiReal x = Complex.exp (-(2 * π * Complex.I * x)) := rfl

def realSign (x : ℝˣ) : ℂˣ :=
  Units.mk0 ((x : ℝ) / (‖(x : ℝ)‖ : ℝ) : ℂ) (by
    have hx : (x : ℝ) ≠ 0 := x.ne_zero
    simp only [ne_eq, Complex.ofReal_eq_zero, div_eq_zero_iff, hx, norm_eq_zero, or_self,
      not_false_eq_true])

/--
@isnad1 id=eq.0h2v.s6.b12775e54e43 from=translated src=- shape=72e5a4ef vocab=99cd2990
-/
theorem realSign_mul (x y : ℝˣ) : realSign (x * y) = realSign x * realSign y := by
  ext
  simp only [realSign, Units.val_mk0, Units.val_mul, norm_mul]
  push_cast
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]; ring

def realCharFun (u : ℂ) (a : ZMod 2) : ℝˣ →* ℂˣ where
  toFun x := Units.mk0 ((‖(x : ℝ)‖ : ℂ) ^ u)
      (Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero))))
    * realSign x ^ (a.val : ℕ)
  map_one' := by ext; simp [realSign]
  map_mul' x y := by
    ext
    simp only [Units.val_mul, Units.val_mk0, Units.val_pow_eq_pow_val, realSign_mul, mul_pow]
    push_cast [norm_mul]
    rw [Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
    ring

def realTestFun (a : ZMod 2) : ℝ → ℂ :=
  fun x => ((x : ℂ) ^ (a.val : ℕ)) * Complex.exp (-(π * x ^ 2))

/--
@isnad1 id=eq.0h1v.s6.d6d36e76454b from=translated src=- shape=d32cc44c vocab=318ac3a2
-/
@[simp] theorem realTestFun_zero_apply (x : ℝ) :
    realTestFun 0 x = Complex.exp (-(π * x ^ 2)) := by simp [realTestFun]

/--
@isnad1 id=eq.0h0v.s6.588a7c945aed from=translated src=- shape=3b1e5150 vocab=94ddfa0d
-/
theorem realTestFun_zero_at_zero : realTestFun 0 0 = 1 := by simp

/--
@isnad1 id=ne.0h0v.s6.4ff99774b8bd from=translated src=- shape=4cbf1470 vocab=94ddfa0d
-/
theorem realTestFun_zero_ne_zero : realTestFun 0 ≠ 0 := by
  intro h; have := congrFun h 0; simp at this

def realZeta (μ : Measure ℝ) (f : ℝ → ℂ) (χ : ℝˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ x, f x * charExt χ x * ((‖x‖ : ℂ) ^ (s - 1)) ∂μ

def realGammaAt (μ : Measure ℝ) (ψ : AddChar ℝ ℂ) (f₀ : ℝ → ℂ) (χ : ℝˣ →* ℂˣ) (s : ℂ) : ℂ :=
  realZeta μ (tateFourier ψ μ f₀) χ⁻¹ (1 - s) / realZeta μ f₀ χ s

end LanglandsTunnell.ArchPlace

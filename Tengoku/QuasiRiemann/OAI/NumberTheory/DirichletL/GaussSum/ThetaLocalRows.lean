import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.GaussSum.AbelPhaseLimit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology

namespace ActualEisensteinCubic

section

open EisensteinEmbedding ConcreteTraceCRT Complex

/--
@isnad1 id=other.0h5v.s7.92bdcbe7fd51 from=translated src=- shape=a32d942d vocab=54e180ff
-/
theorem actual_fixed_kernel_eq_dualFixedTerm
    (a b k l : ℤ) (η : ℝ) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let y : O := dualFrequencyEquiv (k,l)
    Complex.exp (-(Real.pi : ℂ) *
        (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
        (‖eisEmbedding y‖ ^ 2 : ℂ)) *
      fixedDualPhase c y =
      OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) (k,l) := by
  let c : O := ActualEisensteinCoordinates.eval a b
  let y : O := dualFrequencyEquiv (k,l)
  have hnormC : ((‖eisEmbedding y‖ : ℂ)^2) =
      (((k^2+k*l+l^2 : ℤ) : ℂ)) := by
    exact_mod_cast dualFrequencyEquiv_norm_sq k l
  have hreal : Complex.exp (-(Real.pi : ℂ) *
        (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
        (‖eisEmbedding y‖ ^ 2 : ℂ)) =
      (OscSpecial.dualAmp η (a : ℝ) (b : ℝ) (k,l) : ℂ) := by
    rw [hnormC]
    dsimp [OscSpecial.dualAmp, OscSpecial.dualScale, OscSpecial.dualQ]
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hphase : fixedDualPhase c y =
      Complex.exp (Complex.I *
        (OscSpecial.phaseAngle (a : ℝ) (b : ℝ) (k,l) : ℂ)) := by
    have h := breveE_dual_quadratic_real_scale 1 a b k l
    have harg : fixedDualPhase c y =
        Complex.exp (-(2 * Real.pi * Complex.I *
          (((a-b)*k^2+2*a*k*l+b*l^2 : ℤ) : ℂ)) / (4 : ℂ)) := by
      change ShortDraftTrace.breveE
        (eisEmbedding (-(ActualEisensteinCoordinates.eval a b *
          (ActualEisensteinCoordinates.eval (k+l) k)^2)) /
          eisLam / (4 : ℂ)) = _
      simpa using h
    rw [harg]
    congr 1
    dsimp [OscSpecial.phaseAngle, OscSpecial.dualTrace]
    push_cast
    ring
  dsimp only
  rw [hreal, hphase]
  rfl

open EisensteinEmbedding ConcreteTraceCRT Complex
open scoped Topology
open Filter

noncomputable def actualVariableDualKernel (a b : ℤ) (η : ℝ) (y : O) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
    (‖eisEmbedding y‖ ^ 2 : ℂ)) *
  ShortDraftTrace.breveE
    (eisEmbedding (-(ActualEisensteinCoordinates.eval a b * y^2)) /
      eisLam /
      ((4 * OscSpecial.r η (a : ℝ) (b : ℝ) : ℝ) : ℂ))

noncomputable def actualFixedDualKernel (a b : ℤ) (η : ℝ) (y : O) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
    (‖eisEmbedding y‖ ^ 2 : ℂ)) *
  fixedDualPhase (ActualEisensteinCoordinates.eval a b) y

private theorem dualScale_cast (η a b : ℝ) :
    (OscSpecial.dualScale η a b : ℂ) =
      (η : ℂ) * (OscSpecial.q a b : ℂ) /
        (4 * (OscSpecial.r η a b : ℂ)) := by
  dsimp [OscSpecial.dualScale]
  push_cast
  ring

/--
@isnad1 id=eq.2h4v.s6.902295ee4b20 from=translated src=- shape=1fab516c vocab=9714bb1d
-/
theorem actual_variable_kernel_eq_dualVarTerm
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) (z : ℤ × ℤ) :
    actualVariableDualKernel a b η (dualFrequencyEquiv z) =
      OscSpecial.dualVarTerm η (a : ℝ) (b : ℝ) z := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by
      simpa only [pow_two] using hqZ)
  have h := (dual_gaussian_is_actual_trace_phase
    a b z.1 z.2 hc η hη).symm.trans
      (OscSpecial.dualGaussian_eq_dualVarTerm hη hq z)
  unfold actualVariableDualKernel
  rw [dualScale_cast]
  exact h

/--
@isnad1 id=eq.0h4v.s5.cd9f153b6031 from=translated src=- shape=390759ef vocab=4e710a60
-/
theorem actual_fixed_kernel_eq_dualFixedTerm_point
    (a b : ℤ) (η : ℝ) (z : ℤ × ℤ) :
    actualFixedDualKernel a b η (dualFrequencyEquiv z) =
      OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) z := by
  rcases z with ⟨k,l⟩
  exact actual_fixed_kernel_eq_dualFixedTerm a b k l η

end

section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

end

section

open EisensteinEmbedding ConcreteTraceCRT Complex

/--
@isnad1 id=other.2h3v.s10.b9deab48154a from=translated src=- shape=8361b9b5 vocab=53b13ec6
-/
theorem actual_oscillatory_poisson_kernel
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) :
    let c : O := ActualEisensteinCoordinates.eval a b
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ))) =
      (1 / ((OscSpecial.R η (a : ℝ) (b : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
        ∑' y : O, actualVariableDualKernel a b η y := by
  dsimp only
  rw [actual_oscillatory_poisson a b hc η hη]
  congr 1
  apply tsum_congr
  intro y
  unfold actualVariableDualKernel
  rw [dualScale_cast]

end

section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

end

section

/--
@isnad1 id=other.1h2v.s7.f745ee9946b4 from=translated src=- shape=0b9d32f2 vocab=567df713
-/
theorem dual_abel_coefficient (a b : ℤ)
    (hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ)) :
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) *
      ((2 / (Real.sqrt 3 *
        (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)) =
      ((2 / (Real.sqrt 3 * OscSpecial.q (a : ℝ) (b : ℝ)) : ℝ) : ℂ) := by
  dsimp only
  rw [two_coordinate_norm_four]
  have hqC : (OscSpecial.q (a : ℝ) (b : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hq.ne'
  have hsC : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 3)))
  push_cast
  field_simp [hqC, hsC]

/--
@isnad1 id=other.1h2v.s8.8794bb1f683b from=translated src=- shape=9b1d6a14 vocab=05b980d1
-/
theorem full_dual_abel_coefficient (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let q : ℝ := OscSpecial.q (a : ℝ) (b : ℝ)
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    (((Real.sqrt q / 2 : ℝ) : ℂ) *
      (((4 / q : ℝ) : ℂ) *
        ((2 / (Real.sqrt 3 *
          (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ))) =
      (((2 / (Real.sqrt 3 * ‖ConcreteTraceCRT.eisEmbedding c‖) : ℝ) : ℂ) / 2) := by
  dsimp only
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by simpa only [pow_two] using hqZ)
  rw [dual_abel_coefficient a b hq]
  have hqnorm := osc_q_eq_eis_norm_sq a b
  have hsqrt : Real.sqrt (OscSpecial.q (a : ℝ) (b : ℝ)) =
      ‖ConcreteTraceCRT.eisEmbedding
        (ActualEisensteinCoordinates.eval a b)‖ := by
    rw [hqnorm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [hsqrt, hqnorm]
  have hn : (‖ConcreteTraceCRT.eisEmbedding
      (ActualEisensteinCoordinates.eval a b)‖ : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (norm_pos_iff.mpr
      (ConcreteTraceCRT.eisEmbedding_ne_zero hc)))
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 3)))
  push_cast
  field_simp [hn, hs]

open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

end

end ActualEisensteinCubic

/--
@isnad1 id=eq.0h0v.s4.7d82970f79e8 from=translated src=- shape=a8d4d362 vocab=1a898209
-/
theorem theta_counter_lambda_eq : ActualEisensteinCubic.lambda =
    ActualEisensteinCoordinates.eval (-1) 1 := by
  have homega : ActualEisensteinCubic.omega = ActualEisensteinCoordinates.omega := by
    rfl
  rw [ActualEisensteinCubic.lambda, ActualEisensteinCoordinates.eval, homega]
  ring

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

private noncomputable def pSeven : ActualEisensteinCubic.O := ActualEisensteinCoordinates.eval 1 3
private noncomputable def PSeven : Ideal ActualEisensteinCubic.O := Ideal.span {pSeven}

open MulChar AddChar

namespace ShortDraftLocal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/--
@isnad1 id=eq.0h4v.s9.083126e746cd from=translated src=- shape=4f38964d vocab=ad2ac8e3
-/
theorem direct_theta_jone_inversion (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (a : F) :
    (∑ h : Fˣ, (χ⁻¹ * χ ^ 2) (h : F) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      gaussSum χ⁻¹ (ψ.mulShift a) := by
  classical
  have hchar : χ⁻¹ * χ ^ 2 = χ := by group
  rw [hchar]
  calc
    (∑ h : Fˣ, χ (h : F) * ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, χ⁻¹ (y : F) * ψ (a * (y : F)) := by
      apply Fintype.sum_equiv (Equiv.inv Fˣ)
      intro y
      simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val]
      rw [MulChar.inv_apply']
      simp
    _ = gaussSum χ⁻¹ (ψ.mulShift a) := by
      rw [gaussSum_eq_units_sum]
      simp only [AddChar.mulShift_apply]

/--
@isnad1 id=eq.1h6v.s10.57f1388c4e4b from=translated src=- shape=59b03e53 vocab=9fa9053c
-/
theorem direct_theta_jone_local_row (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (σ : Fˣ) (ε x : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, χ t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      (χ ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum χ (ψ.mulShift (-1)) * gaussSum χ⁻¹ ψ * χ ε) * χ x := by
  classical
  have hsum :
      (∑ h : Fˣ,
        (∑ t : F, χ t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
        (χ ^ 2) σ * gaussSum χ (ψ.mulShift (-1)) *
          (∑ h : Fˣ,
            (χ⁻¹ * χ ^ 2) (h : F) *
              ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [nontrivial_fourier_coefficient χ ψ hχ, map_mul]
    simp only [MulChar.mul_apply]
    ring
  rw [hsum, direct_theta_jone_inversion χ ψ (ε * x)]
  have hinv : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    calc χ = (χ⁻¹)⁻¹ := by group
      _ = 1 := by rw [h]; simp
  rw [gaussSum_mulShift_any χ⁻¹ ψ hinv (ε * x)]
  simp only [inv_inv, map_mul]
  ring

/--
@isnad1 id=eq.1h5v.s9.558f7b37b1a8 from=translated src=- shape=a7c1ea5d vocab=33a7e420
-/
theorem direct_theta_jone_zero (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (σ : Fˣ) (ε : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, χ t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * 0) * ((h⁻¹ : Fˣ) : F))) = 0 := by
  rw [direct_theta_jone_local_row χ ψ hχ σ ε 0]
  simp

omit [Fintype F] [DecidableEq F] in
/--
@isnad1 id=ne.1h2v.s8.f23fbea57d24 from=translated src=- shape=b4872a0e vocab=5e87c77b
-/
theorem direct_theta_jone_not_quadratic (χ : MulChar F ℂ)
    (hχ₂ : χ ^ 2 ≠ 1) : χ ≠ χ ^ 3 := by
  intro h
  apply hχ₂
  calc
    χ ^ 2 = χ ^ 3 * χ⁻¹ := by group
    _ = χ * χ⁻¹ := by rw [← h]
    _ = 1 := by group

end ShortDraftLocal

end

end OAI

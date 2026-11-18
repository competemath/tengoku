import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.Poisson.GaussianMoments

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

namespace OscSpecial

/--
@isnad1 id=eq.2h3v.s7.7a4c097e344d from=translated src=- shape=863e95cb vocab=d842a473
-/
theorem oscillatory_gaussian_poisson {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) :
    (∑' z : ℤ × ℤ, RankTwoComplex.binaryGaussian (A η a b) (B η a b) (D η a b) z) =
      (1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ))) *
        ∑' z : ℤ × ℤ,
          RankTwoComplex.dualGaussian (A η a b) (B η a b) (D η a b) z := by
  have hq0 : q a b ≠ 0 := hq.ne'
  have ha : 0 < (A η a b).re := by
    rw [(coefficient_re η a b hq0).1]
    exact hη
  have hR : 0 < R η a b := by
    unfold R
    positivity
  exact binary_gaussian_poisson_real_det ha hR
    (oscillatory_determinant η a b hq0)
    (real_positive_definite hη hq0)

noncomputable def r (η a b : ℝ) : ℝ := 1 + 3 * q a b * η ^ 2 / 16

/--
@isnad1 id=lt.2h3v.s5.ca2d629e21bb from=translated src=- shape=c2c6ddf7 vocab=40a0ab9c
-/
theorem r_pos {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    0 < r η a b := by
  unfold r
  positivity

private theorem inverseForm_explicit {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b)
    (z : ℤ × ℤ) :
    inverseForm (A η a b) (B η a b) (D η a b) (R η a b) z =
      ((η : ℂ) * (q a b : ℂ) / (4 * (r η a b : ℂ))) *
        ((z.1 : ℂ) ^ 2 + (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2) +
      Complex.I / (2 * (r η a b : ℂ)) *
        (((a-b : ℝ) : ℂ) * (z.1 : ℂ) ^ 2 +
          2 * (a : ℂ) * (z.1 : ℂ) * (z.2 : ℂ) +
          (b : ℂ) * (z.2 : ℂ) ^ 2) := by
  have hq0 : q a b ≠ 0 := hq.ne'
  have hqc : (q a b : ℂ) ≠ 0 := by exact_mod_cast hq0
  have hr0 : r η a b ≠ 0 := (r_pos hη hq).ne'
  have hrc : (r η a b : ℂ) ≠ 0 := by exact_mod_cast hr0
  have hR : 0 < R η a b := by unfold R; positivity
  have hRc : (R η a b : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hRexpr : (R η a b : ℂ) = 4 * (r η a b : ℂ) / (q a b : ℂ) := by
    simp [R, r]
    field_simp [hqc]
    ring
  have hqexpr : (q a b : ℂ) = (a : ℂ) ^ 2 - (a : ℂ) * (b : ℂ) + (b : ℂ) ^ 2 := by
    simp [q]
  have hrexpr : (r η a b : ℂ) = 1 + 3 * (q a b : ℂ) * (η : ℂ) ^ 2 / 16 := by
    simp [r]
  dsimp [inverseForm, A, B, D]
  rw [hRexpr]
  field_simp [hqc, hrc]
  push_cast
  ring

/--
@isnad1 id=eq.2h4v.s8.20da5f758c28 from=translated src=- shape=2f42448b vocab=bcbd002c
-/
theorem dualGaussian_explicit {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b)
    (z : ℤ × ℤ) :
    RankTwoComplex.dualGaussian (A η a b) (B η a b) (D η a b) z =
      Complex.exp (-(Real.pi : ℂ) *
        (((η : ℂ) * (q a b : ℂ) / (4 * (r η a b : ℂ))) *
          ((z.1 : ℂ) ^ 2 + (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2) +
         Complex.I / (2 * (r η a b : ℂ)) *
          (((a-b : ℝ) : ℂ) * (z.1 : ℂ) ^ 2 +
            2 * (a : ℂ) * (z.1 : ℂ) * (z.2 : ℂ) +
            (b : ℂ) * (z.2 : ℂ) ^ 2))) := by
  have hq0 : q a b ≠ 0 := hq.ne'
  have hA0 : A η a b ≠ 0 := by
    intro h
    have hAr : (A η a b).re = η := (coefficient_re η a b hq0).1
    simp [h] at hAr
    linarith
  have hR : 0 < R η a b := by unfold R; positivity
  rw [dualGaussian_inverseForm hA0 hR.ne'
    (oscillatory_determinant η a b hq0) z,
    inverseForm_explicit hη hq z]

end OscSpecial

namespace ActualEisensteinCubic

section

open EisensteinEmbedding ConcreteTraceCRT Complex

/--
@isnad1 id=eq.0h4v.s7.50807694a6cf from=translated src=- shape=cfe1b9f6 vocab=3e2a3b38
-/
theorem dual_quadratic_trace_coeff (a b k l : ℤ) :
    (ActualEisensteinCoordinates.coords
      (ActualEisensteinCoordinates.eval a b *
        (ActualEisensteinCoordinates.eval (k+l) k)^2)).2 =
      (a-b)*k^2+2*a*k*l+b*l^2 := by
  rw [pow_two, ActualEisensteinCoordinates.eval_mul (k+l) k (k+l) k]
  rw [ActualEisensteinCoordinates.eval_mul]
  rw [ShortDraftLatticeCount.coords_eval]
  ring

private theorem coords_neg_second (z : O) :
    (ActualEisensteinCoordinates.coords (-z)).2 =
      -(ActualEisensteinCoordinates.coords z).2 := by
  let a := (ActualEisensteinCoordinates.coords z).1
  let b := (ActualEisensteinCoordinates.coords z).2
  have hz : z = ActualEisensteinCoordinates.eval a b :=
    (ActualEisensteinCoordinates.eval_coords z).symm
  rw [hz]
  have hneg : -ActualEisensteinCoordinates.eval a b =
      ActualEisensteinCoordinates.eval (-a) (-b) := by
    simp only [ActualEisensteinCoordinates.eval]
    push_cast
    ring
  rw [hneg, ShortDraftLatticeCount.coords_eval,
    ShortDraftLatticeCount.coords_eval]

/--
@isnad1 id=eq.0h5v.s8.a63634d92c14 from=translated src=- shape=f6a2d343 vocab=9cc4072b
-/
theorem breveE_dual_quadratic_real_scale
    (r : ℝ) (a b k l : ℤ) :
    ShortDraftTrace.breveE
      (eisEmbedding (-(ActualEisensteinCoordinates.eval a b *
        (ActualEisensteinCoordinates.eval (k+l) k)^2)) /
        eisLam / ((4*r : ℝ) : ℂ)) =
      Complex.exp (-(2 * Real.pi * Complex.I *
        (((a-b)*k^2+2*a*k*l+b*l^2 : ℤ) : ℂ)) /
        ((4*r : ℝ) : ℂ)) := by
  rw [breveE_real_trace_of_O]
  have hneg : (ActualEisensteinCoordinates.coords
      (-(ActualEisensteinCoordinates.eval a b *
        (ActualEisensteinCoordinates.eval (k+l) k)^2))).2 =
      -((a-b)*k^2+2*a*k*l+b*l^2) := by
    have hp := dual_quadratic_trace_coeff a b k l
    rw [coords_neg_second]
    simpa using congrArg Neg.neg hp
  rw [hneg]
  congr 1
  push_cast
  ring_nf

end

section

open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

end

open EisensteinEmbedding ConcreteTraceCRT Complex

/--
@isnad1 id=other.1h5v.s10.7c77bcb9738f from=translated src=- shape=7b1311bc vocab=1b71d246
-/
theorem actual_oscillatory_binary_coordinate
    (a b m n : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let z : O := ActualEisensteinCoordinates.eval m n
    (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ)) =
      RankTwoComplex.binaryGaussian
        (OscSpecial.A η (a : ℝ) (b : ℝ))
        (OscSpecial.B η (a : ℝ) (b : ℝ))
        (OscSpecial.D η (a : ℝ) (b : ℝ)) (m,n) := by
  have hqZ : a*a-a*b+b*b ≠ 0 :=
    (coordinate_norm_pos_of_nonzero a b hc).ne'
  have hqC : (((a*a-a*b+b*b : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast hqZ
  dsimp only
  rw [actual_oscillatory_gaussian_coordinate a b m n hc η]
  unfold RankTwoComplex.binaryGaussian OscSpecial.A OscSpecial.B
    OscSpecial.D OscSpecial.q
  congr 1
  push_cast
  field_simp [hqC]
  ring

/--
@isnad1 id=other.1h3v.s10.c5f2a08ddf55 from=translated src=- shape=b5da36f6 vocab=8b65e088
-/
theorem actual_oscillatory_sum_eq_binary
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) :
    let c : O := ActualEisensteinCoordinates.eval a b
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ))) =
      ∑' p : ℤ × ℤ,
        RankTwoComplex.binaryGaussian
          (OscSpecial.A η (a : ℝ) (b : ℝ))
          (OscSpecial.B η (a : ℝ) (b : ℝ))
          (OscSpecial.D η (a : ℝ) (b : ℝ)) p := by
  let W : O → ℂ := fun z =>
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates
        (ActualEisensteinCoordinates.eval a b) hc)
      (Ideal.Quotient.mk (Ideal.span {ActualEisensteinCoordinates.eval a b}) z ^ 2) *
    Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
      (‖eisEmbedding z‖ ^ 2 : ℂ))
  have h := (latticeCoordEquiv.symm.tsum_eq W).symm
  simpa only [W, latticeCoordEquiv] using
    (show (∑' z : O, W z) =
      ∑' p : ℤ × ℤ,
        RankTwoComplex.binaryGaussian
          (OscSpecial.A η (a : ℝ) (b : ℝ))
          (OscSpecial.B η (a : ℝ) (b : ℝ))
          (OscSpecial.D η (a : ℝ) (b : ℝ)) p from by
      calc
        (∑' z : O, W z) = ∑' p : ℤ × ℤ, W (latticeCoordEquiv.symm p) := h
        _ = _ := by
          apply tsum_congr
          intro p
          have hp : latticeCoordEquiv.symm p =
              ActualEisensteinCoordinates.eval p.1 p.2 := rfl
          rw [hp]
          exact actual_oscillatory_binary_coordinate a b p.1 p.2 hc η)

def dualFrequencyEquiv : (ℤ × ℤ) ≃ O where
  toFun p := ActualEisensteinCoordinates.eval (p.1 + p.2) p.1
  invFun y := ((ActualEisensteinCoordinates.coords y).2,
    (ActualEisensteinCoordinates.coords y).1 -
      (ActualEisensteinCoordinates.coords y).2)
  left_inv p := by
    rcases p with ⟨k,l⟩
    simp only [  ShortDraftLatticeCount.coords_eval]
    ext <;> ring
  right_inv y := by
    change ActualEisensteinCoordinates.eval
      ((ActualEisensteinCoordinates.coords y).2 +
        ((ActualEisensteinCoordinates.coords y).1 -
          (ActualEisensteinCoordinates.coords y).2))
      (ActualEisensteinCoordinates.coords y).2 = y
    convert ActualEisensteinCoordinates.eval_coords y using 1 ; ring_nf

/--
@isnad1 id=eq.0h2v.s7.c2c55b4ee2a0 from=translated src=- shape=74b2f34d vocab=a5771e4e
-/
theorem dualFrequencyEquiv_norm_sq (k l : ℤ) :
    ‖eisEmbedding (dualFrequencyEquiv (k,l))‖ ^ 2 =
      (((k^2+k*l+l^2 : ℤ) : ℝ)) := by
  change ‖eisEmbedding (ActualEisensteinCoordinates.eval (k+l) k)‖ ^ 2 = _
  rw [eisEmbedding_eval_norm_sq]
  ring_nf

/--
@isnad1 id=eq.0h5v.s8.8a40545fcfd1 from=translated src=- shape=f4378903 vocab=63b407e1
-/
theorem dualFrequencyEquiv_trace_phase (r : ℝ) (a b k l : ℤ) :
    ShortDraftTrace.breveE
      (eisEmbedding (-(ActualEisensteinCoordinates.eval a b *
        (dualFrequencyEquiv (k,l))^2)) /
        eisLam / ((4*r : ℝ) : ℂ)) =
      Complex.exp (-(2 * Real.pi * Complex.I *
        (((a-b)*k^2+2*a*k*l+b*l^2 : ℤ) : ℂ)) /
        ((4*r : ℝ) : ℂ)) := by
  exact breveE_dual_quadratic_real_scale r a b k l

end ActualEisensteinCubic

namespace GaussianMoment

open scoped Topology
open Filter

noncomputable def realGauss (t : ℝ) (z : ℤ × ℤ) : ℝ :=
  Real.exp (-Real.pi * t * RankTwoPoisson.eisQ z)

/--
@isnad1 id=le.0h2v.s4.97ba6a8293a1 from=translated src=- shape=5c861c0a vocab=cf912e8e
-/
theorem realGauss_nonneg (t : ℝ) (z : ℤ × ℤ) :
    0 ≤ realGauss t z := (Real.exp_pos _).le

/--
@isnad1 id=summable.1h1v.s4.f63d773832cd from=translated src=- shape=286866f6 vocab=e45e2c66
-/
theorem realGauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (realGauss t) := by
  have h := (RankTwoPoisson.eis_gauss_summable ht).norm
  convert h using 1
  funext z
  dsimp [realGauss, RankTwoPoisson.eisGauss]
  rw [Complex.norm_exp]
  simp

/--
@isnad1 id=eq.0h2v.s4.3153f9faa182 from=translated src=- shape=18d8efcc vocab=d3e7a3f1
-/
theorem realGauss_cast (t : ℝ) (z : ℤ × ℤ) :
    (realGauss t z : ℂ) = RankTwoEisShift.shifted t 0 0 z := by
  dsimp [realGauss, RankTwoPoisson.eisQ,
    RankTwoEisShift.shifted, RankTwoEisShift.Q]
  rw [← Complex.ofReal_exp]
  congr 1
  ring_nf

end GaussianMoment

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

/--
@isnad1 id=other.2h5v.s8.644f7aab17c9 from=translated src=- shape=8ceef2f4 vocab=7c5ce53e
-/
theorem dual_gaussian_is_actual_trace_phase
    (a b k l : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let y : O := dualFrequencyEquiv (k,l)
    let q : ℝ := OscSpecial.q (a : ℝ) (b : ℝ)
    let r : ℝ := OscSpecial.r η (a : ℝ) (b : ℝ)
    RankTwoComplex.dualGaussian
        (OscSpecial.A η (a : ℝ) (b : ℝ))
        (OscSpecial.B η (a : ℝ) (b : ℝ))
        (OscSpecial.D η (a : ℝ) (b : ℝ)) (k,l) =
      Complex.exp (-(Real.pi : ℂ) *
        ((η : ℂ) * (q : ℂ) / (4 * (r : ℂ))) *
        (‖eisEmbedding y‖ ^ 2 : ℂ)) *
      ShortDraftTrace.breveE
        (eisEmbedding (-(c * y^2)) / eisLam / ((4*r : ℝ) : ℂ)) := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by simpa only [pow_two] using hqZ)
  dsimp only
  rw [OscSpecial.dualGaussian_explicit hη hq (k,l)]
  rw [dualFrequencyEquiv_trace_phase (OscSpecial.r η (a : ℝ) (b : ℝ)) a b k l]
  have hnormC : ((‖eisEmbedding (dualFrequencyEquiv (k,l))‖ : ℂ)^2) =
      (((k^2+k*l+l^2 : ℤ) : ℂ)) := by
    exact_mod_cast dualFrequencyEquiv_norm_sq k l
  rw [hnormC]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/--
@isnad1 id=other.2h3v.s10.8055547155ec from=translated src=- shape=3d5a1813 vocab=82d705bc
-/
theorem actual_oscillatory_poisson
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let q : ℝ := OscSpecial.q (a : ℝ) (b : ℝ)
    let r : ℝ := OscSpecial.r η (a : ℝ) (b : ℝ)
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ))) =
      (1 / ((OscSpecial.R η (a : ℝ) (b : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
        ∑' y : O,
          Complex.exp (-(Real.pi : ℂ) *
            ((η : ℂ) * (q : ℂ) / (4 * (r : ℂ))) *
            (‖eisEmbedding y‖ ^ 2 : ℂ)) *
          ShortDraftTrace.breveE
            (eisEmbedding (-(c * y^2)) / eisLam / ((4*r : ℝ) : ℂ)) := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by simpa only [pow_two] using hqZ)
  dsimp only
  rw [actual_oscillatory_sum_eq_binary a b hc η,
    OscSpecial.oscillatory_gaussian_poisson hη hq]
  congr 1
  let W : O → ℂ := fun y =>
    Complex.exp (-(Real.pi : ℂ) *
      ((η : ℂ) * (OscSpecial.q (a : ℝ) (b : ℝ) : ℂ) /
        (4 * (OscSpecial.r η (a : ℝ) (b : ℝ) : ℂ))) *
      (‖eisEmbedding y‖ ^ 2 : ℂ)) *
    ShortDraftTrace.breveE
      (eisEmbedding (-(ActualEisensteinCoordinates.eval a b * y^2)) /
        eisLam /
        ((4 * OscSpecial.r η (a : ℝ) (b : ℝ) : ℝ) : ℂ))
  calc
    (∑' p : ℤ × ℤ,
      RankTwoComplex.dualGaussian
        (OscSpecial.A η (a : ℝ) (b : ℝ))
        (OscSpecial.B η (a : ℝ) (b : ℝ))
        (OscSpecial.D η (a : ℝ) (b : ℝ)) p) =
        ∑' p : ℤ × ℤ, W (dualFrequencyEquiv p) := by
      apply tsum_congr
      intro p
      simpa only [W] using
        dual_gaussian_is_actual_trace_phase a b p.1 p.2 hc η hη
    _ = ∑' y : O, W y := dualFrequencyEquiv.tsum_eq W

end ActualEisensteinCubic

namespace OscSpecial

private theorem R_eq_four_r_div_q {η a b : ℝ} (hq : q a b ≠ 0) :
    R η a b = 4 * r η a b / q a b := by
  unfold R r
  field_simp [hq]
  ring

private theorem sqrt_R_eq {η a b : ℝ} (_hη : 0 < η) (hq : 0 < q a b) :
    Real.sqrt (R η a b) = 2 * Real.sqrt (r η a b) / Real.sqrt (q a b) := by
  rw [R_eq_four_r_div_q hq.ne']
  rw [Real.sqrt_div' (4 * r η a b) hq.le]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hs4]

/--
@isnad1 id=eq.2h3v.s6.51a24ef59bb9 from=translated src=- shape=752635a6 vocab=ddf959d9
-/
theorem prefactor_eq_real_sqrt {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    (1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ))) =
      ((Real.sqrt (q a b) / (2 * Real.sqrt (r η a b)) : ℝ) : ℂ) := by
  have hR : 0 ≤ R η a b := by unfold R; positivity
  have hqS : Real.sqrt (q a b) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hrS : Real.sqrt (r η a b) ≠ 0 :=
    (Real.sqrt_pos.mpr (r_pos hη hq)).ne'
  have hcpow : (R η a b : ℂ) ^ (1 / 2 : ℂ) =
      ((R η a b) ^ (1 / 2 : ℝ) : ℝ) := by
    simpa using (Complex.ofReal_cpow hR (1 / 2 : ℝ)).symm
  rw [hcpow]
  simp only [Complex.ofReal_div]
  rw [← Real.sqrt_eq_rpow, sqrt_R_eq hη hq]
  push_cast
  field_simp [hqS, hrS]

open scoped Topology
open Filter

end OscSpecial

namespace GaussianMoment

open scoped Topology
open Filter

end GaussianMoment

end

end OAI

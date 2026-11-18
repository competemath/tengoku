import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.GaussSum.GaussianDualLimit

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

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

/--
@isnad1 id=eq.0h3v.s7.fe8351e057b0 from=translated src=- shape=d6d98b39 vocab=8ac539f8
-/
theorem breveE_real_trace_div (r : ℝ) (u v : ℤ) :
    ShortDraftTrace.breveE
      ((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / (r : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / (r : ℂ)) := by
  have htrace := ShortDraftTrace.trace_div_lam omega3 omega3_sq
    ShortDraftTrace.omega_conj u v
  have hL : ((u : ℂ) + (v : ℂ) * omega3) / eisLam +
      star (((u : ℂ) + (v : ℂ) * omega3) / eisLam) = (v : ℂ) := by
    simpa only [eisLam, Complex.star_def] using htrace
  change Complex.exp (2 * Real.pi * Complex.I *
    (((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / (r : ℂ)) +
      star (((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / (r : ℂ))))) = _
  rw [show star (((u : ℂ) + (v : ℂ) * omega3) / eisLam / (r : ℂ)) =
      star (((u : ℂ) + (v : ℂ) * omega3) / eisLam) / (r : ℂ) by simp]
  rw [← add_div, hL]
  congr 1
  ring

/--
@isnad1 id=eq.0h2v.s7.f5ae497098e0 from=translated src=- shape=d8c9cafc vocab=bdfc4ddb
-/
theorem breveE_real_trace_of_O (r : ℝ) (z : O) :
    ShortDraftTrace.breveE (eisEmbedding z / eisLam / (r : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((ActualEisensteinCoordinates.coords z).2 : ℂ) / (r : ℂ)) := by
  rw [← ActualEisensteinCoordinates.eval_coords z]
  rw [eisEmbedding_eval]
  simp only [ShortDraftLatticeCount.coords_eval]
  exact breveE_real_trace_div r _ _

end ActualEisensteinCubic
namespace SqrtBranch
open Complex

private theorem arg_ne_pi_of_re_pos {a : ℂ} (ha : 0 < a.re) : a.arg ≠ Real.pi := by
  intro h
  have := (Complex.arg_eq_pi_iff.mp h).1
  linarith

/--
@isnad1 id=eq.2h2v.s7.75f1bd6dcd0e from=translated src=- shape=81d4a2e7 vocab=7618474e
-/
theorem cpow_half_product {a : ℂ} {r : ℝ} (ha : 0 < a.re) (hr : 0 < r) :
    a ^ (1 / 2 : ℂ) * (((r : ℂ) / a) ^ (1 / 2 : ℂ)) =
      (r : ℂ) ^ (1 / 2 : ℂ) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have harg := arg_ne_pi_of_re_pos ha
  have hlog : Complex.log ((r : ℂ) / a) = (Real.log r : ℂ) - Complex.log a := by
    rw [div_eq_mul_inv, Complex.log_ofReal_mul hr (inv_ne_zero ha0),
      Complex.log_inv a harg]
    ring
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hdiv : (r : ℂ) / a ≠ 0 := div_ne_zero hr0 ha0
  rw [Complex.cpow_def_of_ne_zero ha0,
    Complex.cpow_def_of_ne_zero hdiv,
    Complex.cpow_def_of_ne_zero hr0, hlog, ← Complex.exp_add]
  congr 1
  rw [Complex.ofReal_log hr.le]
  ring

/--
@isnad1 id=eq.2h2v.s7.613db68b4c27 from=translated src=- shape=98589c2c vocab=7618474e
-/
theorem prefactor_product {a : ℂ} {r : ℝ} (ha : 0 < a.re) (hr : 0 < r) :
    (1 / a ^ (1 / 2 : ℂ)) * (1 / (((r : ℂ) / a) ^ (1 / 2 : ℂ))) =
      1 / ((r : ℂ) ^ (1 / 2 : ℂ)) := by
  simpa [div_eq_mul_inv, mul_inv_rev, mul_comm] using
    congrArg (fun z : ℂ => z⁻¹) (cpow_half_product ha hr)

end SqrtBranch

namespace PowerExtraction

/--
@isnad1 id=le.7h6v.s8.1b305b7d808e from=translated src=- shape=4c874bef vocab=5df71cf7
-/
theorem from_mean_square_and_prime_rows_with_loss
    (D ε J A C M : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hC : 1 ≤ C) (hM : 1 ≤ M)
    (hcount : D ^ ((11 / 60 : ℝ) - ε) ≤ M * J)
    (hmean : J * A ^ 2 ≤
      2 * M * D ^ ((21 / 10 : ℝ) + ε) +
        2 * J * C ^ 2 * D ^ (49 / 30 : ℝ)) :
    A ≤ 2 * (M + C) * D ^ ((23 / 24 : ℝ) + ε) := by
  let E : ℝ := (23 / 24 : ℝ) + ε
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hMJpos : 0 < M * J :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hDpos _) hcount
  have hJpos : 0 < J := by
    nlinarith
  have hbase : D ^ ((21 / 10 : ℝ) + ε) ≤
      (M * J) * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      D ^ ((21 / 10 : ℝ) + ε) =
          D ^ ((11 / 60 : ℝ) - ε) *
            D ^ ((23 / 12 : ℝ) + 2 * ε) := by
              rw [← Real.rpow_add hDpos]
              congr 1
              ring
      _ ≤ (M * J) * D ^ ((23 / 12 : ℝ) + 2 * ε) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
  have hpow : M * D ^ ((21 / 10 : ℝ) + ε) ≤
      M ^ 2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      M * D ^ ((21 / 10 : ℝ) + ε) ≤
          M * ((M * J) * D ^ ((23 / 12 : ℝ) + 2 * ε)) :=
            mul_le_mul_of_nonneg_left hbase hMpos.le
      _ = M ^ 2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by ring
  have herr : D ^ (49 / 30 : ℝ) ≤
      D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hD
    linarith
  have hcoeff : 2 * M ^ 2 + 2 * C ^ 2 ≤ 4 * (M + C) ^ 2 := by
    nlinarith [mul_nonneg hMpos.le hCpos.le]
  have hT : 0 ≤ J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by positivity
  have hmain : J * A ^ 2 ≤
      4 * (M + C) ^ 2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      J * A ^ 2 ≤
          2 * M * D ^ ((21 / 10 : ℝ) + ε) +
            2 * J * C ^ 2 * D ^ (49 / 30 : ℝ) := hmean
      _ ≤ 2 * (M ^ 2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε)) +
            2 * J * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
              have hleft :
                  2 * M * D ^ ((21 / 10 : ℝ) + ε) ≤
                    2 * (M ^ 2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε)) := by
                nlinarith [hpow]
              have hright :
                  2 * J * C ^ 2 * D ^ (49 / 30 : ℝ) ≤
                    2 * J * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
                exact mul_le_mul_of_nonneg_left herr (by positivity)
              linarith
      _ = (2 * M ^ 2 + 2 * C ^ 2) *
            (J * D ^ ((23 / 12 : ℝ) + 2 * ε)) := by ring
      _ ≤ 4 * (M + C) ^ 2 *
            (J * D ^ ((23 / 12 : ℝ) + 2 * ε)) :=
              mul_le_mul_of_nonneg_right hcoeff hT
      _ = 4 * (M + C) ^ 2 * J *
            D ^ ((23 / 12 : ℝ) + 2 * ε) := by ring
  have hsq : A ^ 2 ≤
      4 * (M + C) ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    nlinarith
  have hexp : (23 / 12 : ℝ) + 2 * ε = E * 2 := by
    dsimp [E]
    ring
  have hpow2 : (D ^ E) ^ 2 = D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      (D ^ E) ^ 2 = D ^ (E * 2) :=
        (Real.rpow_mul_natCast hDpos.le E 2).symm
      _ = D ^ ((23 / 12 : ℝ) + 2 * ε) := by rw [hexp]
  have htarget : 0 ≤ 2 * (M + C) * D ^ E := by positivity
  apply (sq_le_sq₀ hA htarget).mp
  rw [mul_pow, mul_pow, hpow2]
  nlinarith

end PowerExtraction

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

/--
@isnad1 id=eq.1h7v.s8.06f1b57090fa from=translated src=- shape=1cb657be vocab=4c7f8110
-/
theorem actual_fiber_gaussian_eq_shifted
    (a b x y m n : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) (η : ℝ) :
    Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
      (‖eisEmbedding
        (ActualEisensteinCoordinates.eval x y +
          ActualEisensteinCoordinates.eval a b *
            ActualEisensteinCoordinates.eval m n)‖ ^ 2 : ℂ)) =
      RankTwoEisShift.shifted
        (η * ((a*a-a*b+b*b : ℤ) : ℝ))
        (EisensteinFiberShift.shiftX (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ))
        (EisensteinFiberShift.shiftY (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ))
        (m,n) := by
  have hqZ : a*a-a*b+b*b ≠ 0 :=
    ne_of_gt (coordinate_norm_pos_of_nonzero a b hc)
  have hqR : EisensteinFiberShift.q (a : ℝ) (b : ℝ) ≠ 0 := by
    dsimp [EisensteinFiberShift.q, EisensteinFiberShift.Q]
    exact_mod_cast hqZ
  have hshift := EisensteinFiberShift.exact_shift
    (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ) (m : ℝ) (n : ℝ) hqR
  have hnormC : ((‖eisEmbedding
      (ActualEisensteinCoordinates.eval x y +
        ActualEisensteinCoordinates.eval a b *
          ActualEisensteinCoordinates.eval m n)‖ : ℂ)^2) =
      (((a*a-a*b+b*b)*(m*m-m*n+n*n) +
        ((2*a-b)*x+(2*b-a)*y)*m +
        (-(a+b)*x+(2*a-b)*y)*n +
        (x*x-x*y+y*y) : ℤ) : ℂ) := by
    exact_mod_cast eisEmbedding_fiber_norm_sq a b x y m n
  rw [hnormC]
  dsimp [RankTwoEisShift.shifted, RankTwoEisShift.Q]
  congr 1
  dsimp [EisensteinFiberShift.Q, EisensteinFiberShift.q] at hshift
  have hshiftC := congrArg (fun v : ℝ => (v : ℂ)) hshift
  push_cast at hshiftC ⊢
  linear_combination -(Real.pi : ℂ) * (η : ℂ) * hshiftC

end ActualEisensteinCubic

namespace EisensteinAbelFiber

open scoped Topology
open Filter

end EisensteinAbelFiber

namespace ActualEisensteinCubic

section

open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

end

section

open EisensteinEmbedding ConcreteTraceCRT Complex

def latticeCoordEquiv : O ≃ ℤ × ℤ where
  toFun := ActualEisensteinCoordinates.coords
  invFun z := ActualEisensteinCoordinates.eval z.1 z.2
  left_inv := ActualEisensteinCoordinates.eval_coords
  right_inv z := ShortDraftLatticeCount.coords_eval z.1 z.2

/--
@isnad1 id=summable.1h1v.s7.3dc09635d274 from=translated src=- shape=bf0cd82c vocab=5e82c89f
-/
theorem eis_gaussian_summable {η : ℝ} (hη : 0 < η) :
    Summable (fun z : O => Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
      (‖eisEmbedding z‖ ^ 2 : ℂ))) := by
  have hbase := RankTwoPoisson.eis_gauss_summable hη
  have hcomp : Summable (fun z : O =>
      RankTwoPoisson.eisGauss η (latticeCoordEquiv z)) :=
    (latticeCoordEquiv.summable_iff).2 hbase
  convert hcomp using 1
  funext z
  let p := ActualEisensteinCoordinates.coords z
  have hz : z = ActualEisensteinCoordinates.eval p.1 p.2 :=
    (ActualEisensteinCoordinates.eval_coords z).symm
  rw [hz]
  have hnormC : ((‖eisEmbedding
      (ActualEisensteinCoordinates.eval p.1 p.2)‖ : ℂ)^2) =
      ((p.1*p.1-p.1*p.2+p.2*p.2 : ℤ) : ℂ) := by
    exact_mod_cast eisEmbedding_eval_norm_sq p.1 p.2
  rw [hnormC]
  change _ = RankTwoPoisson.eisGauss η
    (ActualEisensteinCoordinates.coords
      (ActualEisensteinCoordinates.eval p.1 p.2))
  rw [ShortDraftLatticeCount.coords_eval]
  dsimp [RankTwoPoisson.eisGauss, RankTwoPoisson.eisQ]
  congr 1
  push_cast
  ring

/--
@isnad1 id=summable.2h2v.s10.c2e0fd67a827 from=translated src=- shape=5dfdaa10 vocab=c9a10d0b
-/
theorem actual_oscillatory_kernel_summable (c : O) (hc : c ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    Summable (fun z : O =>
      (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
          (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ))) := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  have hbase := (eis_gaussian_summable hη).norm
  apply hbase.of_norm_bounded
  intro z
  simp only [norm_mul]
  rw [AddChar.norm_apply]
  simp

end

end ActualEisensteinCubic
namespace GaussianPhasePointwise

/--
@isnad1 id=le.0h2v.s5.52fa916d0aed from=translated src=- shape=e8ad8558 vocab=95df0439
-/
theorem exp_imag_diff_le (u v : ℝ) :
    ‖Complex.exp (Complex.I * (u : ℂ)) -
      Complex.exp (Complex.I * (v : ℂ))‖ ≤ |u - v| := by
  have heq :
      Complex.exp (Complex.I * (u : ℂ)) -
        Complex.exp (Complex.I * (v : ℂ)) =
      (Complex.exp (Complex.I * ((u - v : ℝ) : ℂ)) - 1) *
        Complex.exp (Complex.I * (v : ℂ)) := by
    rw [sub_mul, one_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [heq, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  simpa only [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := u - v))

/--
@isnad1 id=le.1h3v.s7.5320721d2ccd from=translated src=- shape=7ad7d428 vocab=72014df1
-/
theorem exp_imag_denominator_error (θ A η : ℝ) (hA : 0 ≤ A) :
    ‖Complex.exp (Complex.I * ((θ / (1 + A * η ^ 2) : ℝ) : ℂ)) -
      Complex.exp (Complex.I * (θ : ℂ))‖ ≤
      |θ| * (A * η ^ 2) := by
  let r : ℝ := 1 + A * η ^ 2
  have hAη : 0 ≤ A * η ^ 2 := mul_nonneg hA (sq_nonneg _)
  have hr : 1 ≤ r := by dsimp [r]; linarith
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hdiff : |θ / r - θ| = |θ| * ((r - 1) / r) := by
    have heq : θ / r - θ = -θ * ((r - 1) / r) := by
      field_simp
      ring
    rw [heq, abs_mul, abs_neg, abs_of_nonneg (div_nonneg (by linarith) hrpos.le)]
  have hfrac : (r - 1) / r ≤ r - 1 := by
    apply (div_le_iff₀ hrpos).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hr)]
  have hbound := exp_imag_diff_le (θ / r) θ
  dsimp [r] at hbound ⊢
  calc
    ‖Complex.exp (Complex.I * ((θ / (1 + A * η ^ 2) : ℝ) : ℂ)) -
      Complex.exp (Complex.I * (θ : ℂ))‖ ≤
        |θ / (1 + A * η ^ 2) - θ| := hbound
    _ = |θ| * (((1 + A * η ^ 2) - 1) / (1 + A * η ^ 2)) := hdiff
    _ ≤ |θ| * (A * η ^ 2) := by
      have hfrac' := hfrac
      dsimp [r] at hfrac'
      nlinarith [mul_nonneg (abs_nonneg θ) (sub_nonneg.mpr hfrac')]

end GaussianPhasePointwise

namespace ActualEisensteinCubic

open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

end ActualEisensteinCubic

end

end OAI

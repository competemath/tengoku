import Tengoku.Piirrationalitymeasure.Formalization.SaddlePhaseMaximum
import Tengoku.Seed.RingTheory.Polynomial.Resultant.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The exact elimination polynomials and branch isolation in Appendix A.2. -/

namespace PiIrrationality

def saddleEliminationA {R : Type*} [CommRing R] (x e : R) : R :=
  (3481875 * e ^ 2 - 1160625) * x ^ 3 +
    (-9749175 * e ^ 2 - 7427800 * e + 2785425) * x ^ 2 +
    (9052725 * e ^ 2 + 12998656 * e + 1624833) * x -
    2785425 * e ^ 2 - 5570856 * e + 434655

def saddleEliminationB {R : Type*} [CommRing R] (x e : R) : R :=
  (-1160625 * e ^ 3 + 3481875 * e) * x ^ 3 +
    (3481875 * e ^ 3 + 3713900 * e ^ 2 - 9052725 * e - 3713900) * x ^ 2 +
    (-3481875 * e ^ 3 - 7427800 * e ^ 2 + 3946017 * e + 5570856) * x +
    1160625 * e ^ 3 + 3713900 * e ^ 2 + 1624833 * e + 163460

def saddleEliminationG {R : Type*} [CommRing R] (e : R) : R :=
  17643 * e ^ 3 - 70568 * e ^ 2 + 132777 * e - 7430

def saddleEliminationM {R : Type*} [CommRing R] (e : R) : R :=
  61114327234279 * e ^ 6 + 476161418762182 * e ^ 5 +
    1249735047872147 * e ^ 4 + 1103707235761676 * e ^ 3 -
    510839674922447 * e ^ 2 - 1100344963626938 * e - 597807070530939

noncomputable def saddleEliminationNumerator (z : ℂ) : ℂ :=
  3715 * saddleQ ^ 3 - 232119 * saddleQ ^ 2 * z -
    928475 * saddleQ * z ^ 2 - 1160625 * z ^ 3

/--
@isnad1 id=eq.0h2v.s6.adfa10a832c8 from=translated src=- shape=0ecec6c5 vocab=40a9ef55
-/
theorem saddleElimination_real_imag (x e : ℝ) :
    saddleEliminationNumerator ((x : ℂ) + (e : ℂ) * (1 - x) * Complex.I) =
      ((saddleEliminationA x e : ℝ) : ℂ) +
        ((saddleEliminationB x e : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp [saddleEliminationNumerator, saddleQ, saddleEliminationA, saddleEliminationB,
      pow_succ, Complex.mul_re, Complex.mul_im] <;> ring

/--
@isnad1 id=and.0h0v.s4.94c0f39adf73 from=translated src=- shape=83905ffe vocab=f6960963
-/
theorem saddleElimination_common_root :
    saddleEliminationA saddleX saddleEta = 0 ∧ saddleEliminationB saddleX saddleEta = 0 := by
  have hxy : saddleEta * (1 - saddleX) = saddleY := by
    have hx : saddleX - 1 ≠ 0 := by linarith [saddleX_gt_one]
    unfold saddleEta
    field_simp
    ring
  have hz : ((saddleX : ℂ) + (saddleEta : ℂ) * (1 - saddleX) * Complex.I) =
      (saddleX : ℂ) + (saddleY : ℂ) * Complex.I := by
    have hc := congrArg Complex.ofReal hxy
    push_cast at hc
    rw [hc]
  have hzero : saddleEliminationNumerator
      ((saddleX : ℂ) + (saddleY : ℂ) * Complex.I) = 0 := by
    unfold saddleEliminationNumerator
    rw [← saddle_ratio_mul]
    linear_combination
      ((saddleX : ℂ) + (saddleY : ℂ) * Complex.I) ^ 3 * stationaryCubic_saddleUpper
  rw [← hz, saddleElimination_real_imag] at hzero
  exact ⟨by simpa using congrArg Complex.re hzero, by simpa using congrArg Complex.im hzero⟩

/--
@isnad1 id=lt.2h1v.s5.894c07503eda from=translated src=- shape=ca36100f vocab=48e0abdd
-/
theorem saddleEliminationG_pos {e : ℝ} (he : (9 : ℝ) / 10 ≤ e) (he1 : e ≤ 1) :
    0 < saddleEliminationG e := by
  have hsq : (9 / 10 : ℝ) ^ 2 ≤ e ^ 2 := by nlinarith
  have hcube : (9 / 10 : ℝ) ^ 3 ≤ e ^ 3 := by nlinarith
  have hsq1 : e ^ 2 ≤ 1 := by nlinarith
  unfold saddleEliminationG
  nlinarith

/--
@isnad1 id=and.0h0v.s7.62e372704668 from=translated src=- shape=6f31f623 vocab=24383473
-/
theorem saddleEliminationM_endpoint_signs :
    -(278 : ℝ) / 10 ^ 6 < saddleEliminationM saddleEtaLower ∧
    saddleEliminationM saddleEtaLower < -(277 : ℝ) / 10 ^ 6 ∧
    (356 : ℝ) / 10 ^ 6 < saddleEliminationM saddleEtaUpper ∧
    saddleEliminationM saddleEtaUpper < (357 : ℝ) / 10 ^ 6 := by
  norm_num [saddleEliminationM, saddleEtaLower, saddleEtaUpper]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
open Polynomial in
private theorem cubic_sylvester (a b c d A B C' D : ℝ) :
    Polynomial.sylvester (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d)
      (C A * X ^ 3 + C B * X ^ 2 + C C' * X + C D) 3 3 =
      !![D, 0, 0, d, 0, 0; C', D, 0, c, d, 0; B, C', D, b, c, d;
         A, B, C', a, b, c; 0, A, B, 0, a, b; 0, 0, A, 0, 0, a] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Polynomial.sylvester, Fin.addCases, Polynomial.coeff_add,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_C]
  exact fun h => False.elim ((by decide : ¬ ((2 : Fin 6) ≤ 1)) h)

open Polynomial in
noncomputable def saddleEliminationAPoly (e : ℝ) : ℝ[X] :=
  C (3481875 * e ^ 2 - 1160625) * X ^ 3 +
    C (-9749175 * e ^ 2 - 7427800 * e + 2785425) * X ^ 2 +
    C (9052725 * e ^ 2 + 12998656 * e + 1624833) * X +
    C (-2785425 * e ^ 2 - 5570856 * e + 434655)

open Polynomial in
noncomputable def saddleEliminationBPoly (e : ℝ) : ℝ[X] :=
  C (-1160625 * e ^ 3 + 3481875 * e) * X ^ 3 +
    C (3481875 * e ^ 3 + 3713900 * e ^ 2 - 9052725 * e - 3713900) * X ^ 2 +
    C (-3481875 * e ^ 3 - 7427800 * e ^ 2 + 3946017 * e + 5570856) * X +
    C (1160625 * e ^ 3 + 3713900 * e ^ 2 + 1624833 * e + 163460)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
/--
@isnad1 id=eq.0h1v.s5.697497ad55c8 from=translated src=- shape=a58c482a vocab=4244913a
-/
theorem saddleElimination_resultant (e : ℝ) :
    (saddleEliminationAPoly e).resultant (saddleEliminationBPoly e) 3 3 =
      27587592000000000000 * saddleEliminationG e * saddleEliminationM e := by
  rw [Polynomial.resultant, saddleEliminationAPoly, saddleEliminationBPoly, cubic_sylvester]
  simp (config := { maxSteps := 1000000 }) [Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove]
  unfold saddleEliminationG saddleEliminationM
  ring

/--
@isnad1 id=eq.0h2v.s4.77ba4a8d5313 from=translated src=- shape=9e0fa439 vocab=ce1bf5f0
-/
theorem saddleEliminationAPoly_eval (x e : ℝ) :
    (saddleEliminationAPoly e).eval x = saddleEliminationA x e := by
  simp [saddleEliminationAPoly, saddleEliminationA]
  ring

/--
@isnad1 id=eq.0h2v.s4.cfa71866d480 from=translated src=- shape=9e0fa439 vocab=c774cae0
-/
theorem saddleEliminationBPoly_eval (x e : ℝ) :
    (saddleEliminationBPoly e).eval x = saddleEliminationB x e := by
  simp [saddleEliminationBPoly, saddleEliminationB]
  ring

/--
@isnad1 id=eq.0h0v.s3.b8ae21c2c8b4 from=translated src=- shape=3701a056 vocab=3bfb7f0b
-/
theorem saddleEliminationM_saddleEta : saddleEliminationM saddleEta = 0 := by
  have hA : (saddleEliminationAPoly saddleEta).natDegree ≤ 3 := by
    unfold saddleEliminationAPoly
    compute_degree!
  have hB : (saddleEliminationBPoly saddleEta).natDegree ≤ 3 := by
    unfold saddleEliminationBPoly
    compute_degree!
  obtain ⟨P, Q, _, _, hbezout⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    (saddleEliminationAPoly saddleEta) (saddleEliminationBPoly saddleEta) hA hB (by decide)
  have hzero := congrArg (Polynomial.eval saddleX) hbezout
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    saddleEliminationAPoly_eval, saddleEliminationBPoly_eval,
    saddleElimination_common_root.1, saddleElimination_common_root.2, zero_mul,
    zero_add, saddleElimination_resultant] at hzero
  have hG := saddleEliminationG_pos saddleEta_gt_nine_tenths.le saddleEta_lt_one.le
  exact (mul_eq_zero.mp hzero.symm).resolve_left (mul_ne_zero (by norm_num) hG.ne')

/--
@isnad1 id=strictmo.0h0v.s5.ca49a0f5c2a0 from=translated src=- shape=49b7a648 vocab=7acddbdb
-/
theorem saddleEliminationM_strictMonoOn :
    StrictMonoOn (saddleEliminationM : ℝ → ℝ) (Set.Icc (9 / 10 : ℝ) 1) := by
  intro x hx y hy hxy
  have hxpos : 0 < x := by linarith [hx.1]
  have h3 : y ^ 3 - x ^ 3 ≥ (243 / 100 : ℝ) * (y - x) := by
    have hx2 : (81 / 100 : ℝ) ≤ x ^ 2 := by nlinarith [hx.1]
    have hy2 : (81 / 100 : ℝ) ≤ y ^ 2 := by nlinarith [hy.1]
    have hxy2 : (81 / 100 : ℝ) ≤ x * y := by nlinarith [hx.1, hy.1]
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy.le)
      (show 0 ≤ y ^ 2 + x * y + x ^ 2 - 243 / 100 by linarith)]
  have h2 : y ^ 2 - x ^ 2 ≤ 2 * (y - x) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy.le)
      (show 0 ≤ 2 - (y + x) by linarith [hx.2, hy.2])]
  have h4 := pow_le_pow_left₀ hxpos.le hxy.le 4
  have h5 := pow_le_pow_left₀ hxpos.le hxy.le 5
  have h6 := pow_le_pow_left₀ hxpos.le hxy.le 6
  unfold saddleEliminationM
  nlinarith

/--
@isnad1 id=existsun.0h0v.s5.d1bac66f84d4 from=translated src=- shape=21d151ff vocab=943b1383
-/
theorem saddleEliminationM_unique_root :
    ∃! e : ℝ, e ∈ Set.Icc (9 / 10 : ℝ) 1 ∧ saddleEliminationM e = 0 := by
  refine ⟨saddleEta, ⟨⟨saddleEta_gt_nine_tenths.le, saddleEta_lt_one.le⟩,
    saddleEliminationM_saddleEta⟩, ?_⟩
  intro e he
  exact saddleEliminationM_strictMonoOn.injOn he.1
    ⟨saddleEta_gt_nine_tenths.le, saddleEta_lt_one.le⟩
    (he.2.trans saddleEliminationM_saddleEta.symm)

/--
@isnad1 id=and.0h0v.s3.95cfc065c07b from=translated src=- shape=9cf45692 vocab=0e0ead0b
-/
theorem saddleEliminationM_isolation :
    saddleEtaLower < saddleEta ∧ saddleEta < saddleEtaUpper := by
  have hL : saddleEtaLower ∈ Set.Icc (9 / 10 : ℝ) 1 := by
    norm_num [saddleEtaLower]
  have hU : saddleEtaUpper ∈ Set.Icc (9 / 10 : ℝ) 1 := by
    norm_num [saddleEtaUpper]
  have he : saddleEta ∈ Set.Icc (9 / 10 : ℝ) 1 :=
    ⟨saddleEta_gt_nine_tenths.le, saddleEta_lt_one.le⟩
  have hsign := saddleEliminationM_endpoint_signs
  constructor
  · by_contra! hle
    have h := saddleEliminationM_strictMonoOn.monotoneOn he hL hle
    rw [saddleEliminationM_saddleEta] at h
    linarith [hsign.2.1]
  · by_contra! hle
    have h := saddleEliminationM_strictMonoOn.monotoneOn hU he hle
    rw [saddleEliminationM_saddleEta] at h
    linarith [hsign.2.2.1]

end PiIrrationality

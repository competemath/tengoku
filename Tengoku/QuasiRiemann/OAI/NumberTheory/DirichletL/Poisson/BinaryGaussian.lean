import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.GaussSum.QuadraticNormalization

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

namespace RankTwoComplex

open Real

/--
@isnad1 id=summable.2h2v.s7.b1ff378bca2f from=translated src=- shape=ad2f773d vocab=d8118325
-/
theorem lattice_gaussian_summable_of_re_bound (F : ℤ × ℤ → ℂ)
    {eps : ℝ} (heps : 0 < eps)
    (hbound : ∀ z : ℤ × ℤ,
      eps * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ≤ (F z).re) :
    Summable (fun z : ℤ × ℤ => Complex.exp (-(Real.pi : ℂ) * F z)) := by
  have h1 := RankTwoPoisson.real_gauss_summable heps
  have hmaj : Summable (fun z : ℤ × ℤ =>
      Real.exp (-Real.pi * eps * (z.1 : ℝ) ^ 2) *
      Real.exp (-Real.pi * eps * (z.2 : ℝ) ^ 2)) :=
    h1.mul_of_nonneg h1 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  refine hmaj.of_norm_bounded ?_
  intro z
  have hb := hbound z
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hm := mul_le_mul_of_nonneg_left hb hpi
  have hexp : (-(Real.pi : ℂ) * F z).re ≤
      -Real.pi * eps * (z.1 : ℝ) ^ 2 +
      -Real.pi * eps * (z.2 : ℝ) ^ 2 := by
    simp [Complex.mul_re] at *
    nlinarith [hm]
  simpa only [Complex.norm_exp, Real.exp_add] using
    (Real.exp_le_exp.mpr hexp)

noncomputable def schur (a b d : ℂ) : ℂ := d - b ^ 2 / a

noncomputable def binaryGaussian (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (a * (z.1 : ℂ) ^ 2 + 2 * b * (z.1 : ℂ) * (z.2 : ℂ) + d * (z.2 : ℂ) ^ 2))

noncomputable def firstGaussian (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) / a * (z.1 : ℂ) ^ 2) *
    Complex.exp (-(Real.pi : ℂ) * schur a b d * (z.2 : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * (Complex.I * b / a * (z.1 : ℂ)) * (z.2 : ℂ))

noncomputable def dualGaussian (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) / a * (z.1 : ℂ) ^ 2) *
    Complex.exp (-(Real.pi : ℂ) / (schur a b d) *
      ((z.2 : ℂ) - b / a * (z.1 : ℂ)) ^ 2)

private theorem binary_split (a b d : ℂ) (m n : ℤ) :
    binaryGaussian a b d (m,n) =
      Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * a * (m : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * (-(b * (n : ℂ))) * (m : ℂ)) := by
  dsimp [binaryGaussian]
  rw [← Complex.exp_add]
  congr 1
  ring

private theorem first_exponent_identity {a b d : ℂ} (ha : a ≠ 0) (k n : ℤ) :
    (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2) +
      (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * (-(b * (n : ℂ)))) ^ 2) =
      (-(Real.pi : ℂ) / a * (k : ℂ) ^ 2) +
        (-(Real.pi : ℂ) * schur a b d * (n : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * (Complex.I * b / a * (k : ℂ)) * (n : ℂ)) := by
  dsimp [schur]
  field_simp [ha]
  ring_nf
  simp [Complex.I_sq]

private theorem first_transform_term {a b d : ℂ} (ha : a ≠ 0) (k n : ℤ) :
    Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2) *
      Complex.exp (-(Real.pi : ℂ) / a *
        ((k : ℂ) + Complex.I * (-(b * (n : ℂ)))) ^ 2) =
      firstGaussian a b d (k,n) := by
  rw [← Complex.exp_add, first_exponent_identity ha k n, Complex.exp_add]
  rfl

private theorem first_poisson_slice {a b d : ℂ} (ha : 0 < a.re) (n : ℤ) :
    (∑' m : ℤ, binaryGaussian a b d (m,n)) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, firstGaussian a b d (k,n) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  let C : ℂ := Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2)
  let B : ℂ := -(b * (n : ℂ))
  let F : ℤ → ℂ := fun m => Complex.exp
    (-(Real.pi : ℂ) * a * (m : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (m : ℂ))
  let H : ℤ → ℂ := fun k => Complex.exp
    (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' m : ℤ, binaryGaussian a b d (m,n)) = C * ∑' m : ℤ, F m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    exact binary_split a b d m n
  have hpoisson : (∑' m : ℤ, F m) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k :=
    Complex.tsum_exp_neg_quadratic ha B
  calc
    (∑' m : ℤ, binaryGaussian a b d (m,n)) = C * ∑' m : ℤ, F m := hsplit
    _ = C * ((1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k) := by rw [hpoisson]
    _ = (1 / a ^ (1 / 2 : ℂ)) * (C * ∑' k : ℤ, H k) := by ring
    _ = (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, firstGaussian a b d (k,n) := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      exact first_transform_term ha0 k n

private theorem second_poisson_slice {a b d : ℂ}
    (hδ : 0 < (schur a b d).re) (k : ℤ) :
    (∑' n : ℤ, firstGaussian a b d (k,n)) =
      (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' l : ℤ, dualGaussian a b d (k,l) := by
  have hδ0 : schur a b d ≠ 0 := by
    intro h
    simp [h] at hδ
  let A : ℂ := schur a b d
  let B : ℂ := Complex.I * b / a * (k : ℂ)
  let C : ℂ := Complex.exp (-(Real.pi : ℂ) / a * (k : ℂ) ^ 2)
  let F : ℤ → ℂ := fun n => Complex.exp
    (-(Real.pi : ℂ) * A * (n : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (n : ℂ))
  let H : ℤ → ℂ := fun l => Complex.exp
    (-(Real.pi : ℂ) / A * ((l : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' n : ℤ, firstGaussian a b d (k,n)) = C * ∑' n : ℤ, F n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rfl
  have hpoisson : (∑' n : ℤ, F n) =
      (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l :=
    Complex.tsum_exp_neg_quadratic hδ B
  have hterm (l : ℤ) : C * H l = dualGaussian a b d (k,l) := by
    have hb : Complex.I * B = -(b / a * (k : ℂ)) := by
      dsimp [B]
      field_simp
      ring_nf
      simp [Complex.I_sq]
    dsimp [H, dualGaussian, C, A]
    rw [hb]
    ring_nf
  calc
    (∑' n : ℤ, firstGaussian a b d (k,n)) = C * ∑' n : ℤ, F n := hsplit
    _ = C * ((1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l) := by rw [hpoisson]
    _ = (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) := by ring
    _ = (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          ∑' l : ℤ, dualGaussian a b d (k,l) := by
      change (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) =
        (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, dualGaussian a b d (k,l)
      congr 1
      rw [← tsum_mul_left]
      exact tsum_congr hterm

/--
@isnad1 id=eq.5h3v.s8.9909eb851630 from=translated src=- shape=b5df9be6 vocab=b86676a3
-/
theorem binary_gaussian_poisson {a b d : ℂ}
    (ha : 0 < a.re) (hδ : 0 < (schur a b d).re)
    (hO : Summable (binaryGaussian a b d))
    (hM : Summable (firstGaussian a b d))
    (hD : Summable (dualGaussian a b d)) :
    (∑' z : ℤ × ℤ, binaryGaussian a b d z) =
      (1 / a ^ (1 / 2 : ℂ)) *
        (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, dualGaussian a b d z := by
  have hOcomm :
      (∑' n : ℤ, ∑' m : ℤ, binaryGaussian a b d (m,n)) =
        ∑' m : ℤ, ∑' n : ℤ, binaryGaussian a b d (m,n) :=
    (show Summable (Function.uncurry (fun m n : ℤ => binaryGaussian a b d (m,n)))
      from hO).tsum_comm
  have hMcomm :
      (∑' n : ℤ, ∑' k : ℤ, firstGaussian a b d (k,n)) =
        ∑' k : ℤ, ∑' n : ℤ, firstGaussian a b d (k,n) :=
    (show Summable (Function.uncurry (fun k n : ℤ => firstGaussian a b d (k,n)))
      from hM).tsum_comm
  calc
    (∑' z : ℤ × ℤ, binaryGaussian a b d z) =
        ∑' m : ℤ, ∑' n : ℤ, binaryGaussian a b d (m,n) := hO.tsum_prod
    _ = ∑' n : ℤ, ∑' m : ℤ, binaryGaussian a b d (m,n) := hOcomm.symm
    _ = ∑' n : ℤ, (1 / a ^ (1 / 2 : ℂ)) *
          ∑' k : ℤ, firstGaussian a b d (k,n) := by
      apply tsum_congr
      intro n
      exact first_poisson_slice ha n
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' n : ℤ, ∑' k : ℤ, firstGaussian a b d (k,n)) := tsum_mul_left
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' n : ℤ, firstGaussian a b d (k,n)) := by
      rw [hMcomm]
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
            ∑' l : ℤ, dualGaussian a b d (k,l)) := by
      congr 1
      apply tsum_congr
      intro k
      exact second_poisson_slice hδ k
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' l : ℤ, dualGaussian a b d (k,l)) := by
      rw [tsum_mul_left]
      ring
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          ∑' z : ℤ × ℤ, dualGaussian a b d z := by
      rw [hD.tsum_prod]

end RankTwoComplex

namespace GaussianShiftedPartition

open ActualEisensteinCubic ConcreteTraceCRT ConcreteBreveE

noncomputable def representative (c : O) (r : O ⧸ Ideal.span {c}) : O :=
  Classical.choose (Ideal.Quotient.mk_surjective r)

/--
@isnad1 id=eq.0h2v.s9.77a3ed61f1c7 from=translated src=- shape=dff41b6e vocab=2c6d6148
-/
theorem representative_spec (c : O) (r : O ⧸ Ideal.span {c}) :
    Ideal.Quotient.mk (Ideal.span {c}) (representative c r) = r :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective r)

/--
@isnad1 id=eq.2h2v.s11.ccbc34c593ef from=translated src=- shape=8eaf988b vocab=b21c86ce
-/
theorem actual_quadratic_shifted_partition (c : O) (hc : c ≠ 0)
    (W : O → ℂ)
    (hsum : Summable (fun z : O =>
      (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z)) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z) =
      ∑ r : O ⧸ Ideal.span {c},
        (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
          (r ^ 2) *
          ∑' w : O, W (representative c r + c*w) := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [GaussianAbelPartition.actual_quadratic_gaussian_partition c hc W hsum]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  exact GaussianFiberEquiv.fiber_tsum c hc r
    (representative c r) (representative_spec c r) W

end GaussianShiftedPartition

namespace RankTwoAffine

open RankTwoComplex

noncomputable def binaryGaussian (a b d u v : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (a * (z.1 : ℂ) ^ 2 + 2 * b * (z.1 : ℂ) * (z.2 : ℂ) + d * (z.2 : ℂ) ^ 2) +
    2 * (Real.pi : ℂ) * (u * (z.1 : ℂ) + v * (z.2 : ℂ)))

noncomputable def firstGaussian (a b d u v : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) / a * ((z.1 : ℂ) + Complex.I * u) ^ 2) *
    Complex.exp (-(Real.pi : ℂ) * schur a b d * (z.2 : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) *
        (v + Complex.I * b / a * ((z.1 : ℂ) + Complex.I * u)) * (z.2 : ℂ))

noncomputable def dualGaussian (a b d u v : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) / a * ((z.1 : ℂ) + Complex.I * u) ^ 2) *
    Complex.exp (-(Real.pi : ℂ) / (schur a b d) *
      ((z.2 : ℂ) + Complex.I *
        (v + Complex.I * b / a * ((z.1 : ℂ) + Complex.I * u))) ^ 2)

private theorem binary_split (a b d u v : ℂ) (m n : ℤ) :
    binaryGaussian a b d u v (m,n) =
      Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * v * (n : ℂ)) *
        Complex.exp (-(Real.pi : ℂ) * a * (m : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * (u - b * (n : ℂ)) * (m : ℂ)) := by
  dsimp [binaryGaussian]
  rw [← Complex.exp_add]
  congr 1
  ring

private theorem first_exponent_identity {a b d u v : ℂ} (ha : a ≠ 0) (k n : ℤ) :
    (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * v * (n : ℂ)) +
      (-(Real.pi : ℂ) / a *
        ((k : ℂ) + Complex.I * (u - b * (n : ℂ))) ^ 2) =
      (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * u) ^ 2) +
        (-(Real.pi : ℂ) * schur a b d * (n : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) *
            (v + Complex.I * b / a * ((k : ℂ) + Complex.I * u)) * (n : ℂ)) := by
  dsimp [schur]
  field_simp [ha]
  ring_nf
  simp [Complex.I_sq]

private theorem first_transform_term {a b d u v : ℂ} (ha : a ≠ 0) (k n : ℤ) :
    Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * v * (n : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) / a *
        ((k : ℂ) + Complex.I * (u - b * (n : ℂ))) ^ 2) =
      firstGaussian a b d u v (k,n) := by
  rw [← Complex.exp_add, first_exponent_identity ha k n, Complex.exp_add]
  rfl

private theorem first_poisson_slice {a b d u v : ℂ} (ha : 0 < a.re) (n : ℤ) :
    (∑' m : ℤ, binaryGaussian a b d u v (m,n)) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, firstGaussian a b d u v (k,n) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  let C : ℂ := Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2 +
    2 * (Real.pi : ℂ) * v * (n : ℂ))
  let B : ℂ := u - b * (n : ℂ)
  let F : ℤ → ℂ := fun m => Complex.exp
    (-(Real.pi : ℂ) * a * (m : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (m : ℂ))
  let H : ℤ → ℂ := fun k => Complex.exp
    (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' m : ℤ, binaryGaussian a b d u v (m,n)) = C * ∑' m : ℤ, F m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    exact binary_split a b d u v m n
  have hpoisson : (∑' m : ℤ, F m) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k :=
    Complex.tsum_exp_neg_quadratic ha B
  calc
    (∑' m : ℤ, binaryGaussian a b d u v (m,n)) = C * ∑' m : ℤ, F m := hsplit
    _ = C * ((1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k) := by rw [hpoisson]
    _ = (1 / a ^ (1 / 2 : ℂ)) * (C * ∑' k : ℤ, H k) := by ring
    _ = (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, firstGaussian a b d u v (k,n) := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      exact first_transform_term ha0 k n

private theorem second_poisson_slice {a b d u v : ℂ}
    (hδ : 0 < (schur a b d).re) (k : ℤ) :
    (∑' n : ℤ, firstGaussian a b d u v (k,n)) =
      (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' l : ℤ, dualGaussian a b d u v (k,l) := by
  let A : ℂ := schur a b d
  let B : ℂ := v + Complex.I * b / a * ((k : ℂ) + Complex.I * u)
  let C : ℂ := Complex.exp (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * u) ^ 2)
  let F : ℤ → ℂ := fun n => Complex.exp
    (-(Real.pi : ℂ) * A * (n : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (n : ℂ))
  let H : ℤ → ℂ := fun l => Complex.exp
    (-(Real.pi : ℂ) / A * ((l : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' n : ℤ, firstGaussian a b d u v (k,n)) = C * ∑' n : ℤ, F n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rfl
  have hpoisson : (∑' n : ℤ, F n) =
      (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l :=
    Complex.tsum_exp_neg_quadratic hδ B
  calc
    (∑' n : ℤ, firstGaussian a b d u v (k,n)) = C * ∑' n : ℤ, F n := hsplit
    _ = C * ((1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l) := by rw [hpoisson]
    _ = (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) := by ring
    _ = (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          ∑' l : ℤ, dualGaussian a b d u v (k,l) := by
      change (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) =
        (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, dualGaussian a b d u v (k,l)
      congr 1
      rw [← tsum_mul_left]
      rfl

/--
@isnad1 id=eq.5h5v.s8.19938e68e419 from=translated src=- shape=023703ae vocab=37bd9888
-/
theorem affine_gaussian_poisson {a b d u v : ℂ}
    (ha : 0 < a.re) (hδ : 0 < (schur a b d).re)
    (hO : Summable (binaryGaussian a b d u v))
    (hM : Summable (firstGaussian a b d u v))
    (hD : Summable (dualGaussian a b d u v)) :
    (∑' z : ℤ × ℤ, binaryGaussian a b d u v z) =
      (1 / a ^ (1 / 2 : ℂ)) *
        (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, dualGaussian a b d u v z := by
  have hOcomm :
      (∑' n : ℤ, ∑' m : ℤ, binaryGaussian a b d u v (m,n)) =
        ∑' m : ℤ, ∑' n : ℤ, binaryGaussian a b d u v (m,n) :=
    (show Summable (Function.uncurry (fun m n : ℤ => binaryGaussian a b d u v (m,n)))
      from hO).tsum_comm
  have hMcomm :
      (∑' n : ℤ, ∑' k : ℤ, firstGaussian a b d u v (k,n)) =
        ∑' k : ℤ, ∑' n : ℤ, firstGaussian a b d u v (k,n) :=
    (show Summable (Function.uncurry (fun k n : ℤ => firstGaussian a b d u v (k,n)))
      from hM).tsum_comm
  calc
    (∑' z : ℤ × ℤ, binaryGaussian a b d u v z) =
        ∑' m : ℤ, ∑' n : ℤ, binaryGaussian a b d u v (m,n) := hO.tsum_prod
    _ = ∑' n : ℤ, ∑' m : ℤ, binaryGaussian a b d u v (m,n) := hOcomm.symm
    _ = ∑' n : ℤ, (1 / a ^ (1 / 2 : ℂ)) *
          ∑' k : ℤ, firstGaussian a b d u v (k,n) := by
      apply tsum_congr
      intro n
      exact first_poisson_slice ha n
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' n : ℤ, ∑' k : ℤ, firstGaussian a b d u v (k,n)) := tsum_mul_left
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' n : ℤ, firstGaussian a b d u v (k,n)) := by
      rw [hMcomm]
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
            ∑' l : ℤ, dualGaussian a b d u v (k,l)) := by
      congr 1
      apply tsum_congr
      intro k
      exact second_poisson_slice hδ k
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' l : ℤ, dualGaussian a b d u v (k,l)) := by
      rw [tsum_mul_left]
      ring
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          ∑' z : ℤ × ℤ, dualGaussian a b d u v z := by
      rw [hD.tsum_prod]

end RankTwoAffine

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

/--
@isnad1 id=eq.0h2v.s6.c28851fba51b from=translated src=- shape=beb26c9e vocab=d9513d23
-/
theorem eisEmbedding_eval_norm_sq (x y : ℤ) :
    ‖eisEmbedding (ActualEisensteinCoordinates.eval x y)‖ ^ 2 =
      (x*x-x*y+y*y : ℤ) := by
  rw [eisEmbedding_eval, ← Complex.normSq_eq_norm_sq]
  have hre : ((x : ℂ) + (y : ℂ) * omega3).re =
      (x : ℝ) - (y : ℝ) / 2 := by
    simp [omega3, Complex.add_re, Complex.mul_re]
    ring
  have him : ((x : ℂ) + (y : ℂ) * omega3).im =
      (y : ℝ) * Real.sqrt 3 / 2 := by
    simp [omega3, Complex.add_im, Complex.mul_im]
    ring
  rw [Complex.normSq_apply, hre, him]
  have hs : (Real.sqrt 3)^2 = (3:ℝ) := Real.sq_sqrt (by norm_num)
  push_cast
  nlinarith

/--
@isnad1 id=eq.0h6v.s7.ea843e170047 from=translated src=- shape=992a9971 vocab=7afcf051
-/
theorem fiber_coordinates (a b x y m n : ℤ) :
    ActualEisensteinCoordinates.eval x y +
      ActualEisensteinCoordinates.eval a b *
        ActualEisensteinCoordinates.eval m n =
    ActualEisensteinCoordinates.eval (x + a*m-b*n)
      (y+b*m+(a-b)*n) := by
  rw [ActualEisensteinCoordinates.eval_mul]
  simp only [ActualEisensteinCoordinates.eval]
  push_cast
  ring

/--
@isnad1 id=other.0h6v.s8.4339d103c558 from=translated src=- shape=6cf3c0c6 vocab=01d1c51b
-/
theorem fiber_quadratic_expansion (a b x y m n : ℤ) :
    let q := a*a-a*b+b*b
    let X := x+a*m-b*n
    let Y := y+b*m+(a-b)*n
    X*X-X*Y+Y*Y =
      q*(m*m-m*n+n*n) +
      ((2*a-b)*x+(2*b-a)*y)*m +
      (-(a+b)*x+(2*a-b)*y)*n +
      (x*x-x*y+y*y) := by
  dsimp
  ring

/--
@isnad1 id=eq.0h6v.s8.c32457a52c19 from=translated src=- shape=ab2fe8e7 vocab=906e72e6
-/
theorem eisEmbedding_fiber_norm_sq (a b x y m n : ℤ) :
    ‖eisEmbedding
      (ActualEisensteinCoordinates.eval x y +
        ActualEisensteinCoordinates.eval a b *
          ActualEisensteinCoordinates.eval m n)‖ ^ 2 =
      ((a*a-a*b+b*b)*(m*m-m*n+n*n) +
      ((2*a-b)*x+(2*b-a)*y)*m +
      (-(a+b)*x+(2*a-b)*y)*n +
      (x*x-x*y+y*y) : ℤ) := by
  rw [fiber_coordinates, eisEmbedding_eval_norm_sq]
  exact_mod_cast fiber_quadratic_expansion a b x y m n

/--
@isnad1 id=lt.1h2v.s6.4bb9b078f779 from=translated src=- shape=db59c338 vocab=9687b187
-/
theorem coordinate_norm_pos_of_nonzero (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    0 < a*a-a*b+b*b := by
  have he : eisEmbedding (ActualEisensteinCoordinates.eval a b) ≠ 0 :=
    ConcreteTraceCRT.eisEmbedding_ne_zero hc
  have hn : 0 < ‖eisEmbedding (ActualEisensteinCoordinates.eval a b)‖ :=
    norm_pos_iff.mpr he
  have heq := eisEmbedding_eval_norm_sq a b
  exact_mod_cast (show (0:ℝ) < (a*a-a*b+b*b : ℤ) by
    rw [← heq]
    positivity)

end ActualEisensteinCubic

namespace RankTwoEisShift

noncomputable def Q (x y : ℝ) : ℝ := x ^ 2 - x * y + y ^ 2

noncomputable def shifted (t x y : ℝ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (((-Real.pi * t * Q ((z.1 : ℝ) + x) ((z.2 : ℝ) + y) : ℝ) : ℂ))

noncomputable def A (t : ℝ) : ℂ := (t : ℂ)
noncomputable def B (t : ℝ) : ℂ := ((-t / 2 : ℝ) : ℂ)
noncomputable def D (t : ℝ) : ℂ := (t : ℂ)
noncomputable def U (t x y : ℝ) : ℂ := ((-t * (x - y / 2) : ℝ) : ℂ)
noncomputable def V (t x y : ℝ) : ℂ := ((-t * (y - x / 2) : ℝ) : ℂ)
noncomputable def C (t x y : ℝ) : ℂ :=
  Complex.exp (((-Real.pi * t * Q x y : ℝ) : ℂ))

noncomputable def dualPhase (k l : ℤ) (x y : ℝ) : ℂ :=
  Complex.exp ((((2 * Real.pi * ((k : ℝ) * x + (l : ℝ) * y) : ℝ) : ℂ)) * Complex.I)

noncomputable def middlePhase (k n : ℤ) (x y : ℝ) : ℂ :=
  Complex.exp ((((2 * Real.pi * (k : ℝ) * (x - ((n : ℝ) + y) / 2) : ℝ) : ℂ)) * Complex.I)

/--
@isnad1 id=eq.0h4v.s4.df8ae782a79a from=translated src=- shape=bd1a6281 vocab=536454ff
-/
theorem dualPhase_norm (k l : ℤ) (x y : ℝ) :
    ‖dualPhase k l x y‖ = 1 := by
  simp [dualPhase, Complex.norm_exp, Complex.mul_re]

end RankTwoEisShift

end

end OAI

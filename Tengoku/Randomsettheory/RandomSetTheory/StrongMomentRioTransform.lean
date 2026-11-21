/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentIntermediateTransform

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Closing the deterministic transform estimate in Rio's strong-moment argument

This file proves the first branch of the deterministic calculation in the proof
of Rio's strong-moment Fuk--Nagaev inequality.  In particular, it formalizes the
monotonicity of `t⁻² ℓ₁(t)`, inequalities (3.19)--(3.20), and combines that
branch with the Bernstein branch and the minimum estimate (3.23).

The results here concern only the deterministic Chernoff exponent.  They do not
assert the maximal martingale or empirical-process inequality.
-/

open Real Set Finset
open scoped BigOperators

noncomputable section

namespace ProbabilityTheory

/-! ## Scaling of Chernoff transforms -/

/-- Rescaling the Laplace parameter by a positive factor rescales the
Chernoff transform by at most the same factor.  Equality also holds, but this
one-sided form is exactly what is needed for homogenization.
@isnad1 id=le.3h3v.s6.91d4f6e1e23b from=translated src=- shape=48a6eca4 vocab=2362af4c
-/
theorem chernoffTransform_comp_mul_le_mul
    {psi : ℝ → ℝ} {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x)
    (hpsi : ∀ t, 0 < t → 0 ≤ psi t) :
    chernoffTransform (fun t => psi (a * t)) x ≤
      a * chernoffTransform psi x := by
  have hcomp : ∀ t : ℝ, 0 < t → 0 ≤ psi (a * t) := by
    intro t ht
    exact hpsi (a * t) (mul_pos ha ht)
  have hbComp := bddBelow_range_chernoffObjective hx hcomp
  refine le_of_forall_pos_le_add fun epsilon hepsilon => ?_
  obtain ⟨r, ⟨s, hs⟩, hrs⟩ := Real.lt_sInf_add_pos
    (Set.range_nonempty (chernoffObjective psi x))
    (div_pos hepsilon ha)
  subst r
  have heval := chernoffTransform_le_objective
    (psi := fun t => psi (a * t)) (x := x)
    (t := s / a) (div_pos s.property ha) hbComp
  have harg : a * (s / a) = s := by field_simp [ha.ne']
  rw [harg] at heval
  have hobjective :
      (psi s + x) / (s / a) =
        a * chernoffObjective psi x s := by
    unfold chernoffObjective
    field_simp [ha.ne', s.property.ne']
  rw [hobjective] at heval
  calc
    chernoffTransform (fun t => psi (a * t)) x ≤
        a * chernoffObjective psi x s := heval
    _ ≤ a * (chernoffTransform psi x + epsilon / a) :=
      mul_le_mul_of_nonneg_left hrs.le ha.le
    _ = a * chernoffTransform psi x + epsilon := by
      field_simp [ha.ne']

/-! ## Homogeneous strong-moment scale -/

/-- The natural linear scale associated with a positive aggregate `q`-th
moment `Q`.-/
def strongMomentQScale (q : ℕ) (Q : ℝ) : ℝ :=
  Q ^ (1 / (q : ℝ))

/--
@isnad1 id=lt.1h2v.s4.da678e946130 from=translated src=- shape=696abc3b vocab=d456a097
-/
theorem strongMomentQScale_pos
    {q : ℕ} {Q : ℝ} (hQ : 0 < Q) :
    0 < strongMomentQScale q Q :=
  Real.rpow_pos_of_pos hQ _

/-- Raising the natural scale back to order `q` recovers `Q`.
@isnad1 id=eq.2h2v.s5.db57e188c8e1 from=translated src=- shape=56a096fd vocab=4100bb4c
-/
theorem strongMomentQScale_pow
    {q : ℕ} (hq : 1 ≤ q) {Q : ℝ} (hQ : 0 < Q) :
    strongMomentQScale q Q ^ q = Q := by
  unfold strongMomentQScale
  simpa only [one_div] using
    (Real.rpow_inv_natCast_pow hQ.le (by omega : q ≠ 0))

/-- Homogeneity of every interpolated moment coefficient.
@isnad1 id=eq.3h4v.s6.1bb4a36bce66 from=translated src=- shape=933e533d vocab=bb32eb2e
-/
theorem interpolatedStrongMomentCoefficient_eq_scale_pow_mul
    (q k : ℕ) (hq : 3 ≤ q) {V Q : ℝ}
    (hV : 0 < V) (hQ : 0 < Q) :
    interpolatedStrongMomentCoefficient q V Q k =
      strongMomentQScale q Q ^ k *
        interpolatedStrongMomentCoefficient q
          (V / strongMomentQScale q Q ^ 2) 1 k := by
  let a : ℝ := strongMomentQScale q Q
  have ha : 0 < a := strongMomentQScale_pos hQ
  have hVeq : V = a ^ 2 * (V / a ^ 2) := by
    field_simp [ha.ne']
  have hQeq : Q = a ^ q :=
    (strongMomentQScale_pow (by omega) hQ).symm
  have hV0 : 0 ≤ V / a ^ 2 := (div_pos hV (sq_pos_of_pos ha)).le
  unfold interpolatedStrongMomentCoefficient
  change V ^ strongMomentSecondWeight q k *
      Q ^ strongMomentQWeight q k =
    a ^ k *
      ((V / a ^ 2) ^ strongMomentSecondWeight q k *
        1 ^ strongMomentQWeight q k)
  nth_rewrite 1 [hVeq]
  nth_rewrite 1 [hQeq]
  rw [Real.mul_rpow (sq_nonneg a) hV0,
    ← Real.rpow_natCast_mul ha.le 2 (strongMomentSecondWeight q k),
    ← Real.rpow_natCast_mul ha.le q (strongMomentQWeight q k)]
  have hpowers :
      a ^ ((2 : ℝ) * strongMomentSecondWeight q k) *
          a ^ ((q : ℝ) * strongMomentQWeight q k) = a ^ k := by
    rw [← Real.rpow_add ha,
      two_mul_strongMomentSecondWeight_add_q_mul_strongMomentQWeight hq,
      Real.rpow_natCast]
  rw [one_rpow]
  calc
    a ^ ((2 : ℝ) * strongMomentSecondWeight q k) *
          (V / a ^ 2) ^ strongMomentSecondWeight q k *
          a ^ ((q : ℝ) * strongMomentQWeight q k) =
      (a ^ ((2 : ℝ) * strongMomentSecondWeight q k) *
          a ^ ((q : ℝ) * strongMomentQWeight q k)) *
        (V / a ^ 2) ^ strongMomentSecondWeight q k := by ring
    _ = a ^ k * (V / a ^ 2) ^ strongMomentSecondWeight q k := by
      rw [hpowers]
    _ = a ^ k *
        ((V / a ^ 2) ^ strongMomentSecondWeight q k * 1) := by ring

/-- Homogeneity of the finite intermediate exponent under simultaneous
rescaling of `V`, `Q`, and the Laplace parameter.
@isnad1 id=eq.3h4v.s6.292c8d040d19 from=translated src=- shape=b1d544a9 vocab=58be1799
-/
theorem strongMomentIntermediateExponent_eq_scaled_one
    (q : ℕ) (hq : 3 ≤ q) {V Q t : ℝ}
    (hV : 0 < V) (hQ : 0 < Q) :
    strongMomentIntermediateExponent q V Q t =
      strongMomentIntermediateExponent q
        (V / strongMomentQScale q Q ^ 2) 1
        (strongMomentQScale q Q * t) := by
  unfold strongMomentIntermediateExponent
  apply Finset.sum_congr rfl
  intro k hk
  rw [interpolatedStrongMomentCoefficient_eq_scale_pow_mul q k hq hV hQ,
    mul_pow]
  ring

/-- Homogeneity of the full deterministic Rio exponent.
@isnad1 id=eq.4h5v.s6.6c80cca16dc5 from=translated src=- shape=46c0c75d vocab=30e2dc32
-/
theorem rioStrongMomentExponent_eq_scaled_one
    (q : ℕ) (hq : 3 ≤ q) {V Q y t : ℝ}
    (hV : 0 < V) (hQ : 0 < Q) (hy : 0 < y) :
    rioStrongMomentExponent q V Q y t =
      rioStrongMomentExponent q
        (V / strongMomentQScale q Q ^ 2) 1
        (y / strongMomentQScale q Q)
        (strongMomentQScale q Q * t) := by
  let a : ℝ := strongMomentQScale q Q
  have ha : 0 < a := strongMomentQScale_pos hQ
  have haPow : a ^ q = Q := strongMomentQScale_pow (by omega) hQ
  have hgaussian : gaussianChernoffExponent V t =
      gaussianChernoffExponent (V / a ^ 2) (a * t) := by
    unfold gaussianChernoffExponent
    field_simp [ha.ne']
  have hintermediate : strongMomentIntermediateExponent q V Q t =
      strongMomentIntermediateExponent q (V / a ^ 2) 1 (a * t) := by
    simpa only [a] using
      strongMomentIntermediateExponent_eq_scaled_one q hq hV hQ
  have harg : (a * t) * (y / a) = t * y := by
    field_simp [ha.ne']
  have hcoefficient : 1 / (y / a) ^ q = Q / y ^ q := by
    rw [div_pow, haPow]
    field_simp [ha.ne', hy.ne']
  have htail : exactStrongMomentTailExponent q Q y t =
      exactStrongMomentTailExponent q 1 (y / a) (a * t) := by
    unfold exactStrongMomentTailExponent
    rw [harg, ← hcoefficient]
  unfold rioStrongMomentExponent
  change gaussianChernoffExponent V t +
      strongMomentIntermediateExponent q V Q t +
        exactStrongMomentTailExponent q Q y t =
    gaussianChernoffExponent (V / a ^ 2) (a * t) +
      strongMomentIntermediateExponent q (V / a ^ 2) 1 (a * t) +
        exactStrongMomentTailExponent q 1 (y / a) (a * t)
  rw [hgaussian, hintermediate, htail]

/-! ## The normalized intermediate polynomial -/

/-- The polynomial obtained from Rio's intermediate exponent after factoring
out `t²`.  This definition is meaningful at `t = 0`, unlike literal division
by `t²`.-/
def normalizedStrongMomentIntermediateExponent
    (q : ℕ) (V Q t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ico 3 q,
    t ^ (k - 2) / (k.factorial : ℝ) *
      interpolatedStrongMomentCoefficient q V Q k

/-- Exact factorization `ℓ₁(t) = t² (t⁻² ℓ₁(t))`.
@isnad1 id=eq.0h4v.s5.415b1682f0e3 from=translated src=- shape=586b2597 vocab=9da3e753
-/
theorem strongMomentIntermediateExponent_eq_sq_mul_normalized
    (q : ℕ) (V Q t : ℝ) :
    strongMomentIntermediateExponent q V Q t =
      t ^ 2 * normalizedStrongMomentIntermediateExponent q V Q t := by
  unfold strongMomentIntermediateExponent
    normalizedStrongMomentIntermediateExponent
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk2 : 2 ≤ k := by
    have := (Finset.mem_Ico.mp hk).1
    omega
  have hpow : t ^ k = t ^ 2 * t ^ (k - 2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  ring

/-- Rio's observation that `t ↦ t⁻² ℓ₁(t)` is increasing on the
nonnegative half-line.
@isnad1 id=monotone.2h3v.s5.f5e8968f1fc5 from=translated src=- shape=7f15fc97 vocab=35a87b83
-/
theorem monotoneOn_normalizedStrongMomentIntermediateExponent
    (q : ℕ) {V Q : ℝ} (hV : 0 ≤ V) (hQ : 0 ≤ Q) :
    MonotoneOn (normalizedStrongMomentIntermediateExponent q V Q)
      (Set.Ici 0) := by
  intro a ha b hb hab
  unfold normalizedStrongMomentIntermediateExponent
  apply Finset.sum_le_sum
  intro k hk
  have hpow : a ^ (k - 2) ≤ b ^ (k - 2) :=
    pow_le_pow_left₀ ha hab _
  have hfac : 0 ≤ (k.factorial : ℝ) := by positivity
  have hcoeff : 0 ≤ interpolatedStrongMomentCoefficient q V Q k :=
    interpolatedStrongMomentCoefficient_nonneg q k hV hQ
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hpow hfac) hcoeff

/-- A division-free consequence of the preceding monotonicity.  This is the
precise comparison used between the Laplace parameters `x / y` and `q / e`.
@isnad1 id=le.5h5v.s7.17a469c761dd from=translated src=- shape=2ba70bae vocab=9a043dff
-/
theorem one_div_mul_strongMomentIntermediateExponent_le
    (q : ℕ) {V Q a b : ℝ}
    (hV : 0 ≤ V) (hQ : 0 ≤ Q)
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    (1 / a) * strongMomentIntermediateExponent q V Q a ≤
      (a / b ^ 2) * strongMomentIntermediateExponent q V Q b := by
  rw [strongMomentIntermediateExponent_eq_sq_mul_normalized,
    strongMomentIntermediateExponent_eq_sq_mul_normalized]
  have hmono := monotoneOn_normalizedStrongMomentIntermediateExponent
    q hV hQ ha.le hb.le hab
  calc
    (1 / a) *
        (a ^ 2 * normalizedStrongMomentIntermediateExponent q V Q a) =
      a * normalizedStrongMomentIntermediateExponent q V Q a := by
        field_simp [ha.ne']
    _ ≤ a * normalizedStrongMomentIntermediateExponent q V Q b :=
      mul_le_mul_of_nonneg_left hmono ha.le
    _ = (a / b ^ 2) *
        (b ^ 2 * normalizedStrongMomentIntermediateExponent q V Q b) := by
      field_simp [hb.ne']

/-! ## Rio's scale estimate (3.19) -/

/-- If `exp x ≤ y^q`, then the evaluation parameter used for the tail
branch satisfies `x/y ≤ q/e`.  This is (3.19), stated without introducing
`z = exp x`.
@isnad1 id=le.3h3v.s6.d05ee0a88eb0 from=translated src=- shape=ff6212d0 vocab=eec27af9
-/
theorem div_le_natCast_div_exp_one_of_exp_le_pow
    (q : ℕ) (hq : 1 ≤ q) {x y : ℝ}
    (hy : 0 < y) (hscale : Real.exp x ≤ y ^ q) :
    x / y ≤ (q : ℝ) / Real.exp 1 := by
  have hlogScale : x ≤ (q : ℝ) * Real.log y := by
    have hlog := Real.log_le_log (Real.exp_pos x) hscale
    simpa only [Real.log_exp, Real.log_pow, Nat.cast_ofNat] using hlog
  have hlogY : Real.log y ≤ y / Real.exp 1 := by
    have h := Real.log_le_sub_one_of_pos
      (div_pos hy (Real.exp_pos 1))
    rw [Real.log_div hy.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
    linarith
  have hq0 : 0 ≤ (q : ℝ) := by
    exact_mod_cast (show 0 ≤ q by omega)
  have hxy : x ≤ (q : ℝ) * (y / Real.exp 1) :=
    hlogScale.trans (mul_le_mul_of_nonneg_left hlogY hq0)
  apply (div_le_iff₀ hy).2
  calc
    x ≤ (q : ℝ) * (y / Real.exp 1) := hxy
    _ = ((q : ℝ) / Real.exp 1) * y := by ring

/-- Under the same scale condition, the truncation level is at least one.
The strict form is useful because `x > 0`.
@isnad1 id=lt.4h3v.s6.ea1293f959f8 from=translated src=- shape=4bc91855 vocab=fe9d106e
-/
theorem one_lt_of_exp_le_pow
    (q : ℕ) (hq : 1 ≤ q) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hscale : Real.exp x ≤ y ^ q) :
    1 < y := by
  have honePow : 1 < y ^ q := (Real.one_lt_exp_iff.2 hx).trans_le hscale
  exact (one_lt_pow_iff_of_nonneg hy.le (by omega)).mp honePow

/-! ## The first transform branch (3.20) -/

/-- The finite intermediate correction in the first branch is controlled by
its value at `q/e`.  This is the polynomial calculation in (3.20).
@isnad1 id=le.5h4v.s7.fb2f6f58e3f2 from=translated src=- shape=c0e23a46 vocab=7601e0af
-/
theorem scaled_strongMomentIntermediateExponent_le_exp_linear
    (q : ℕ) (hq : 3 ≤ q) {V y x : ℝ}
    (hV : 0 ≤ V) (hy : 0 < y) (hx : 0 < x)
    (hscale : Real.exp x ≤ y ^ q) :
    (y / x) * strongMomentIntermediateExponent q V 1 (x / y) ≤
      Real.exp 1 * x / 3 *
        strongMomentIntermediateExponent q V 1
          ((q : ℝ) / Real.exp 1) := by
  let a : ℝ := x / y
  let b : ℝ := (q : ℝ) / Real.exp 1
  have ha : 0 < a := div_pos hx hy
  have hb : 0 < b := div_pos (by positivity) (Real.exp_pos 1)
  have hab : a ≤ b := by
    dsimp only [a, b]
    exact div_le_natCast_div_exp_one_of_exp_le_pow q (by omega) hy hscale
  have hnormalized := one_div_mul_strongMomentIntermediateExponent_le
    q hV (by norm_num : (0 : ℝ) ≤ 1) ha hb hab
  have hy1 : 1 ≤ y :=
    (one_lt_of_exp_le_pow q (by omega) hx hy hscale).le
  have hqReal : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hqSq : (9 : ℝ) ≤ (q : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((q : ℝ) - 3)]
  have hqSqY : (q : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 * y :=
    by simpa using
      (mul_le_mul_of_nonneg_left hy1 (sq_nonneg (q : ℝ)))
  have hcore : 3 * Real.exp 1 ≤ (q : ℝ) ^ 2 * y := by
    calc
      3 * Real.exp 1 ≤ 9 := by nlinarith [Real.exp_one_lt_three]
      _ ≤ (q : ℝ) ^ 2 := hqSq
      _ ≤ (q : ℝ) ^ 2 * y := hqSqY
  have hcoeff : a / b ^ 2 ≤ Real.exp 1 * x / 3 := by
    dsimp only [a, b]
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    have he0 : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
    have hy0 : y ≠ 0 := hy.ne'
    field_simp [hq0, he0, hy0]
    nlinarith
  have hmidNonneg : 0 ≤
      strongMomentIntermediateExponent q V 1 b :=
    strongMomentIntermediateExponent_nonneg q hV (by norm_num) hb.le
  have hleft : y / x = 1 / a := by
    dsimp only [a]
    field_simp [hx.ne', hy.ne']
  rw [hleft]
  exact hnormalized.trans
    (mul_le_mul_of_nonneg_right hcoeff hmidNonneg)

/-- Rio's first branch (3.20), after splitting off and optimizing the
Gaussian component.
@isnad1 id=le.5h4v.s7.98a9b523ac2e from=translated src=- shape=7986fc98 vocab=f156e7da
-/
theorem chernoffTransform_rioStrongMomentExponent_one_first_branch_le
    (q : ℕ) (hq : 3 ≤ q) {V y x : ℝ}
    (hV : 0 < V) (hy : 0 < y) (hx : 0 < x)
    (hscale : Real.exp x ≤ y ^ q) :
    chernoffTransform (rioStrongMomentExponent q V 1 y) x ≤
      Real.sqrt (2 * V * x) +
        (1 + 1 / (q : ℝ)) * y +
          Real.exp 1 * x / 3 *
            strongMomentIntermediateExponent q V 1
              ((q : ℝ) / Real.exp 1) := by
  have hbase := chernoffTransform_rioStrongMomentExponent_le
    q hq hV (by norm_num : (0 : ℝ) ≤ 1) hy hx (by simpa using hscale)
  have hcorrection := scaled_strongMomentIntermediateExponent_le_exp_linear
    q hq hV.le hy hx hscale
  calc
    chernoffTransform (rioStrongMomentExponent q V 1 y) x ≤
      Real.sqrt (2 * V * x) + y + y / (q : ℝ) +
        (y / x) * strongMomentIntermediateExponent q V 1 (x / y) := hbase
    _ ≤ Real.sqrt (2 * V * x) + y + y / (q : ℝ) +
        Real.exp 1 * x / 3 *
          strongMomentIntermediateExponent q V 1
            ((q : ℝ) / Real.exp 1) :=
      add_le_add le_rfl hcorrection
    _ = Real.sqrt (2 * V * x) +
        (1 + 1 / (q : ℝ)) * y +
          Real.exp 1 * x / 3 *
            strongMomentIntermediateExponent q V 1
              ((q : ℝ) / Real.exp 1) := by ring

/-- The two branches (3.20) and (3.21), combined exactly as in (3.22).
The finite series remains only inside the minimum appearing in (3.23).
@isnad1 id=le.5h4v.s8.39fcd17084be from=translated src=- shape=be1e1acd vocab=ca690f91
-/
theorem chernoffTransform_rioStrongMomentExponent_one_min_le
    (q : ℕ) (hq : 3 ≤ q) {V y x : ℝ}
    (hV : 0 < V) (hy : 0 < y) (hx : 0 < x)
    (hscale : Real.exp x ≤ y ^ q) :
    chernoffTransform (rioStrongMomentExponent q V 1 y) x ≤
      Real.sqrt (2 * V * x) +
        (1 + 1 / (q : ℝ)) * y +
          x / 3 *
            min
              (Real.exp 1 *
                strongMomentIntermediateExponent q V 1
                  ((q : ℝ) / Real.exp 1))
              (V ^ (-(1 / ((q : ℝ) - 2)))) := by
  have hfirst :=
    chernoffTransform_rioStrongMomentExponent_one_first_branch_le
      q hq hV hy hx hscale
  have hsecond :=
    chernoffTransform_rioStrongMomentExponent_one_second_branch_le
      q hq hV hy hx hscale
  by_cases hbranch :
      Real.exp 1 * strongMomentIntermediateExponent q V 1
          ((q : ℝ) / Real.exp 1) ≤
        V ^ (-(1 / ((q : ℝ) - 2)))
  · rw [min_eq_left hbranch]
    convert hfirst using 1
    ring
  · have hreverse : V ^ (-(1 / ((q : ℝ) - 2))) ≤
        Real.exp 1 * strongMomentIntermediateExponent q V 1
          ((q : ℝ) / Real.exp 1) := le_of_not_ge hbranch
    rw [min_eq_right hreverse]
    convert hsecond using 1
    ring

/-- Fully closed deterministic transform estimate in the normalization
`Q = 1`.  The explicit constant is exactly the one obtained by combining
(3.20)--(3.23):

`sqrt (2 V x) + (1 + 1/q) y + (e/3) x`.
@isnad1 id=le.5h4v.s7.7e63dd4826d9 from=translated src=- shape=3ffa8ba8 vocab=66f6377f
-/
theorem chernoffTransform_rioStrongMomentExponent_one_le
    (q : ℕ) (hq : 3 ≤ q) {V y x : ℝ}
    (hV : 0 < V) (hy : 0 < y) (hx : 0 < x)
    (hscale : Real.exp x ≤ y ^ q) :
    chernoffTransform (rioStrongMomentExponent q V 1 y) x ≤
      Real.sqrt (2 * V * x) +
        (1 + 1 / (q : ℝ)) * y + Real.exp 1 * x / 3 := by
  have hminimum := chernoffTransform_rioStrongMomentExponent_one_min_le
    q hq hV hy hx hscale
  have hlinear := rio_intermediate_min_linear_correction_le
    q hq hV hx.le
  exact hminimum.trans <| by
    gcongr

/-! ## Homogeneous endpoint -/

/-- The closed deterministic Rio transform at an arbitrary positive
aggregate `q`-th moment `Q`.  Homogeneity turns the normalized linear
correction into `(e/3) Q^(1/q) x`.

This is a deterministic Chernoff statement; obtaining a maximal-process
inequality additionally requires a probabilistic MGF/comparison theorem.
@isnad1 id=le.6h5v.s7.b7afcc9dccfd from=translated src=- shape=922b3cc5 vocab=40a25240
-/
theorem chernoffTransform_rioStrongMomentExponent_le_explicit
    (q : ℕ) (hq : 3 ≤ q) {V Q y x : ℝ}
    (hV : 0 < V) (hQ : 0 < Q) (hy : 0 < y) (hx : 0 < x)
    (hscale : Q * Real.exp x ≤ y ^ q) :
    chernoffTransform (rioStrongMomentExponent q V Q y) x ≤
      Real.sqrt (2 * V * x) +
        (1 + 1 / (q : ℝ)) * y +
          Real.exp 1 * strongMomentQScale q Q * x / 3 := by
  let a : ℝ := strongMomentQScale q Q
  let V₀ : ℝ := V / a ^ 2
  let y₀ : ℝ := y / a
  let psi₀ : ℝ → ℝ := rioStrongMomentExponent q V₀ 1 y₀
  have ha : 0 < a := strongMomentQScale_pos hQ
  have hV₀ : 0 < V₀ := div_pos hV (sq_pos_of_pos ha)
  have hy₀ : 0 < y₀ := div_pos hy ha
  have haPow : a ^ q = Q := strongMomentQScale_pow (by omega) hQ
  have hy₀Pow : y₀ ^ q = y ^ q / Q := by
    dsimp only [y₀]
    rw [div_pow, haPow]
  have hscale₀ : Real.exp x ≤ y₀ ^ q := by
    rw [hy₀Pow]
    exact (le_div_iff₀ hQ).2 (by simpa [mul_comm] using hscale)
  have hpsi₀ : ∀ t : ℝ, 0 < t → 0 ≤ psi₀ t := by
    intro t ht
    exact rioStrongMomentExponent_nonneg q hV₀.le
      (by norm_num) hy₀ ht.le
  have hexponent : rioStrongMomentExponent q V Q y =
      fun t => psi₀ (a * t) := by
    funext t
    dsimp only [psi₀, V₀, y₀]
    exact rioStrongMomentExponent_eq_scaled_one q hq hV hQ hy
  have hrescale :
      chernoffTransform (rioStrongMomentExponent q V Q y) x ≤
        a * chernoffTransform psi₀ x := by
    rw [hexponent]
    exact chernoffTransform_comp_mul_le_mul ha hx.le hpsi₀
  have hnormalized : chernoffTransform psi₀ x ≤
      Real.sqrt (2 * V₀ * x) +
        (1 + 1 / (q : ℝ)) * y₀ + Real.exp 1 * x / 3 := by
    dsimp only [psi₀]
    exact chernoffTransform_rioStrongMomentExponent_one_le
      q hq hV₀ hy₀ hx hscale₀
  have hsqrt₀Sq : (Real.sqrt (2 * V₀ * x)) ^ 2 =
      2 * V₀ * x := Real.sq_sqrt (by positivity)
  have hsqrtSq : (Real.sqrt (2 * V * x)) ^ 2 =
      2 * V * x := Real.sq_sqrt (by positivity)
  have hsqrtScale :
      a * Real.sqrt (2 * V₀ * x) = Real.sqrt (2 * V * x) := by
    have hsq : (a * Real.sqrt (2 * V₀ * x)) ^ 2 =
        (Real.sqrt (2 * V * x)) ^ 2 := by
      rw [mul_pow, hsqrt₀Sq, hsqrtSq]
      dsimp only [V₀]
      field_simp [ha.ne']
    have hleft : 0 ≤ a * Real.sqrt (2 * V₀ * x) := by positivity
    have hright : 0 ≤ Real.sqrt (2 * V * x) := Real.sqrt_nonneg _
    nlinarith
  have haMulY₀ : a * y₀ = y := by
    dsimp only [y₀]
    field_simp [ha.ne']
  calc
    chernoffTransform (rioStrongMomentExponent q V Q y) x ≤
        a * chernoffTransform psi₀ x := hrescale
    _ ≤ a * (Real.sqrt (2 * V₀ * x) +
          (1 + 1 / (q : ℝ)) * y₀ + Real.exp 1 * x / 3) :=
      mul_le_mul_of_nonneg_left hnormalized ha.le
    _ = Real.sqrt (2 * V * x) +
        (1 + 1 / (q : ℝ)) * y +
          Real.exp 1 * strongMomentQScale q Q * x / 3 := by
      calc
        a * (Real.sqrt (2 * V₀ * x) +
            (1 + 1 / (q : ℝ)) * y₀ + Real.exp 1 * x / 3) =
          a * Real.sqrt (2 * V₀ * x) +
            (1 + 1 / (q : ℝ)) * (a * y₀) +
              Real.exp 1 * a * x / 3 := by ring
        _ = Real.sqrt (2 * V * x) +
            (1 + 1 / (q : ℝ)) * y +
              Real.exp 1 * strongMomentQScale q Q * x / 3 := by
          rw [hsqrtScale, haMulY₀]

end ProbabilityTheory

/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentSeriesMGF
import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentTailTransform
import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentInterpolation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Deterministic Chernoff calculus for strong moments

This file collects the convex exponents used to optimize the exact-series
MGF bound.  It is deliberately independent of filtrations: the martingale
layer only has to furnish an MGF certificate with one of these exponents.
-/

open Real Set Finset
open scoped BigOperators

noncomputable section

namespace ProbabilityTheory

/-- Quadratic (Gaussian) component of a strong-moment exponent.-/
def gaussianChernoffExponent (V t : ℝ) : ℝ :=
  (V / 2) * t ^ 2

@[simp] theorem gaussianChernoffExponent_zero (V : ℝ) :
    gaussianChernoffExponent V 0 = 0 := by
  simp [gaussianChernoffExponent]

theorem gaussianChernoffExponent_nonneg {V t : ℝ}
    (hV : 0 ≤ V) :
    0 ≤ gaussianChernoffExponent V t := by
  unfold gaussianChernoffExponent
  positivity

theorem convexOn_gaussianChernoffExponent {V : ℝ} (hV : 0 ≤ V) :
    ConvexOn ℝ (Set.Ici 0) (gaussianChernoffExponent V) := by
  have hcoef : 0 ≤ V / 2 := by positivity
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hp := (convexOn_pow (𝕜 := ℝ) 2).2 hx hy ha hb hab
  simp only [smul_eq_mul] at hp ⊢
  unfold gaussianChernoffExponent
  calc
    V / 2 * (a * x + b * y) ^ 2 ≤
        V / 2 * (a * x ^ 2 + b * y ^ 2) :=
      mul_le_mul_of_nonneg_left hp hcoef
    _ = a * (V / 2 * x ^ 2) + b * (V / 2 * y ^ 2) := by ring

/-- Exact optimization of the quadratic Chernoff component.-/
theorem chernoffTransform_gaussianChernoffExponent_le
    {V x : ℝ} (hV : 0 < V) (hx : 0 < x) :
    chernoffTransform (gaussianChernoffExponent V) x ≤
      Real.sqrt (2 * V * x) := by
  let t : ℝ := Real.sqrt (2 * x / V)
  have harg : 0 < 2 * x / V := div_pos (by positivity) hV
  have ht : 0 < t := Real.sqrt_pos.2 harg
  have htSq : t ^ 2 = 2 * x / V := by
    dsimp only [t]
    exact Real.sq_sqrt harg.le
  have hnonneg : ∀ s : ℝ, 0 < s →
      0 ≤ gaussianChernoffExponent V s := by
    intro s _hs
    exact gaussianChernoffExponent_nonneg hV.le
  have hb := bddBelow_range_chernoffObjective hx.le hnonneg
  have heval := chernoffTransform_le_objective
    (psi := gaussianChernoffExponent V) (x := x) ht hb
  have hsqrtSq : (Real.sqrt (2 * V * x)) ^ 2 = 2 * V * x := by
    exact Real.sq_sqrt (by positivity)
  have hobjective :
      (gaussianChernoffExponent V t + x) / t =
        Real.sqrt (2 * V * x) := by
    unfold gaussianChernoffExponent
    have hrootProduct : t * Real.sqrt (2 * V * x) = 2 * x := by
      have hsq : (t * Real.sqrt (2 * V * x)) ^ 2 = (2 * x) ^ 2 := by
        rw [mul_pow, htSq, hsqrtSq]
        field_simp [hV.ne']
      have hprodNonneg : 0 ≤ t * Real.sqrt (2 * V * x) := by positivity
      have htwoXNonneg : 0 ≤ 2 * x := by positivity
      nlinarith
    apply (div_eq_iff ht.ne').2
    rw [htSq]
    have hnum : V / 2 * (2 * x / V) + x = 2 * x := by
      field_simp [hV.ne']
      ring
    rw [hnum]
    simpa only [mul_comm] using hrootProduct.symm
  rw [hobjective] at heval
  exact heval

/-- The exact tail component is convex on nonnegative Laplace parameters.-/
theorem convexOn_exactStrongMomentTailExponent
    (q : ℕ) {Q y : ℝ} (hQ : 0 ≤ Q) (hy : 0 < y) :
    ConvexOn ℝ (Set.Ici 0) (exactStrongMomentTailExponent q Q y) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro s hs t ht a b ha hb hab
  have htail := (convexOn_expSeriesTail q).2
    (mul_nonneg hs hy.le) (mul_nonneg ht hy.le) ha hb hab
  have hcoef : 0 ≤ Q / y ^ q :=
    div_nonneg hQ (pow_nonneg hy.le q)
  unfold exactStrongMomentTailExponent
  simp only [smul_eq_mul] at htail ⊢
  have harg : (a * s + b * t) * y = a * (s * y) + b * (t * y) := by ring
  rw [harg]
  calc
    (Q / y ^ q) * expSeriesTail q (a * (s * y) + b * (t * y)) ≤
        (Q / y ^ q) *
          (a * expSeriesTail q (s * y) +
            b * expSeriesTail q (t * y)) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [smul_eq_mul] using htail) hcoef
    _ = a * ((Q / y ^ q) * expSeriesTail q (s * y)) +
        b * ((Q / y ^ q) * expSeriesTail q (t * y)) := by ring

/-- Interpolated coefficient between the aggregate moments of orders two
and `q`.-/
def interpolatedStrongMomentCoefficient
    (q : ℕ) (V Q : ℝ) (k : ℕ) : ℝ :=
  V ^ strongMomentSecondWeight q k *
    Q ^ strongMomentQWeight q k

/-- Finite contribution of the moment orders strictly between two and
`q`.-/
def strongMomentIntermediateExponent
    (q : ℕ) (V Q t : ℝ) : ℝ :=
  ∑ k ∈ Ico 3 q,
    t ^ k / (k.factorial : ℝ) *
      interpolatedStrongMomentCoefficient q V Q k

theorem interpolatedStrongMomentCoefficient_nonneg
    (q k : ℕ) {V Q : ℝ} (hV : 0 ≤ V) (hQ : 0 ≤ Q) :
    0 ≤ interpolatedStrongMomentCoefficient q V Q k := by
  unfold interpolatedStrongMomentCoefficient
  exact mul_nonneg (Real.rpow_nonneg hV _) (Real.rpow_nonneg hQ _)

theorem strongMomentIntermediateExponent_nonneg
    (q : ℕ) {V Q t : ℝ} (hV : 0 ≤ V) (hQ : 0 ≤ Q)
    (ht : 0 ≤ t) :
    0 ≤ strongMomentIntermediateExponent q V Q t := by
  unfold strongMomentIntermediateExponent
  exact sum_nonneg fun k _hk => mul_nonneg
    (div_nonneg (pow_nonneg ht k) (by positivity))
    (interpolatedStrongMomentCoefficient_nonneg q k hV hQ)

@[simp] theorem strongMomentIntermediateExponent_zero
    (q : ℕ) (V Q : ℝ) :
    strongMomentIntermediateExponent q V Q 0 = 0 := by
  unfold strongMomentIntermediateExponent
  apply sum_eq_zero
  intro k hk
  have hk0 : k ≠ 0 := by
    have hk3 := (mem_Ico.mp hk).1
    omega
  simp [hk0]

theorem convexOn_strongMomentIntermediateExponent
    (q : ℕ) {V Q : ℝ} (hV : 0 ≤ V) (hQ : 0 ≤ Q) :
    ConvexOn ℝ (Set.Ici 0) (strongMomentIntermediateExponent q V Q) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro s hs t ht a b ha hb hab
  simp only [smul_eq_mul] at ⊢
  unfold strongMomentIntermediateExponent
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply sum_le_sum
  intro k hk
  have hp := (convexOn_pow (𝕜 := ℝ) k).2 hs ht ha hb hab
  simp only [smul_eq_mul] at hp
  have hfac : 0 ≤ ((k.factorial : ℕ) : ℝ) := by positivity
  have hc := interpolatedStrongMomentCoefficient_nonneg q k hV hQ
  calc
    (a * s + b * t) ^ k / (k.factorial : ℝ) *
        interpolatedStrongMomentCoefficient q V Q k ≤
      (a * s ^ k + b * t ^ k) / (k.factorial : ℝ) *
        interpolatedStrongMomentCoefficient q V Q k :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hp hfac) hc
    _ = a * (s ^ k / (k.factorial : ℝ) *
          interpolatedStrongMomentCoefficient q V Q k) +
        b * (t ^ k / (k.factorial : ℝ) *
          interpolatedStrongMomentCoefficient q V Q k) := by ring

/-- The exact-series exponent with every intermediate moment replaced by
its Hölder interpolation proxy.-/
def rioStrongMomentExponent
    (q : ℕ) (V Q y t : ℝ) : ℝ :=
  gaussianChernoffExponent V t +
    strongMomentIntermediateExponent q V Q t +
    exactStrongMomentTailExponent q Q y t

@[simp] theorem rioStrongMomentExponent_zero
    {q : ℕ} (hq : q ≠ 0) (V Q y : ℝ) :
    rioStrongMomentExponent q V Q y 0 = 0 := by
  simp [rioStrongMomentExponent, hq]

theorem rioStrongMomentExponent_nonneg
    (q : ℕ) {V Q y t : ℝ}
    (hV : 0 ≤ V) (hQ : 0 ≤ Q) (hy : 0 < y) (ht : 0 ≤ t) :
    0 ≤ rioStrongMomentExponent q V Q y t := by
  unfold rioStrongMomentExponent
  exact add_nonneg
    (add_nonneg (gaussianChernoffExponent_nonneg hV)
      (strongMomentIntermediateExponent_nonneg q hV hQ ht))
    (exactStrongMomentTailExponent_nonneg q hQ hy ht)

theorem convexOn_rioStrongMomentExponent
    (q : ℕ) {V Q y : ℝ}
    (hV : 0 ≤ V) (hQ : 0 ≤ Q) (hy : 0 < y) :
    ConvexOn ℝ (Set.Ici 0) (rioStrongMomentExponent q V Q y) := by
  have hgauss := convexOn_gaussianChernoffExponent hV
  have hmid := convexOn_strongMomentIntermediateExponent q hV hQ
  have htail := convexOn_exactStrongMomentTailExponent q hQ hy
  refine ⟨convex_Ici 0, ?_⟩
  intro s hs t ht a b ha hb hab
  have hg := hgauss.2 hs ht ha hb hab
  have hm := hmid.2 hs ht ha hb hab
  have htl := htail.2 hs ht ha hb hab
  simp only [smul_eq_mul] at hg hm htl ⊢
  unfold rioStrongMomentExponent
  calc
    gaussianChernoffExponent V (a * s + b * t) +
          strongMomentIntermediateExponent q V Q (a * s + b * t) +
          exactStrongMomentTailExponent q Q y (a * s + b * t) ≤
        (a * gaussianChernoffExponent V s +
            b * gaussianChernoffExponent V t) +
          (a * strongMomentIntermediateExponent q V Q s +
            b * strongMomentIntermediateExponent q V Q t) +
          (a * exactStrongMomentTailExponent q Q y s +
            b * exactStrongMomentTailExponent q Q y t) :=
      add_le_add (add_le_add hg hm) htl
    _ = a * (gaussianChernoffExponent V s +
          strongMomentIntermediateExponent q V Q s +
          exactStrongMomentTailExponent q Q y s) +
        b * (gaussianChernoffExponent V t +
          strongMomentIntermediateExponent q V Q t +
          exactStrongMomentTailExponent q Q y t) := by ring

/-- Hölder interpolation upgrades an exact-series exponent with raw moment
proxies to Rio's deterministic exponent.-/
theorem strongMomentSeriesExponent_le_rioStrongMomentExponent
    (q : ℕ) {t y second V Q : ℝ} {moment : ℕ → ℝ}
    (ht : 0 ≤ t) (hy : 0 < y)
    (hsecond : second ≤ V)
    (hmiddle : ∀ k ∈ Finset.Ico 3 q,
      moment k ≤ interpolatedStrongMomentCoefficient q V Q k)
    (hmomentQ : moment q ≤ Q) :
    strongMomentSeriesExponent q t y second moment ≤
      rioStrongMomentExponent q V Q y t := by
  have hgauss :
      (1 / 2 : ℝ) * t ^ 2 * second ≤ gaussianChernoffExponent V t := by
    unfold gaussianChernoffExponent
    have hcoef : 0 ≤ (1 / 2 : ℝ) * t ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsecond hcoef]
  have hmiddleSum :
      (∑ k ∈ Ico 3 q,
        t ^ k / (k.factorial : ℝ) * moment k) ≤
        strongMomentIntermediateExponent q V Q t := by
    unfold strongMomentIntermediateExponent
    exact sum_le_sum fun k hk =>
      mul_le_mul_of_nonneg_left (hmiddle k hk)
        (div_nonneg (pow_nonneg ht k) (by positivity))
  have htailCoef : 0 ≤ expSeriesTail q (t * y) / y ^ q := by
    exact div_nonneg (expSeriesTail_nonneg (mul_nonneg ht hy.le) q)
      (pow_nonneg hy.le q)
  have htail :
      expSeriesTail q (t * y) / y ^ q * moment q ≤
        exactStrongMomentTailExponent q Q y t := by
    unfold exactStrongMomentTailExponent
    calc
      expSeriesTail q (t * y) / y ^ q * moment q ≤
          expSeriesTail q (t * y) / y ^ q * Q :=
        mul_le_mul_of_nonneg_left hmomentQ htailCoef
      _ = Q / y ^ q * expSeriesTail q (t * y) := by ring
  unfold strongMomentSeriesExponent rioStrongMomentExponent
  exact add_le_add (add_le_add hgauss hmiddleSum) htail

/-- Evaluation of the combined intermediate and exact-tail components at
`x / y`.  This is the formal version of Rio's inequality (3.20) before the
last bound on the finite intermediate series.-/
theorem chernoffTransform_intermediate_add_tail_le
    (q : ℕ) (hq : 1 ≤ q) {V Q y x : ℝ}
    (hV : 0 ≤ V) (hQ : 0 ≤ Q) (hy : 0 < y) (hx : 0 < x)
    (hscale : Q * Real.exp x ≤ y ^ q) :
    chernoffTransform
        (fun t => strongMomentIntermediateExponent q V Q t +
          exactStrongMomentTailExponent q Q y t) x ≤
      y + y / (q : ℝ) +
        (y / x) * strongMomentIntermediateExponent q V Q (x / y) := by
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  have hyq : 0 < y ^ q := pow_pos hy q
  have hcoef : 0 ≤ Q / y ^ q := div_nonneg hQ hyq.le
  have hcoefExp : (Q / y ^ q) * Real.exp x ≤ 1 := by
    calc
      (Q / y ^ q) * Real.exp x = (Q * Real.exp x) / y ^ q := by ring
      _ ≤ 1 := (div_le_one hyq).2 hscale
  have htail := expSeriesTail_le_div_mul_exp q hq x hx.le
  have hscaledTail :
      (Q / y ^ q) * expSeriesTail q x ≤ x / (q : ℝ) := by
    calc
      (Q / y ^ q) * expSeriesTail q x ≤
          (Q / y ^ q) * ((x / (q : ℝ)) * Real.exp x) :=
        mul_le_mul_of_nonneg_left htail hcoef
      _ = (x / (q : ℝ)) *
          ((Q / y ^ q) * Real.exp x) := by ring
      _ ≤ (x / (q : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hcoefExp (div_nonneg hx.le (by positivity))
      _ = x / (q : ℝ) := by ring
  have hnonneg : ∀ t : ℝ, 0 < t →
      0 ≤ strongMomentIntermediateExponent q V Q t +
        exactStrongMomentTailExponent q Q y t := by
    intro t ht
    exact add_nonneg
      (strongMomentIntermediateExponent_nonneg q hV hQ ht.le)
      (exactStrongMomentTailExponent_nonneg q hQ hy ht.le)
  have hb := bddBelow_range_chernoffObjective hx.le hnonneg
  have heval := chernoffTransform_le_objective
    (psi := fun t => strongMomentIntermediateExponent q V Q t +
      exactStrongMomentTailExponent q Q y t)
    (x := x) (t := x / y) (div_pos hx hy) hb
  have harg : (x / y) * y = x := by field_simp
  unfold exactStrongMomentTailExponent at heval
  rw [harg] at heval
  calc
    chernoffTransform
        (fun t => strongMomentIntermediateExponent q V Q t +
          exactStrongMomentTailExponent q Q y t) x ≤
      (strongMomentIntermediateExponent q V Q (x / y) +
          (Q / y ^ q) * expSeriesTail q x + x) / (x / y) := heval
    _ ≤ (strongMomentIntermediateExponent q V Q (x / y) +
          x / (q : ℝ) + x) / (x / y) := by
      exact div_le_div_of_nonneg_right
        (add_le_add
          (add_le_add le_rfl hscaledTail) le_rfl)
        (div_pos hx hy).le
    _ = y + y / (q : ℝ) +
        (y / x) * strongMomentIntermediateExponent q V Q (x / y) := by
      field_simp [hx.ne', hy.ne', hq0]
      ring

/-- Three-way Chernoff decomposition: exact Gaussian optimization plus an
explicit evaluation of the intermediate and heavy-tail components.-/
theorem chernoffTransform_rioStrongMomentExponent_le
    (q : ℕ) (hq : 3 ≤ q) {V Q y x : ℝ}
    (hV : 0 < V) (hQ : 0 ≤ Q) (hy : 0 < y) (hx : 0 < x)
    (hscale : Q * Real.exp x ≤ y ^ q) :
    chernoffTransform (rioStrongMomentExponent q V Q y) x ≤
      Real.sqrt (2 * V * x) +
        y + y / (q : ℝ) +
          (y / x) * strongMomentIntermediateExponent q V Q (x / y) := by
  let middleTail : ℝ → ℝ := fun t =>
    strongMomentIntermediateExponent q V Q t +
      exactStrongMomentTailExponent q Q y t
  have hmidConv := convexOn_strongMomentIntermediateExponent q hV.le hQ
  have htailConv := convexOn_exactStrongMomentTailExponent q hQ hy
  have hmiddleTailConv : ConvexOn ℝ (Set.Ici 0) middleTail := by
    refine ⟨convex_Ici 0, ?_⟩
    intro s hs t ht a b ha hb hab
    have hm := hmidConv.2 hs ht ha hb hab
    have htl := htailConv.2 hs ht ha hb hab
    simp only [middleTail, smul_eq_mul] at hm htl ⊢
    calc
      strongMomentIntermediateExponent q V Q (a * s + b * t) +
          exactStrongMomentTailExponent q Q y (a * s + b * t) ≤
        (a * strongMomentIntermediateExponent q V Q s +
          b * strongMomentIntermediateExponent q V Q t) +
        (a * exactStrongMomentTailExponent q Q y s +
          b * exactStrongMomentTailExponent q Q y t) := add_le_add hm htl
      _ = a * (strongMomentIntermediateExponent q V Q s +
            exactStrongMomentTailExponent q Q y s) +
          b * (strongMomentIntermediateExponent q V Q t +
            exactStrongMomentTailExponent q Q y t) := by ring
  have hmiddleTailZero : middleTail 0 = 0 := by
    dsimp only [middleTail]
    rw [strongMomentIntermediateExponent_zero,
      exactStrongMomentTailExponent_zero (q := q) (by omega)]
    exact add_zero 0
  have hmiddleTailNonneg : ∀ t : ℝ, 0 < t → 0 ≤ middleTail t := by
    intro t ht
    exact add_nonneg
      (strongMomentIntermediateExponent_nonneg q hV.le hQ ht.le)
      (exactStrongMomentTailExponent_nonneg q hQ hy ht.le)
  have hsplit := chernoffTransform_add_le hx.le
    (convexOn_gaussianChernoffExponent hV.le) hmiddleTailConv
    (gaussianChernoffExponent_zero V) hmiddleTailZero
    (fun t _ht => gaussianChernoffExponent_nonneg hV.le)
    hmiddleTailNonneg
  have hgauss := chernoffTransform_gaussianChernoffExponent_le hV hx
  have htail := chernoffTransform_intermediate_add_tail_le q (by omega)
    hV.le hQ hy hx hscale
  have htotal : chernoffTransform
      (fun t => gaussianChernoffExponent V t + middleTail t) x ≤
      Real.sqrt (2 * V * x) + y + y / (q : ℝ) +
        (y / x) * strongMomentIntermediateExponent q V Q (x / y) :=
    hsplit.trans <| by
    calc
      chernoffTransform (gaussianChernoffExponent V) x +
          chernoffTransform middleTail x ≤
        Real.sqrt (2 * V * x) +
          (y + y / (q : ℝ) +
            (y / x) * strongMomentIntermediateExponent q V Q (x / y)) :=
        add_le_add hgauss (by simpa only [middleTail] using htail)
      _ = Real.sqrt (2 * V * x) + y + y / (q : ℝ) +
          (y / x) * strongMomentIntermediateExponent q V Q (x / y) := by ring
  have hexponent : rioStrongMomentExponent q V Q y =
      fun t => gaussianChernoffExponent V t + middleTail t := by
    funext t
    unfold rioStrongMomentExponent
    dsimp only [middleTail]
    ring
  rw [hexponent]
  exact htotal

end ProbabilityTheory

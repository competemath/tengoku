/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Seed.Analysis.Convex.SpecificFunctions.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Chernoff transform of a convex exponent

For a nonnegative convex function `psi` on the nonnegative half-line with
`psi 0 = 0`, define

`T psi x = inf { (psi t + x) / t : 0 < t }`.

This is the inverse-Legendre-transform quantity used in the integrated-
quantile proof of the martingale Fuk--Nagaev inequality.  The main result is
Rio's elementary subadditivity property

`T (psi₀ + psi₁) x ≤ T psi₀ x + T psi₁ x`.

The proof is constructive at the level of two positive Laplace parameters:
given `t,s > 0`, use their harmonic combination `z = s*t/(s+t)` and convexity
at the origin.
-/

open Real Set

noncomputable section

namespace ProbabilityTheory

/-- A strictly positive real parameter, used as the domain of the Chernoff
objective.-/
abbrev PositiveLaplaceParameter := {t : ℝ // 0 < t}

/-- The Chernoff objective at a positive Laplace parameter.-/
def chernoffObjective (psi : ℝ → ℝ) (x : ℝ)
    (t : PositiveLaplaceParameter) : ℝ :=
  (psi t + x) / t

/-- Infimum of the Chernoff objective over positive Laplace parameters.-/
def chernoffTransform (psi : ℝ → ℝ) (x : ℝ) : ℝ :=
  sInf (Set.range (chernoffObjective psi x))

/-- Under nonnegativity of the exponent and of `x`, every Chernoff objective
is nonnegative.
@isnad1 id=le.2h3v.s5.7fe5fdc51329 from=translated src=- shape=00cc8a1e vocab=ad76efba
-/
theorem chernoffObjective_nonneg
    {psi : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x)
    (hpsi : ∀ t, 0 < t → 0 ≤ psi t)
    (t : PositiveLaplaceParameter) :
    0 ≤ chernoffObjective psi x t := by
  exact div_nonneg (add_nonneg (hpsi t t.property) hx) t.property.le

/-- The range of a nonnegative Chernoff objective is bounded below.
@isnad1 id=bddbelow.2h2v.s5.60cc31cb313f from=translated src=- shape=8dfb5880 vocab=e4c79d75
-/
theorem bddBelow_range_chernoffObjective
    {psi : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x)
    (hpsi : ∀ t, 0 < t → 0 ≤ psi t) :
    BddBelow (Set.range (chernoffObjective psi x)) := by
  refine ⟨0, ?_⟩
  intro y hy
  obtain ⟨t, rfl⟩ := hy
  exact chernoffObjective_nonneg hx hpsi t

/-- Evaluation at any positive parameter gives an upper bound on the
Chernoff transform.
@isnad1 id=le.2h3v.s5.4ebb1b000d4f from=translated src=- shape=b14c887f vocab=0fa70656
-/
theorem chernoffTransform_le_objective
    {psi : ℝ → ℝ} {x t : ℝ} (ht : 0 < t)
    (hbounded : BddBelow (Set.range (chernoffObjective psi x))) :
    chernoffTransform psi x ≤ (psi t + x) / t := by
  unfold chernoffTransform
  exact csInf_le hbounded ⟨⟨t, ht⟩, rfl⟩

/-- Convexity at the origin contracts a convex exponent under multiplication
by a coefficient in `[0,1]`.
@isnad1 id=le.5h3v.s6.75d2e42f3022 from=translated src=- shape=98543222 vocab=959ff45d
-/
theorem convexOn_Ici_mul_le_mul
    {psi : ℝ → ℝ} (hconv : ConvexOn ℝ (Set.Ici 0) psi)
    (hzero : psi 0 = 0) {a t : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht : 0 ≤ t) :
    psi (a * t) ≤ a * psi t := by
  have hweight : a + (1 - a) = 1 := by ring
  have htmem : t ∈ Set.Ici (0 : ℝ) := ht
  have h0mem : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := by simp
  have hbase := hconv.2 htmem h0mem ha0 (sub_nonneg.mpr ha1) hweight
  simpa only [smul_eq_mul, mul_zero, add_zero, hzero] using hbase

/-- Two positive Chernoff objectives dominate the objective of the sum at
the harmonic combination of their parameters.  This is inequality (2.5) in
Rio's proof.
@isnad1 id=le.6h5v.s8.4f5f162f2ff8 from=translated src=- shape=7d666b6a vocab=1e16039e
-/
theorem chernoffObjective_add_harmonic_le
    {psi0 psi1 : ℝ → ℝ} {x s t : ℝ}
    (hconv0 : ConvexOn ℝ (Set.Ici 0) psi0)
    (hconv1 : ConvexOn ℝ (Set.Ici 0) psi1)
    (hzero0 : psi0 0 = 0) (hzero1 : psi1 0 = 0)
    (hs : 0 < s) (ht : 0 < t) :
    ((psi0 (s * t / (s + t)) + psi1 (s * t / (s + t))) + x) /
        (s * t / (s + t)) ≤
      (psi0 t + x) / t + (psi1 s + x) / s := by
  have hst : 0 < s + t := add_pos hs ht
  have hsweight0 : 0 ≤ s / (s + t) := (div_pos hs hst).le
  have hsweight1 : s / (s + t) ≤ 1 := by
    exact (div_le_one hst).2 (le_add_of_nonneg_right ht.le)
  have htweight0 : 0 ≤ t / (s + t) := (div_pos ht hst).le
  have htweight1 : t / (s + t) ≤ 1 := by
    exact (div_le_one hst).2 (le_add_of_nonneg_left hs.le)
  have hpsi0 : psi0 (s * t / (s + t)) ≤
      (s / (s + t)) * psi0 t := by
    have h := convexOn_Ici_mul_le_mul hconv0 hzero0
      hsweight0 hsweight1 ht.le
    have heq : (s / (s + t)) * t = s * t / (s + t) := by ring
    rw [← heq]
    exact h
  have hpsi1 : psi1 (s * t / (s + t)) ≤
      (t / (s + t)) * psi1 s := by
    have h := convexOn_Ici_mul_le_mul hconv1 hzero1
      htweight0 htweight1 hs.le
    have heq : (t / (s + t)) * s = s * t / (s + t) := by ring
    rw [← heq]
    exact h
  have hz : 0 < s * t / (s + t) := div_pos (mul_pos hs ht) hst
  apply (div_le_iff₀ hz).2
  have hstne : s + t ≠ 0 := hst.ne'
  have hsne : s ≠ 0 := hs.ne'
  have htne : t ≠ 0 := ht.ne'
  calc
    psi0 (s * t / (s + t)) + psi1 (s * t / (s + t)) + x
        ≤ (s / (s + t)) * psi0 t +
            (t / (s + t)) * psi1 s + x := by linarith
    _ = ((psi0 t + x) / t + (psi1 s + x) / s) *
          (s * t / (s + t)) := by
      field_simp [hstne, hsne, htne]
      ring

/-- The Chernoff transform is subadditive on nonnegative convex exponents
vanishing at the origin.
@isnad1 id=le.7h3v.s7.663c92dd7e86 from=translated src=- shape=82662448 vocab=aedbd37a
-/
theorem chernoffTransform_add_le
    {psi0 psi1 : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x)
    (hconv0 : ConvexOn ℝ (Set.Ici 0) psi0)
    (hconv1 : ConvexOn ℝ (Set.Ici 0) psi1)
    (hzero0 : psi0 0 = 0) (hzero1 : psi1 0 = 0)
    (hnonneg0 : ∀ t, 0 < t → 0 ≤ psi0 t)
    (hnonneg1 : ∀ t, 0 < t → 0 ≤ psi1 t) :
    chernoffTransform (fun t => psi0 t + psi1 t) x ≤
      chernoffTransform psi0 x + chernoffTransform psi1 x := by
  let f0 : PositiveLaplaceParameter → ℝ := chernoffObjective psi0 x
  let f1 : PositiveLaplaceParameter → ℝ := chernoffObjective psi1 x
  let fsum : PositiveLaplaceParameter → ℝ :=
    chernoffObjective (fun t => psi0 t + psi1 t) x
  have hb0 : BddBelow (Set.range f0) := by
    simpa only [f0] using bddBelow_range_chernoffObjective hx hnonneg0
  have hb1 : BddBelow (Set.range f1) := by
    simpa only [f1] using bddBelow_range_chernoffObjective hx hnonneg1
  have hnonnegSum : ∀ t, 0 < t → 0 ≤ psi0 t + psi1 t := by
    intro t ht
    exact add_nonneg (hnonneg0 t ht) (hnonneg1 t ht)
  have hbsum : BddBelow (Set.range fsum) := by
    simpa only [fsum] using
      bddBelow_range_chernoffObjective hx hnonnegSum
  refine le_of_forall_pos_le_add fun epsilon hepsilon => ?_
  obtain ⟨a0, ⟨t, ht⟩, ha0⟩ :=
    Real.lt_sInf_add_pos (Set.range_nonempty f0) (half_pos hepsilon)
  obtain ⟨a1, ⟨s, hs⟩, ha1⟩ :=
    Real.lt_sInf_add_pos (Set.range_nonempty f1) (half_pos hepsilon)
  subst a0
  subst a1
  let z : PositiveLaplaceParameter :=
    ⟨s * t / (s + t), div_pos (mul_pos s.property t.property)
      (add_pos s.property t.property)⟩
  have hsumAtZ : sInf (Set.range fsum) ≤ fsum z :=
    csInf_le hbsum ⟨z, rfl⟩
  have hharmonic : fsum z ≤ f0 t + f1 s := by
    dsimp only [fsum, f0, f1, chernoffObjective, z]
    exact chernoffObjective_add_harmonic_le hconv0 hconv1
      hzero0 hzero1 s.property t.property
  change sInf (Set.range fsum) ≤
    sInf (Set.range f0) + sInf (Set.range f1) + epsilon
  calc
    sInf (Set.range fsum) ≤ fsum z := hsumAtZ
    _ ≤ f0 t + f1 s := hharmonic
    _ ≤ (sInf (Set.range f0) + epsilon / 2) +
        (sInf (Set.range f1) + epsilon / 2) := (add_lt_add ha0 ha1).le
    _ = sInf (Set.range f0) + sInf (Set.range f1) + epsilon := by ring

end ProbabilityTheory

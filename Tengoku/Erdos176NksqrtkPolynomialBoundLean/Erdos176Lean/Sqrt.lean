import Tengoku.Erdos176NksqrtkPolynomialBoundLean.Erdos176Lean.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/KitaKen1/erdos176-nksqrtk-polynomial-bound-lean@19b2ad31c812, `Erdos176Lean/Sqrt.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/


/-!
# Erdős problem 176: the `sqrt(k)` target

This file starts the Lean formalization of the Fejér-weighted proof outline for
the bound

`N(k, sqrt(k)) = O(k^5)`.

The public-facing mathematical target is that an ordinary `k`-term AP has
absolute sum at least `sqrt(k)`.  Since AP sums are integers, the Lean
formalization uses the equivalent squared form

`(k : ℤ) ≤ S ^ 2`.

This keeps the statement close to the human proof while avoiding unnecessary
real square-root infrastructure.
-/

namespace Erdos176Lean

open scoped BigOperators

section FejerWeights

/-- The Fejér weight used for differences `1 ≤ d ≤ D`.-/
noncomputable def fejerWeight (D d : ℕ) : ℝ :=
  1 - (d : ℝ) / (D + 1 : ℝ)

/--
@isnad1 id=le.1h2v.s4.e9007da08ced from=translated src=- shape=7c81aa35 vocab=61884333
-/
theorem fejerWeight_nonneg {D d : ℕ} (hd : d ≤ D) :
    0 ≤ fejerWeight D d := by
  unfold fejerWeight
  have hpos : (0 : ℝ) < D + 1 := by positivity
  have hdreal : (d : ℝ) ≤ (D : ℝ) := by exact_mod_cast hd
  have hle : (d : ℝ) / (D + 1 : ℝ) ≤ 1 := by
    rw [div_le_one hpos]
    linarith
  linarith

/--
@isnad1 id=eq.0h1v.s6.ac469553c0b3 from=translated src=- shape=f49d97f1 vocab=c0cfc1ee
-/
theorem sum_range_succ_real (D : ℕ) :
    (∑ i ∈ Finset.range D, (((i + 1 : ℕ) : ℝ)))
      = (D : ℝ) * (D + 1 : ℝ) / 2 := by
  induction D with
  | zero =>
      simp
  | succ D ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

/--
@isnad1 id=eq.0h1v.s7.f9a28342cae9 from=translated src=- shape=e9a5ee20 vocab=bebe769f
-/
theorem sum_range_succ_sq_real (D : ℕ) :
    (∑ i ∈ Finset.range D, (((i + 1 : ℕ) : ℝ) ^ 2))
      = (D : ℝ) * (D + 1 : ℝ) * (2 * (D : ℝ) + 1) / 6 := by
  induction D with
  | zero =>
      simp
  | succ D ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

/--
@isnad1 id=eq.0h1v.s5.38996da4abee from=translated src=- shape=fa01f7f9 vocab=50eedc77
-/
theorem sum_fejerWeight_range (D : ℕ) :
    (∑ i ∈ Finset.range D, fejerWeight D (i + 1)) = (D : ℝ) / 2 := by
  unfold fejerWeight
  rw [Finset.sum_sub_distrib]
  have hconst : (∑ _i ∈ Finset.range D, (1 : ℝ)) = (D : ℝ) := by
    simp
  have hdiv :
      (∑ i ∈ Finset.range D, (((i + 1 : ℕ) : ℝ) / (D + 1 : ℝ)))
        = ((∑ i ∈ Finset.range D, (((i + 1 : ℕ) : ℝ))) / (D + 1 : ℝ)) := by
    simp only [div_eq_mul_inv]
    rw [Finset.sum_mul]
  rw [hconst, hdiv, sum_range_succ_real]
  have hpos : (0 : ℝ) < D + 1 := by positivity
  field_simp [ne_of_gt hpos]
  ring

/--
@isnad1 id=eq.0h1v.s6.6bb4eff9b86f from=translated src=- shape=21154b4c vocab=a2a5ab6d
-/
theorem sum_mul_fejerWeight_range (D : ℕ) :
    (∑ i ∈ Finset.range D, (((i + 1 : ℕ) : ℝ) * fejerWeight D (i + 1)))
      = (D : ℝ) * (D + 2 : ℝ) / 6 := by
  unfold fejerWeight
  simp_rw [mul_sub, mul_one, mul_div_assoc]
  rw [Finset.sum_sub_distrib]
  have hdiv :
      (∑ i ∈ Finset.range D, (((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) / (D + 1 : ℝ))))
        =
      ((∑ i ∈ Finset.range D, (((i + 1 : ℕ) : ℝ) ^ 2)) / (D + 1 : ℝ)) := by
    calc
      (∑ i ∈ Finset.range D,
          (((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) / (D + 1 : ℝ))))
          = ∑ i ∈ Finset.range D,
              (((i + 1 : ℕ) : ℝ) ^ 2 / (D + 1 : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = ((∑ i ∈ Finset.range D, (((i + 1 : ℕ) : ℝ) ^ 2)) / (D + 1 : ℝ)) := by
            simp only [div_eq_mul_inv]
            rw [Finset.sum_mul]
  rw [sum_range_succ_real, hdiv, sum_range_succ_sq_real]
  have hpos : (0 : ℝ) < D + 1 := by positivity
  field_simp [ne_of_gt hpos]
  ring

/--
Exact count of the lower triangular differences:
the difference `i + 1` occurs exactly `D - i` times.
@isnad1 id=eq.0h2v.s6.f3c773df4d4a from=translated src=- shape=828b6cee vocab=a9fc3bcc
-/
theorem lowerTriangle_sum_eq_weighted_count (F : ℕ → ℝ) (D : ℕ) :
    (∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range r, F (r - s)) =
      ∑ i ∈ Finset.range D, ((D - i : ℕ) : ℝ) * F (i + 1) := by
  rw [Finset.sum_range_succ']
  simp only [Finset.range_zero, Finset.sum_empty, add_zero]
  have hrow :
      (∑ x ∈ Finset.range D, ∑ s ∈ Finset.range (x + 1), F (x + 1 - s)) =
      (∑ x ∈ Finset.range D, ∑ t ∈ Finset.range (x + 1), F (t + 1)) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have h := Finset.sum_range_reflect (fun t => F (t + 1)) (x + 1)
    calc
      (∑ s ∈ Finset.range (x + 1), F (x + 1 - s))
          = ∑ s ∈ Finset.range (x + 1), F (x - s + 1) := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            simp only [Finset.mem_range] at hs
            congr 1
            omega
      _ = ∑ t ∈ Finset.range (x + 1), F (t + 1) := h
  rw [hrow]
  have hflip := Finset.sum_range_diag_flip D (fun k _l => F (k + 1))
  calc
    (∑ x ∈ Finset.range D, ∑ t ∈ Finset.range (x + 1), F (t + 1))
        = ∑ i ∈ Finset.range D, ∑ _k ∈ Finset.range (D - i), F (i + 1) := by
          simpa using hflip
    _ = ∑ i ∈ Finset.range D, ((D - i : ℕ) : ℝ) * F (i + 1) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [Finset.sum_const, nsmul_eq_mul]

end FejerWeights

section WeightedFourierLower

/-- The weighted scalar power energy corresponding to the Fejér weights.-/
noncomputable def weightedGeomPowerEnergy (z : ℂ) (k D : ℕ) : ℝ :=
  ∑ i ∈ Finset.range D, fejerWeight D (i + 1) * ‖geomPowerSum z k (i + 1)‖ ^ 2

end WeightedFourierLower

section WeightedFourierBridge

variable {N : ℕ} [NeZero N]

end WeightedFourierBridge

section SqrtAlgebra

/-- Real Fejér lower bound before specializing `D`.-/
noncomputable def sqrtFejerLowerReal (k D : ℝ) : ℝ :=
  (k * (D + 1) - k ^ 2) / 2

/-- Real wrap-error upper bound before specializing `D`.-/
noncomputable def sqrtWrapUpperReal (k N D : ℝ) : ℝ :=
  (k - 1) * (D / 2)
    + (((k ^ 2 - (k - 1)) * (k - 1)) / N) * (D * (D + 2) / 6)

/-- The report's real threshold for the `sqrt(k)` target.-/
noncomputable def sqrtThresholdReal (k : ℝ) : ℝ :=
  (4 / 3) * (k ^ 2 - k + 1) * (k - 1) * (k * (k - 1) + 1)

end SqrtAlgebra

section SqrtThreshold

variable {N : ℕ} [NeZero N]

/--
Squared version of the `sqrt(k)` discrepancy target.

For an integer AP sum `z`, this is equivalent to `sqrt(k) ≤ |z|` over the reals.-/
def sqrtLargeSq (k : ℕ) (z : ℤ) : Prop :=
  (k : ℤ) ≤ z ^ 2

end SqrtThreshold

section PublicSqrtBound

/-- The report's displayed real threshold, with `k : ℕ`.-/
noncomputable def sqrtHtmlThresholdReal (k : ℕ) : ℝ :=
  sqrtThresholdReal (k : ℝ)

/-- The displayed integer upper bound, `floor(threshold) + 1`.-/
noncomputable def sqrtHtmlBoundNat (k : ℕ) : ℕ :=
  Nat.floor (sqrtHtmlThresholdReal k) + 1

/--
@isnad1 id=lt.0h1v.s3.f8ff34642881 from=translated src=- shape=8a62b088 vocab=6e44eb39
-/
theorem sqrtHtmlBoundNat_pos (k : ℕ) :
    0 < sqrtHtmlBoundNat k := by
  simp [sqrtHtmlBoundNat]

/--
@isnad1 id=lt.0h1v.s3.b7cdd6b15335 from=translated src=- shape=6b4ab8ce vocab=458979ab
-/
theorem sqrtHtmlThresholdReal_lt_sqrtHtmlBoundNat (k : ℕ) :
    sqrtHtmlThresholdReal k < (sqrtHtmlBoundNat k : ℝ) := by
  simpa [sqrtHtmlBoundNat, Nat.cast_add, Nat.cast_one]
    using Nat.lt_floor_add_one (sqrtHtmlThresholdReal k)

/--
@isnad1 id=lt.1h2v.s4.644a90813b68 from=translated src=- shape=9ab11ad5 vocab=a8acdb89
-/
theorem sqrtHtmlThresholdReal_lt_of_sqrtHtmlBoundNat_le
    {k N : ℕ}
    (hN : sqrtHtmlBoundNat k ≤ N) :
    sqrtHtmlThresholdReal k < (N : ℝ) := by
  have hfloor := sqrtHtmlThresholdReal_lt_sqrtHtmlBoundNat k
  have hNreal : (sqrtHtmlBoundNat k : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  exact lt_of_lt_of_le hfloor hNreal

/--
For a fixed coloring on `[0, N)`, there is a non-wrapping ordinary `k`-term AP
whose squared signed sum is at least `k`.-/
def hasLargeOrdinaryAPSqrtAt
    (k N : ℕ) (hNpos : 0 < N) (f : Fin N → ℤ) : Prop :=
  letI : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  ∃ d : ℕ, 0 < d ∧ ∃ a : Fin N,
    ∃ hnowrap : ¬ wraps (N := N) k a d,
      sqrtLargeSq k (ordinaryAPSum f k a d hnowrap)

/--
Formalized `N(k, sqrt(k))` property in squared form: every `±1` coloring of
`[0, N)` has a non-wrapping ordinary `k`-term AP whose squared sum is at least
`k`.-/
def erdos176SqrtGood (k N : ℕ) : Prop :=
  ∃ hNpos : 0 < N,
    ∀ f : Fin N → ℤ,
      (∀ x, f x = -1 ∨ f x = 1) →
        hasLargeOrdinaryAPSqrtAt k N hNpos f

/-- Public-facing name for the displayed `sqrt(k)` bound.-/
noncomputable abbrev sqrtReportBound (k : ℕ) : ℕ :=
  sqrtHtmlBoundNat k

end PublicSqrtBound

end Erdos176Lean

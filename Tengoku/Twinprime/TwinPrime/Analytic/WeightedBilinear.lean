import Tengoku.Twinprime.TwinPrime.Analytic.CharacterBilinear

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Weighted first moments over varying finite families

Cauchy--Schwarz on the combined outer and inner indices bounds products
using two second moments. The inner finite set may depend on the outer
index, as happens for character-dependent staircase intervals.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/-- Weighted Cauchy--Schwarz on two finite indices, with a varying inner set.
@isnad1 id=le.1h7v.s7.fb7eee2f72d1 from=translated src=- shape=ac1a7da3 vocab=410affd2
-/
theorem weighted_sum_sum_mul_le_sqrt_mul_sqrt {ι κ : Type*}
    (s : Finset ι) (J : ι → Finset κ) (w : ι → ℝ) (f g : ι → κ → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * ∑ j ∈ J i, f i j * g i j) ≤
      Real.sqrt (∑ i ∈ s, w i * ∑ j ∈ J i, f i j ^ 2) *
        Real.sqrt (∑ i ∈ s, w i * ∑ j ∈ J i, g i j ^ 2) := by
  have h := weighted_sum_mul_le_sqrt_mul_sqrt (s.sigma J)
    (fun p => w p.1) (fun p => f p.1 p.2) (fun p => g p.1 p.2)
    (fun p hp => hw p.1 (mem_sigma.mp hp).1)
  simpa only [sum_sigma, mul_sum, mul_assoc] using h

/-- Complex products are bounded by their two actual weighted square sums.
@isnad1 id=le.1h7v.s7.0e414019e106 from=translated src=- shape=fe7e81ac vocab=c0bff357
-/
theorem weighted_sum_sum_norm_mul_le_sqrt_mul_sqrt {ι κ : Type*}
    (s : Finset ι) (J : ι → Finset κ) (w : ι → ℝ) (A B : ι → κ → ℂ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * ∑ j ∈ J i, ‖A i j * B i j‖) ≤
      Real.sqrt (∑ i ∈ s, w i * ∑ j ∈ J i, ‖A i j‖ ^ 2) *
        Real.sqrt (∑ i ∈ s, w i * ∑ j ∈ J i, ‖B i j‖ ^ 2) := by
  simpa only [norm_mul] using weighted_sum_sum_mul_le_sqrt_mul_sqrt s J w
    (fun i j => ‖A i j‖) (fun i j => ‖B i j‖) hw

/-- Bounds on the two second moments give a first-moment product bound.
Separate nonnegativity hypotheses on the budgets are unnecessary: they
already follow from the displayed square-sum bounds and nonnegative weights.
@isnad1 id=le.3h9v.s7.f077594b35eb from=translated src=- shape=69ae2b38 vocab=c0bff357
-/
theorem weighted_sum_sum_norm_mul_le {ι κ : Type*}
    (s : Finset ι) (J : ι → Finset κ) (w : ι → ℝ) (A B : ι → κ → ℂ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (EA EB : ℝ)
    (hA : (∑ i ∈ s, w i * ∑ j ∈ J i, ‖A i j‖ ^ 2) ≤ EA)
    (hB : (∑ i ∈ s, w i * ∑ j ∈ J i, ‖B i j‖ ^ 2) ≤ EB) :
    (∑ i ∈ s, w i * ∑ j ∈ J i, ‖A i j * B i j‖) ≤
      Real.sqrt EA * Real.sqrt EB := by
  exact (weighted_sum_sum_norm_mul_le_sqrt_mul_sqrt s J w A B hw).trans
    (mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- The corresponding first-moment bound for a single finite index.
@isnad1 id=le.3h7v.s7.8c2000798ffd from=translated src=- shape=bfe08148 vocab=c0bff357
-/
theorem weighted_sum_norm_mul_le {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (A B : ι → ℂ) (hw : ∀ i ∈ s, 0 ≤ w i) (EA EB : ℝ)
    (hA : (∑ i ∈ s, w i * ‖A i‖ ^ 2) ≤ EA)
    (hB : (∑ i ∈ s, w i * ‖B i‖ ^ 2) ≤ EB) :
    (∑ i ∈ s, w i * ‖A i * B i‖) ≤ Real.sqrt EA * Real.sqrt EB := by
  simpa only [sum_singleton] using weighted_sum_sum_norm_mul_le s (fun _ => {()}) w
    (fun i (_ : Unit) => A i) (fun i (_ : Unit) => B i) hw EA EB
    (by simpa only [sum_singleton] using hA) (by simpa only [sum_singleton] using hB)

/-- The norm may instead surround the inner sum, by the finite triangle inequality.
@isnad1 id=le.3h9v.s7.7f971f246b38 from=translated src=- shape=0a8d4c2f vocab=c0bff357
-/
theorem weighted_sum_norm_sum_mul_le {ι κ : Type*}
    (s : Finset ι) (J : ι → Finset κ) (w : ι → ℝ) (A B : ι → κ → ℂ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (EA EB : ℝ)
    (hA : (∑ i ∈ s, w i * ∑ j ∈ J i, ‖A i j‖ ^ 2) ≤ EA)
    (hB : (∑ i ∈ s, w i * ∑ j ∈ J i, ‖B i j‖ ^ 2) ≤ EB) :
    (∑ i ∈ s, w i * ‖∑ j ∈ J i, A i j * B i j‖) ≤
      Real.sqrt EA * Real.sqrt EB := by
  calc
    _ ≤ ∑ i ∈ s, w i * ∑ j ∈ J i, ‖A i j * B i j‖ :=
      sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hw i hi)
    _ ≤ _ := weighted_sum_sum_norm_mul_le s J w A B hw EA EB hA hB

/-- A varying finite family of factorized rectangular sums has the same bound.
@isnad1 id=le.3h13v.s8.2ed387402fb4 from=translated src=- shape=b6731a4b vocab=c0bff357
-/
theorem weighted_sum_sum_norm_rectangular_le {ι κ α β : Type*}
    (s : Finset ι) (J : ι → Finset κ) (w : ι → ℝ)
    (U : ι → κ → Finset α) (V : ι → κ → Finset β)
    (a : ι → α → ℂ) (b : ι → β → ℂ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (EA EB : ℝ)
    (hA : (∑ i ∈ s, w i * ∑ j ∈ J i, ‖∑ m ∈ U i j, a i m‖ ^ 2) ≤ EA)
    (hB : (∑ i ∈ s, w i * ∑ j ∈ J i, ‖∑ n ∈ V i j, b i n‖ ^ 2) ≤ EB) :
    (∑ i ∈ s, w i * ∑ j ∈ J i, ‖∑ m ∈ U i j, ∑ n ∈ V i j, a i m * b i n‖) ≤
      Real.sqrt EA * Real.sqrt EB := by
  have h := weighted_sum_sum_norm_mul_le s J w
    (fun i j => ∑ m ∈ U i j, a i m) (fun i j => ∑ n ∈ V i j, b i n)
    hw EA EB hA hB
  simpa only [sum_mul_sum] using h

/-- A prefix baseline and `k` disjoint-interval levels have the safe
staircase factor `2(k+1)(j+1)`.
@isnad1 id=le.2h4v.s7.7a3b8d70f07f from=translated src=- shape=0c482b7b vocab=00494cef
-/
theorem sqrt_baseline_add_levels_le (EA EB : ℝ) (_hEA : 0 ≤ EA) (hEB : 0 ≤ EB)
    (k j : ℕ) :
    Real.sqrt EA * Real.sqrt (((j : ℝ) + 1) ^ 2 * EB) +
        (k : ℝ) * (Real.sqrt EA * Real.sqrt ((2 * ((j : ℝ) + 1) ^ 2) * EB)) ≤
      (2 * ((k : ℝ) + 1) * ((j : ℝ) + 1)) * Real.sqrt EA * Real.sqrt EB := by
  have hj : 0 ≤ (j : ℝ) + 1 := by positivity
  have hbase : Real.sqrt (((j : ℝ) + 1) ^ 2 * EB) =
      ((j : ℝ) + 1) * Real.sqrt EB := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hj]
  have hlevel : Real.sqrt ((2 * ((j : ℝ) + 1) ^ 2) * EB) ≤
      (2 * ((j : ℝ) + 1)) * Real.sqrt EB := by
    calc
      _ ≤ Real.sqrt ((2 * ((j : ℝ) + 1)) ^ 2 * EB) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right
          (by nlinarith [sq_nonneg ((j : ℝ) + 1)]) hEB)
      _ = _ := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [hbase]
  calc
    _ ≤ Real.sqrt EA * (((j : ℝ) + 1) * Real.sqrt EB) +
        (k : ℝ) * (Real.sqrt EA * ((2 * ((j : ℝ) + 1)) * Real.sqrt EB)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlevel (Real.sqrt_nonneg _)) (Nat.cast_nonneg _))
    _ ≤ _ := by
      have hp : 0 ≤ Real.sqrt EA * ((j : ℝ) + 1) * Real.sqrt EB := by positivity
      nlinarith

end TwinPrime.Analytic

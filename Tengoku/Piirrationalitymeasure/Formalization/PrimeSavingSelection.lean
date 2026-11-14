import Tengoku.Piirrationalitymeasure.Formalization.PrimeSavingComponents
import Tengoku.Piirrationalitymeasure.Formalization.Denominator
import Tengoku.Piirrationalitymeasure.Formalization.PrimeSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The periodic interval set selects the actual prime factors of Phi. -/

namespace PiIrrationality

private theorem fract_nat_mul_fract_add (k : ℕ) (u t : ℝ) :
    Int.fract ((k : ℝ) * Int.fract u + t) = Int.fract ((k : ℝ) * u + t) := by
  have heq : (k : ℝ) * Int.fract u + t =
      ((k : ℝ) * u + t) - (((k : ℤ) * ⌊u⌋ : ℤ) : ℝ) := by
    simp only [Int.fract, Int.cast_mul, Int.cast_natCast]
    ring
  rw [heq, Int.fract_sub_intCast]

/--
@isnad1 id=iff.0h1v.s3.09bb23ce261a from=translated src=- shape=f58cbc93 vocab=8568547c
-/
theorem primeSavingCondition_fract (u : ℝ) :
    primeSavingCondition (Int.fract u) ↔ primeSavingCondition u := by
  have h₁ := fract_nat_mul_fract_add 1857 u (1 / 2)
  have h₂ := fract_nat_mul_fract_add 3714 u 0
  have h₃ := fract_nat_mul_fract_add 5570 u 0
  norm_num only [Nat.cast_ofNat, add_zero] at h₁ h₂ h₃
  simp only [primeSavingCondition, h₁, h₂, h₃]

/--
@isnad1 id=iff.0h1v.s4.e1ad00ca786d from=translated src=- shape=754ed894 vocab=84e04c79
-/
theorem fract_mem_primeSavingSet (u : ℝ) :
    Int.fract u ∈ primeSavingSet ↔ primeSavingCondition u := by
  simp only [primeSavingSet, Set.mem_ofPred_eq, Int.fract_nonneg, Int.fract_lt_one,
    true_and, primeSavingCondition_fract]

/--
@isnad1 id=iff.0h2v.s6.5abe4df5a5f6 from=translated src=- shape=4d00bf08 vocab=8cf17155
-/
theorem removablePrime_iff_periodic (n p : ℕ) :
    removablePrime n p ↔ Nat.Prime p ∧ 5 < p ∧ Nat.sqrt (7430 * n) < p ∧
      p ≤ 7430 * n ∧ Int.fract ((n : ℝ) / p) ∈ primeSavingSet := by
  rw [fract_mem_primeSavingSet]
  unfold removablePrime primeSavingCondition
  have hcast :
      (Int.fract (((1857 * n : ℕ) : ℚ) / p + 1 / 2) +
        2 * Int.fract (((3714 * n : ℕ) : ℚ) / p) <
        Int.fract (((5570 * n : ℕ) : ℚ) / p)) ↔
      Int.fract (1857 * ((n : ℝ) / p) + 1 / 2) +
        2 * Int.fract (3714 * ((n : ℝ) / p)) < Int.fract (5570 * ((n : ℝ) / p)) := by
    rw [← Rat.cast_lt (K := ℝ)]
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_fract,
      Rat.cast_div, Rat.cast_natCast, Rat.cast_one, Nat.cast_mul, Nat.cast_ofNat,
      mul_div_assoc]
  rw [hcast]

/--
@isnad1 id=iff.0h2v.s7.624aba9fe493 from=translated src=- shape=2f68fcb6 vocab=99f11e92
-/
theorem removablePrime_iff_intervals (n p : ℕ) :
    removablePrime n p ↔ Nat.Prime p ∧ 5 < p ∧ Nat.sqrt (7430 * n) < p ∧
      p ≤ 7430 * n ∧ ∃ j ∈ activeSavingCells,
        savingLeft j ≤ Int.fract ((n : ℝ) / p) ∧
          Int.fract ((n : ℝ) / p) < savingRight j := by
  rw [removablePrime_iff_periodic, primeSavingSet_eq_intervals]
  simp only [Set.mem_iUnion, savingInterval, Set.mem_Ico, exists_prop]

/--
@isnad1 id=iff.1h2v.s6.f6e78649773f from=translated src=- shape=0cb966e7 vocab=8cf17155
-/
theorem removablePrime_iff_periodic_of_pos {n : ℕ} (hn : 1 ≤ n) (p : ℕ) :
    removablePrime n p ↔ Nat.Prime p ∧ Nat.sqrt (7430 * n) < p ∧
      p ≤ 7430 * n ∧ Int.fract ((n : ℝ) / p) ∈ primeSavingSet := by
  rw [removablePrime_iff_periodic]
  constructor
  · rintro ⟨hp, h5, hs, hb, he⟩
    exact ⟨hp, hs, hb, he⟩
  · rintro ⟨hp, hs, hb, he⟩
    have hsq : 7430 * n < p ^ 2 := Nat.sqrt_lt'.mp hs
    have h5 : 5 < p := by nlinarith
    exact ⟨hp, h5, hs, hb, he⟩

noncomputable def primeSavingSeries : ℝ :=
  ∑ j ∈ activeSavingCells, ∑' q : ℕ, periodicSummandReal (savingLeft j) (savingRight j) q

/--
@isnad1 id=summable.1h1v.s5.13363e94cdc4 from=translated src=- shape=55a23acc vocab=2fd0ced6
-/
theorem savingInterval_series_summable {j : ℕ} (hj : j ∈ activeSavingCells) :
    Summable (fun q => periodicSummandReal (savingLeft j) (savingRight j) q) := by
  have he := savingInterval_endpoints hj
  exact periodicSummandReal_summable he.1 he.2.1 he.2.2.2.le

/--
@isnad1 id=eq.0h0v.s6.e72f86fe8474 from=translated src=- shape=feab7bb1 vocab=bce0e242
-/
theorem primeSavingSeries_eq_endpoint_series :
    primeSavingSeries = ∑ j ∈ activeSavingCells, ∑' q : ℕ,
      (1 / ((q : ℝ) + savingLeft j) - 1 / ((q : ℝ) + savingRight j)) := by
  apply Finset.sum_congr rfl
  intro j hj
  apply tsum_congr
  intro q
  have he := savingInterval_endpoints hj
  have hℓ : (q : ℝ) + savingLeft j ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (Nat.cast_nonneg q) he.1)
  have hr : (q : ℝ) + savingRight j ≠ 0 := ne_of_gt (by linarith [Nat.cast_nonneg (α := ℝ) q])
  unfold periodicSummandReal
  field_simp
  <;> ring

end PiIrrationality

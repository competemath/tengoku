import Tengoku.Piirrationalitymeasure.Formalization.PeriodIntegral
import Tengoku.Piirrationalitymeasure.Formalization.PrimeSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Integration of a periodic union of intervals against t^(-2), as in (6.5). -/

namespace PiIrrationality

open MeasureTheory Set

/--
@isnad1 id=interval.3h3v.s6.4dd7033da450 from=translated src=- shape=666a8a2b vocab=40ca5022
-/
theorem inverse_square_interval_integrable {k ell r : ℝ} (hk : 0 ≤ k)
    (hell : 0 < ell) (hr : ell ≤ r) :
    IntervalIntegrable (fun u : ℝ => 1 / (k + u) ^ 2) volume ell r := by
  apply ContinuousOn.intervalIntegrable_of_Icc hr
  intro u hu
  have hden : k + u ≠ 0 := by linarith [hu.1]
  have hden2 : (k + u) ^ 2 ≠ 0 := pow_ne_zero 2 hden
  fun_prop

/--
@isnad1 id=eq.3h3v.s7.f3a016e135d4 from=translated src=- shape=6fe64f97 vocab=2d7629f5
-/
theorem inverse_square_interval_integral {k ell r : ℝ} (hk : 0 ≤ k)
    (hell : 0 < ell) (hr : ell ≤ r) :
    (∫ u in ell..r, 1 / (k + u) ^ 2) = 1 / (k + ell) - 1 / (k + r) := by
  have hd : ∀ u ∈ Set.uIcc ell r,
      HasDerivAt (fun u : ℝ => -(k + u)⁻¹) (1 / (k + u) ^ 2) u := by
    intro u hu
    rw [Set.uIcc_of_le hr] at hu
    have hden : k + u ≠ 0 := by linarith [hu.1]
    simpa only [neg_div, neg_neg] using! (((hasDerivAt_id u).const_add k).inv hden).neg
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (inverse_square_interval_integrable hk hell hr)
  simpa only [one_div, neg_sub_neg] using h

/--
@isnad1 id=eq.3h5v.s8.4c6c80f80581 from=translated src=- shape=1f851985 vocab=0eaf4a45
-/
theorem periodic_weighted_cell_integral (chi : ℝ → ℝ) (k : ℕ) (J : Finset ℕ)
    (ell r : ℕ → ℝ)
    (hend : ∀ j ∈ J, 0 < ell j ∧ ell j < r j ∧ r j ≤ 1)
    (hdis : Set.Pairwise (↑J) (fun i j => Disjoint (Ico (ell i) (r i)) (Ico (ell j) (r j))))
    (hchi : ∀ u ∈ Ico (0 : ℝ) 1,
      chi u = (⋃ j ∈ J, Ico (ell j) (r j)).indicator (fun _ => (1 : ℝ)) u) :
    (∫ u in (0 : ℝ)..1, chi u / ((k : ℝ) + u) ^ 2) =
      ∑ j ∈ J, (1 / ((k : ℝ) + ell j) - 1 / ((k : ℝ) + r j)) := by
  classical
  let E := ⋃ j ∈ J, Ico (ell j) (r j)
  have hm : MeasurableSet E := by
    dsimp [E]
    exact J.measurableSet_biUnion (fun j _ => measurableSet_Ico)
  have hsub : E ⊆ Ico (0 : ℝ) 1 := by
    intro u hu
    obtain ⟨j, hu⟩ := mem_iUnion.mp hu
    obtain ⟨hj, hu⟩ := mem_iUnion.mp hu
    have he := hend j hj
    exact ⟨he.1.le.trans hu.1, hu.2.trans_le he.2.2⟩
  have hi : ∀ j ∈ J, IntegrableOn (fun u : ℝ => 1 / ((k : ℝ) + u) ^ 2)
      (Ico (ell j) (r j)) := by
    intro j hj
    have he := hend j hj
    have h := inverse_square_interval_integrable (Nat.cast_nonneg k) he.1 he.2.1.le
    exact (intervalIntegrable_iff_integrableOn_Ico_of_le he.2.1.le).mp h
  calc
    _ = ∫ u in Ico (0 : ℝ) 1, chi u / ((k : ℝ) + u) ^ 2 := by
      rw [intervalIntegral.integral_of_le (by norm_num), integral_Ico_eq_integral_Ioc]
    _ = ∫ u in Ico (0 : ℝ) 1,
        E.indicator (fun u => 1 / ((k : ℝ) + u) ^ 2) u := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro u hu
      dsimp only
      rw [hchi u hu]
      change E.indicator (fun _ => (1 : ℝ)) u / ((k : ℝ) + u) ^ 2 = _
      by_cases he : u ∈ E <;> simp [he]
    _ = ∫ u in E, 1 / ((k : ℝ) + u) ^ 2 := by
      rw [setIntegral_indicator hm, inter_eq_right.mpr hsub]
    _ = ∑ j ∈ J, ∫ u in Ico (ell j) (r j), 1 / ((k : ℝ) + u) ^ 2 :=
      integral_biUnion_finset J (fun _ _ => measurableSet_Ico) hdis hi
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have he := hend j hj
      rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le he.2.1.le]
      exact inverse_square_interval_integral (Nat.cast_nonneg k) he.1 he.2.1.le

/--
@isnad1 id=eq.5h4v.s8.0ee7173fb579 from=translated src=- shape=d6b33b54 vocab=0fe740bb
-/
theorem periodic_saving_integral_eq_series (chi : ℝ → ℝ) (J : Finset ℕ) (ell r : ℕ → ℝ)
    (hper : ∀ (k : ℕ) (u : ℝ), chi ((k : ℝ) + u) = chi u)
    (hi : IntegrableOn (fun t : ℝ => chi t / t ^ 2) (Ioi (0 : ℝ)))
    (hend : ∀ j ∈ J, 0 < ell j ∧ ell j < r j ∧ r j ≤ 1)
    (hdis : Set.Pairwise (↑J) (fun i j => Disjoint (Ico (ell i) (r i)) (Ico (ell j) (r j))))
    (hchi : ∀ u ∈ Ico (0 : ℝ) 1,
      chi u = (⋃ j ∈ J, Ico (ell j) (r j)).indicator (fun _ => (1 : ℝ)) u) :
    (∫ t in Ioi (0 : ℝ), chi t / t ^ 2) =
      ∑ j ∈ J, ∑' k : ℕ, periodicSummandReal (ell j) (r j) k := by
  have hcell : ∀ k : ℕ, (∫ u in (0 : ℝ)..1, chi ((k : ℝ) + u) / ((k : ℝ) + u) ^ 2) =
      ∑ j ∈ J, periodicSummandReal (ell j) (r j) k := by
    intro k
    simp_rw [hper k]
    rw [periodic_weighted_cell_integral chi k J ell r hend hdis hchi]
    apply Finset.sum_congr rfl
    intro j hj
    have hL : (k : ℝ) + ell j ≠ 0 := by linarith [(hend j hj).1, Nat.cast_nonneg (α := ℝ) k]
    have hR : (k : ℝ) + r j ≠ 0 := by
      linarith [(hend j hj).1, (hend j hj).2.1, Nat.cast_nonneg (α := ℝ) k]
    unfold periodicSummandReal
    field_simp
    ring
  have h := hasSum_integral_shifted_periods hi
  simp_rw [hcell] at h
  have hs : HasSum (fun k : ℕ => ∑ j ∈ J, periodicSummandReal (ell j) (r j) k)
      (∑ j ∈ J, ∑' k : ℕ, periodicSummandReal (ell j) (r j) k) := by
    apply hasSum_sum
    intro j hj
    have he := hend j hj
    exact (periodicSummandReal_summable he.1 he.2.1 he.2.2).hasSum
  exact h.unique hs

end PiIrrationality

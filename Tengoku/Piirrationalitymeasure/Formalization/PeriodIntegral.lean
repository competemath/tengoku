import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Decomposition of an integrable function on the positive half-line into unit periods. -/

namespace PiIrrationality

open MeasureTheory Set

theorem nat_unit_intervals_disjoint :
    Pairwise (fun k l : ℕ => Disjoint (Ico (k : ℝ) ((k : ℝ) + 1))
      (Ico (l : ℝ) ((l : ℝ) + 1))) := by
  intro k l hkl
  wlog h : k < l generalizing k l
  · exact (this hkl.symm (lt_of_le_of_ne (Nat.le_of_not_gt h) hkl.symm)).symm
  apply Set.disjoint_left.mpr
  intro t hk hl
  have hcast : (k : ℝ) + 1 ≤ l := by exact_mod_cast h
  linarith [hk.2, hl.1]

theorem nat_unit_intervals_union :
    (⋃ k : ℕ, Ico (k : ℝ) ((k : ℝ) + 1)) = Ici (0 : ℝ) := by
  ext t
  simp only [mem_iUnion, mem_Ico, mem_Ici]
  constructor
  · rintro ⟨k, hk, _⟩
    exact (Nat.cast_nonneg k).trans hk
  · intro ht
    exact ⟨⌊t⌋₊, Nat.floor_le ht, Nat.lt_floor_add_one t⟩

theorem hasSum_integral_nat_periods {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi (0 : ℝ))) :
    HasSum (fun k : ℕ => ∫ t in (k : ℝ)..((k : ℝ) + 1), f t)
      (∫ t in Ioi (0 : ℝ), f t) := by
  have hi : IntegrableOn f (⋃ k : ℕ, Ico (k : ℝ) ((k : ℝ) + 1)) := by
    rw [nat_unit_intervals_union]
    exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hf
  have h := hasSum_integral_iUnion (fun k : ℕ =>
    (measurableSet_Ico : MeasurableSet (Ico (k : ℝ) ((k : ℝ) + 1))))
      nat_unit_intervals_disjoint hi
  rw [nat_unit_intervals_union, integral_Ici_eq_integral_Ioi] at h
  have he : (fun k : ℕ => ∫ t in (k : ℝ)..((k : ℝ) + 1), f t) =
      (fun k : ℕ => ∫ t in Ico (k : ℝ) ((k : ℝ) + 1), f t) := by
    funext k
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ico_eq_integral_Ioc]
  rw [he]
  exact h

theorem hasSum_integral_shifted_periods {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi (0 : ℝ))) :
    HasSum (fun k : ℕ => ∫ u in (0 : ℝ)..1, f ((k : ℝ) + u))
      (∫ t in Ioi (0 : ℝ), f t) := by
  have he : (fun k : ℕ => ∫ u in (0 : ℝ)..1, f ((k : ℝ) + u)) =
      (fun k : ℕ => ∫ t in (k : ℝ)..((k : ℝ) + 1), f t) := by
    funext k
    simpa only [add_zero] using
      intervalIntegral.integral_comp_add_left (a := 0) (b := 1) f (k : ℝ)
  rw [he]
  exact hasSum_integral_nat_periods hf

end PiIrrationality

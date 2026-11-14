import Tengoku.Piirrationalitymeasure.Formalization.Statements

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A lower bound on the defining set of irrationality-measure exponents. -/

namespace PiIrrationality

/--
@isnad1 id=le.1h2v.s4.b289b3ee724a from=translated src=- shape=f99f57a5 vocab=c9bd228c
-/
theorem IrrationalityMeasureAtMost.nonneg {theta mu : ℝ}
    (h : IrrationalityMeasureAtMost theta mu) : 0 ≤ mu := by
  by_contra hm
  have hm0 : mu < 0 := lt_of_not_ge hm
  obtain ⟨q0, hq0⟩ := h (-mu) (by linarith)
  let q : ℕ := q0 + 1
  let p : ℤ := ⌊(q : ℝ) * theta⌋
  have hq : 0 < q := by dsimp [q]; omega
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hb := hq0 p q (by dsimp [q]; omega) hq
  simp only [sub_self, Real.rpow_zero] at hb
  have hfL : (p : ℝ) ≤ (q : ℝ) * theta := Int.floor_le _
  have hfU : (q : ℝ) * theta < (p : ℝ) + 1 := Int.lt_floor_add_one _
  have he : theta - (p : ℝ) / (q : ℝ) = ((q : ℝ) * theta - (p : ℝ)) / (q : ℝ) := by
    field_simp
  have hf : 0 ≤ ((q : ℝ) * theta - (p : ℝ)) / (q : ℝ) :=
    div_nonneg (by linarith) hqR.le
  rw [he, abs_of_nonneg hf] at hb
  have hu : ((q : ℝ) * theta - (p : ℝ)) / (q : ℝ) < 1 := by
    apply (div_lt_iff₀ hqR).mpr
    linarith
  linarith

/--
@isnad1 id=bddbelow.0h1v.s3.5511e7ddefee from=translated src=- shape=9b9e1b9d vocab=969859af
-/
theorem irrationalityMeasure_exponents_bddBelow (theta : ℝ) :
    BddBelow {mu : ℝ | IrrationalityMeasureAtMost theta mu} :=
  ⟨0, fun _ hm => hm.nonneg⟩

end PiIrrationality

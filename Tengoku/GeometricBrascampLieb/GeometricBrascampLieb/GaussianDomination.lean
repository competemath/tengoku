import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.GaussianBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Local uniform Gaussian domination

Continuous coefficients and a strictly positive Gaussian decay rate give one
integrable majorant on a neighborhood of every positive time.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace GeometricBrascampLieb

/--
@isnad1 id=le.0h5v.s7.dd043e4c74c9 from=translated src=- shape=5abffc89 vocab=8e6b9641
-/
theorem abs_quadratic_mul_gaussian_le (A P R b r : ℝ) :
    |A * (P + R * r ^ 2) * Real.exp (-b * r ^ 2)| ≤
      (|A| * (|P| + |R|)) * (1 + r ^ 2) * Real.exp (-b * r ^ 2) := by
  have hp : |P + R * r ^ 2| ≤ (|P| + |R|) * (1 + r ^ 2) := by
    calc
      _ ≤ |P| + |R| * r ^ 2 := by
        have hr : |R * r ^ 2| = |R| * r ^ 2 := by rw [abs_mul, abs_of_nonneg (sq_nonneg r)]
        rw [← hr]
        exact abs_add_le P (R * r ^ 2)
      _ ≤ _ := by nlinarith [abs_nonneg P, abs_nonneg R, mul_nonneg (abs_nonneg P) (sq_nonneg r)]
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (|A| * ((|P| + |R|) * (1 + r ^ 2))) * Real.exp (-b * r ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (abs_nonneg A)) (Real.exp_pos _).le
    _ = _ := by ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/--
@isnad1 id=integrab.1h6v.s7.10b6eb0844d7 from=translated src=- shape=c70b9a16 vocab=672f89d2
-/
theorem integrable_quadratic_mul_gaussian (z : E) (A P R : ℝ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : E => A * (P + R * ‖x - z‖ ^ 2) * Real.exp (-b * ‖x - z‖ ^ 2)) := by
  apply integrable_of_polynomial_gaussian_bound (by fun_prop) z 2 (|A| * (|P| + |R|)) hb
  intro x
  exact abs_quadratic_mul_gaussian_le A P R b ‖x - z‖

/-- A local time-independent integrable bound for Gaussian quadratic expressions.
@isnad1 id=ex.6h7v.s8.3b112cf4b2a7 from=translated src=- shape=625f65f3 vocab=b133142e
-/
theorem exists_local_quadratic_gaussian_bound
    (z : E) {A b P R : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (hb : 0 < b t)
    (hA : ContinuousAt A t) (hbcont : ContinuousAt b t)
    (hP : ContinuousAt P t) (hR : ContinuousAt R t) :
    ∃ V ∈ 𝓝 t, V ⊆ Ioi 0 ∧ ∃ g : E → ℝ, Integrable g ∧
      ∀ s ∈ V, ∀ x,
        ‖A s * (P s + R s * ‖x - z‖ ^ 2) * Real.exp (-b s * ‖x - z‖ ^ 2)‖ ≤ g x := by
  let M : ℝ → ℝ := fun s => |A s| * (|P s| + |R s|)
  let C := M t + 1
  have hM : ContinuousAt M t := hA.abs.mul (hP.abs.add hR.abs)
  have hC : 0 ≤ C := by dsimp [C, M]; positivity
  have hMC : ∀ᶠ s in 𝓝 t, M s < C :=
    hM.eventually_lt continuousAt_const (by dsimp [C]; linarith)
  have hbb : ∀ᶠ s in 𝓝 t, b t / 2 < b s :=
    continuousAt_const.eventually_lt hbcont (by linarith)
  let V := {s : ℝ | 0 < s ∧ M s < C ∧ b t / 2 < b s}
  have hV : V ∈ 𝓝 t := by
    filter_upwards [Ioi_mem_nhds ht, hMC, hbb] with s hs hms hbs
    exact ⟨hs, hms, hbs⟩
  let g : E → ℝ := fun x => C * (1 + ‖x - z‖ ^ 2) * Real.exp (-(b t / 2) * ‖x - z‖ ^ 2)
  refine ⟨V, hV, (fun _ hs => hs.1), g, ?_, ?_⟩
  · have hg := integrable_quadratic_mul_gaussian z C 1 1 (half_pos hb)
    simpa only [one_mul] using hg
  · intro s hs x
    have hr : 0 ≤ 1 + ‖x - z‖ ^ 2 := by positivity
    have he : Real.exp (-b s * ‖x - z‖ ^ 2) ≤ Real.exp (-(b t / 2) * ‖x - z‖ ^ 2) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg hs.2.2.le) (sq_nonneg _)
    calc
      _ ≤ M s * (1 + ‖x - z‖ ^ 2) * Real.exp (-b s * ‖x - z‖ ^ 2) :=
        abs_quadratic_mul_gaussian_le (A s) (P s) (R s) (b s) ‖x - z‖
      _ ≤ C * (1 + ‖x - z‖ ^ 2) * Real.exp (-b s * ‖x - z‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs.2.1.le hr) (Real.exp_pos _).le
      _ ≤ g x := mul_le_mul_of_nonneg_left he (mul_nonneg hC hr)

end GeometricBrascampLieb

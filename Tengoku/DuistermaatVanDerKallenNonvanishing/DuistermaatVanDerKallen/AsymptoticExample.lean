import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.CriticalLocus
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The manuscript's escape-to-infinity regression, with the proper induced
Hermitian metric and the true torus partials. The value `c` is regular but
asymptotic critical. Newton interiority is supplied in `AsymptoticExampleNewton`. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Filter
open scoped Topology

/-- An ambient polynomial representing `c + x + (y-1)²/(xy)` on the torus.-/
def infinityExamplePolynomial (c : ℂ) : AmbientPolynomial 2 :=
  MvPolynomial.C c + MvPolynomial.X (.inl 0) +
    MvPolynomial.X (.inr 0) * MvPolynomial.X (.inr 1) * (MvPolynomial.X (.inl 1) - 1) ^ 2

theorem infinityExample_eval (c : ℂ) (x : TorusAmbient 2) :
    ambientEval (infinityExamplePolynomial c) x =
      c + x (.inl 0) + x (.inr 0) * x (.inr 1) * (x (.inl 1) - 1) ^ 2 := by
  simp [infinityExamplePolynomial, ambientEval]

theorem infinityExample_partial_zero (c : ℂ) (x : TorusAmbient 2) :
    ambientEval (torusPartial (infinityExamplePolynomial c) 0) x =
      1 - x (.inr 0) ^ 2 * x (.inr 1) * (x (.inl 1) - 1) ^ 2 := by
  simp [torusPartial, infinityExamplePolynomial, ambientEval]
  ring

/-- A direct algebraic certificate excludes critical points in the fiber at `c`.-/
theorem infinityExample_regular_identity (c : ℂ) {x : TorusAmbient 2}
    (hx : x ∈ affineTorus 2) :
    ambientEval (torusPartial (infinityExamplePolynomial c) 0) x +
      x (.inr 0) * (ambientEval (infinityExamplePolynomial c) x - c) = 2 := by
  rw [infinityExample_eval, infinityExample_partial_zero]
  have h := hx 0
  calc
    _ = 1 + x (.inl 0) * x (.inr 0) := by ring
    _ = 2 := by rw [h]; norm_num

theorem infinityExample_not_ordinary (c : ℂ) :
    c ∉ ordinaryCriticalValues
      (fun x : affineTorus 2 => ambientEval (infinityExamplePolynomial c) x.val)
      (fun x => ambientDifferentialNorm (torusPartial (infinityExamplePolynomial c)) x.val) := by
  rintro ⟨x, hx, he⟩
  have h := infinityExample_regular_identity c x.property
  have hz := (ambientDifferentialNorm_eq_zero_iff _ _).mp hx 0
  change ambientEval (infinityExamplePolynomial c) x.val = c at he
  rw [hz, he] at h
  norm_num at h

theorem infinityExample_line_eval (c t : ℂ) :
    ambientEval (infinityExamplePolynomial c) (torusEmbed ![t, 1]) = c + t := by
  simp [infinityExample_eval, torusEmbed]

theorem infinityExample_line_partials (c t : ℂ) (i : Fin 2) :
    ambientEval (torusPartial (infinityExamplePolynomial c) i) (torusEmbed ![t, 1]) =
      if i = 0 then 1 else 0 := by
  fin_cases i <;> simp [torusPartial, infinityExamplePolynomial, ambientEval, torusEmbed]

theorem infinityExample_line_gradient (c t : ℂ) :
    ambientDifferentialNorm (torusPartial (infinityExamplePolynomial c))
      (torusEmbed ![t, 1]) = Real.sqrt (1 / (1 + ‖t⁻¹‖ ^ 4)) := by
  simp only [ambientDifferentialNorm, differentialNormSq, infinityExample_line_partials]
  simp [Fin.sum_univ_two, torusEmbed]

theorem infinityExample_line_norm (t : ℂ) :
    ‖torusEmbed ![t, 1]‖ ^ 2 = ‖t‖ ^ 2 + ‖t‖⁻¹ ^ 2 + 2 := by
  simp [torusEmbed_norm_sq, Fin.sum_univ_two]
  ring

theorem infinityExample_inverse_norm (a : ℝ) (ha : 1 ≤ a) :
    a ≤ ‖torusEmbed ![(a : ℂ)⁻¹, 1]‖ ∧
      ‖torusEmbed ![(a : ℂ)⁻¹, 1]‖ ≤ 2 * a := by
  have ha0 : 0 < a := by linarith
  have hna : ‖(a : ℂ)‖ = a := by simp [abs_of_pos ha0]
  constructor
  · have h := PiLp.norm_apply_le (torusEmbed ![(a : ℂ)⁻¹, 1]) (.inr 0)
    simpa [torusEmbed, abs_of_pos ha0] using h
  · have hn := infinityExample_line_norm ((a : ℂ)⁻¹)
    simp only [norm_inv, hna, inv_inv] at hn
    have hi : 0 ≤ a⁻¹ := inv_nonneg.mpr ha0.le
    have hi1 : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha
    have hia : a⁻¹ ^ 2 ≤ 1 := by nlinarith
    have ha2 : 1 ≤ a ^ 2 := by nlinarith
    nlinarith [norm_nonneg (torusEmbed ![(a : ℂ)⁻¹, 1])]

theorem infinityExample_inverse_gradient (c : ℂ) (a : ℝ) (ha : 1 ≤ a) :
    ambientDifferentialNorm (torusPartial (infinityExamplePolynomial c))
      (torusEmbed ![(a : ℂ)⁻¹, 1]) ≤ 1 / a ^ 2 := by
  have ha0 : 0 < a := by linarith
  have hna : ‖(a : ℂ)‖ = a := by simp [abs_of_pos ha0]
  rw [infinityExample_line_gradient, inv_inv, hna]
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · have hden : 0 < 1 + a ^ 4 := by positivity
    rw [div_pow, one_pow, ← pow_mul]
    exact one_div_le_one_div_of_le (show 0 < a ^ (2 * 2) by positivity) (by norm_num)

/-- The explicit sequence is `(1/(n+1),1)`, including both inverse coordinates.-/
theorem infinityExample_asymptotic (c : ℂ) :
    c ∈ asymptoticCriticalValues
      (fun x : affineTorus 2 => ambientEval (infinityExamplePolynomial c) x.val)
      (fun x => ‖x.val‖)
      (fun x => ambientDifferentialNorm (torusPartial (infinityExamplePolynomial c)) x.val) := by
  let a (n : ℕ) : ℝ := (n : ℝ) + 1
  have ha (n : ℕ) : 1 ≤ a n := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have ha0 (n : ℕ) : 0 < a n := lt_of_lt_of_le zero_lt_one (ha n)
  have hz (n : ℕ) : ∀ i : Fin 2, (![((a n : ℝ) : ℂ)⁻¹, 1] i) ≠ 0 := by
    intro i
    fin_cases i
    · simpa using inv_ne_zero (Complex.ofReal_ne_zero.mpr (ha0 n).ne')
    · simp
  let x (n : ℕ) : affineTorus 2 := ⟨torusEmbed ![(a n : ℂ)⁻¹, 1], embed_mem (hz n)⟩
  refine ⟨x, ?_, ?_, ?_⟩
  · have hn : Tendsto a atTop atTop :=
      tendsto_atTop_mono (fun n : ℕ => show (n : ℝ) ≤ a n by dsimp [a]; linarith)
        tendsto_natCast_atTop_atTop
    exact tendsto_atTop_mono (fun n => (infinityExample_inverse_norm (a n) (ha n)).1) hn
  · have hn : Tendsto (fun n => (a n)⁻¹) atTop (𝓝 (0 : ℝ)) := by
      simpa [a, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hn
    have h := tendsto_const_nhds.add hc (a := c)
    simpa [x, infinityExample_line_eval] using h
  · have hn : Tendsto (fun n => 2 / a n) atTop (𝓝 (0 : ℝ)) := by
      have h := tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat (a := (2 : ℝ))
      simpa [a, div_eq_mul_inv] using h
    apply squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) _ hn
    intro n
    have hr := (infinityExample_inverse_norm (a n) (ha n)).2
    have hg := infinityExample_inverse_gradient c (a n) (ha n)
    calc
      _ ≤ (2 * a n) * (1 / a n ^ 2) :=
        mul_le_mul hr hg (Real.sqrt_nonneg _) (by positivity)
      _ = 2 / a n := by field_simp

end
end DuistermaatVanDerKallen

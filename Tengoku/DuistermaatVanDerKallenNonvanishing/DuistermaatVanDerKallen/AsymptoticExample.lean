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

/--
@isnad1 id=eq.0h2v.s10.f0394d1134b1 from=translated src=- shape=110e4196 vocab=69913159
-/
theorem infinityExample_eval (c : ℂ) (x : TorusAmbient 2) :
    ambientEval (infinityExamplePolynomial c) x =
      c + x (.inl 0) + x (.inr 0) * x (.inr 1) * (x (.inl 1) - 1) ^ 2 := by
  simp [infinityExamplePolynomial, ambientEval]

/--
@isnad1 id=eq.0h2v.s10.f2ae76d2ed4c from=translated src=- shape=3bb93be6 vocab=caac971a
-/
theorem infinityExample_partial_zero (c : ℂ) (x : TorusAmbient 2) :
    ambientEval (torusPartial (infinityExamplePolynomial c) 0) x =
      1 - x (.inr 0) ^ 2 * x (.inr 1) * (x (.inl 1) - 1) ^ 2 := by
  simp [torusPartial, infinityExamplePolynomial, ambientEval]
  ring

/-- A direct algebraic certificate excludes critical points in the fiber at `c`.
@isnad1 id=eq.1h2v.s8.78a029065e17 from=translated src=- shape=2cd85219 vocab=dcc3f011
-/
theorem infinityExample_regular_identity (c : ℂ) {x : TorusAmbient 2}
    (hx : x ∈ affineTorus 2) :
    ambientEval (torusPartial (infinityExamplePolynomial c) 0) x +
      x (.inr 0) * (ambientEval (infinityExamplePolynomial c) x - c) = 2 := by
  rw [infinityExample_eval, infinityExample_partial_zero]
  have h := hx 0
  calc
    _ = 1 + x (.inl 0) * x (.inr 0) := by ring
    _ = 2 := by rw [h]; norm_num

/--
@isnad1 id=not.0h1v.s7.ae82e2b55e60 from=translated src=- shape=3635e0b8 vocab=0a64fce0
-/
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

/--
@isnad1 id=eq.0h2v.s5.9967dc47f888 from=translated src=- shape=dade6c35 vocab=9274f4bb
-/
theorem infinityExample_line_eval (c t : ℂ) :
    ambientEval (infinityExamplePolynomial c) (torusEmbed ![t, 1]) = c + t := by
  simp [infinityExample_eval, torusEmbed]

/--
@isnad1 id=eq.0h3v.s6.d5a608a9daf0 from=translated src=- shape=19d2a482 vocab=373b267a
-/
theorem infinityExample_line_partials (c t : ℂ) (i : Fin 2) :
    ambientEval (torusPartial (infinityExamplePolynomial c) i) (torusEmbed ![t, 1]) =
      if i = 0 then 1 else 0 := by
  fin_cases i <;> simp [torusPartial, infinityExamplePolynomial, ambientEval, torusEmbed]

/--
@isnad1 id=eq.0h2v.s6.887deeb7608c from=translated src=- shape=43f4a4ac vocab=baeaa1f3
-/
theorem infinityExample_line_gradient (c t : ℂ) :
    ambientDifferentialNorm (torusPartial (infinityExamplePolynomial c))
      (torusEmbed ![t, 1]) = Real.sqrt (1 / (1 + ‖t⁻¹‖ ^ 4)) := by
  simp only [ambientDifferentialNorm, differentialNormSq, infinityExample_line_partials]
  simp [Fin.sum_univ_two, torusEmbed]

/--
@isnad1 id=eq.0h1v.s7.2075142783dd from=translated src=- shape=855246e7 vocab=1a092750
-/
theorem infinityExample_line_norm (t : ℂ) :
    ‖torusEmbed ![t, 1]‖ ^ 2 = ‖t‖ ^ 2 + ‖t‖⁻¹ ^ 2 + 2 := by
  simp [torusEmbed_norm_sq, Fin.sum_univ_two]
  ring

/--
@isnad1 id=and.1h1v.s8.0eff3fd31d99 from=translated src=- shape=d0968aeb vocab=9d848262
-/
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

/--
@isnad1 id=le.1h2v.s6.3ea36be6f0f6 from=translated src=- shape=fc352504 vocab=c7706268
-/
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

/-- The explicit sequence is `(1/(n+1),1)`, including both inverse coordinates.
@isnad1 id=mem.0h1v.s8.1359b2cf2967 from=translated src=- shape=788439c9 vocab=f2822e31
-/
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

import Tengoku.Piirrationalitymeasure.Formalization.BinomialExpansion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Rationality of the complete Laurent coefficients, including negative indices.
The rational coefficient model is identified with the real normalized
derivative definition, so arithmetic statements can use the same coefficients.
-/

namespace PiIrrationality

/--
@isnad1 id=eq.0h2v.s8.cd05afeade9a from=translated src=- shape=dcfc4ccc vocab=332a2929
-/
theorem iteratedDeriv_rat_aeval (k : ℕ) (P : Polynomial ℚ) :
    iteratedDeriv k (fun t : ℝ => Polynomial.aeval t P) =
      fun t : ℝ => Polynomial.aeval t ((Polynomial.derivative^[k]) P) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      simp only [Polynomial.deriv_aeval, Function.iterate_succ_apply']

/--
@isnad1 id=eq.0h3v.s7.aaffdb5031b6 from=translated src=- shape=949fa583 vocab=67b17894
-/
theorem normalizedDeriv_rat_aeval (k : ℕ) (P : Polynomial ℚ) (x : ℚ) :
    normalizedDeriv k (fun t : ℝ => Polynomial.aeval t P) (x : ℝ) =
      (((Polynomial.derivative^[k]) P).eval x / (k.factorial : ℚ) : ℚ) := by
  unfold normalizedDeriv
  rw [iteratedDeriv_rat_aeval]
  have heval := Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval
    (A := ℝ) x ((Polynomial.derivative^[k]) P)
  change Polynomial.aeval (x : ℝ) ((Polynomial.derivative^[k]) P) =
    ((((Polynomial.derivative^[k]) P).eval x : ℚ) : ℝ) at heval
  dsimp only
  rw [heval]
  push_cast
  rfl

/--
@isnad1 id=ex.0h2v.s6.f5c1c5b3b480 from=translated src=- shape=b42baa10 vocab=ffd216a0
-/
theorem normalizedDeriv_inv_linear_is_rational (M k : ℕ) :
    ∃ q : ℚ, normalizedDeriv k (fun t : ℝ => (5 - t) ^ (-(M : ℤ))) (-5) =
      (q : ℝ) := by
  refine ⟨((-1 : ℚ) ^ k * (∏ i ∈ Finset.range k, (-(M : ℚ) - i)) *
    (10 : ℚ) ^ (-(M : ℤ) - k)) / (k.factorial : ℚ), ?_⟩
  rw [normalized_inv_linear_deriv]
  push_cast
  norm_num

/--
@isnad1 id=ex.0h2v.s4.effe0f037bf8 from=translated src=- shape=8864ae95 vocab=47e67900
-/
theorem laurentCoeff_is_rational (n : ℕ) (j : ℤ) :
    ∃ q : ℚ, laurentCoeff n j = (q : ℝ) := by
  by_cases hj : j ≤ 5570 * (n : ℤ)
  · let K : Subfield ℝ := (algebraMap ℚ ℝ).fieldRange
    have hpoly (P : Polynomial ℚ) (k : ℕ) :
        normalizedDeriv k (fun t : ℝ => Polynomial.aeval t P) (-5) ∈ K := by
      have h := normalizedDeriv_rat_aeval k P (-5)
      norm_num only [Rat.cast_neg, Rat.cast_ofNat] at h
      rw [h]
      exact RingHom.mem_fieldRange_self _ _
    have hinv (M k : ℕ) :
        normalizedDeriv k (fun t : ℝ => (5 - t) ^ (-(M : ℤ))) (-5) ∈ K := by
      obtain ⟨q, hq⟩ := normalizedDeriv_inv_linear_is_rational M k
      rw [hq]
      exact RingHom.mem_fieldRange_self _ _
    have hplus :
        (fun t : ℝ => Polynomial.aeval t
          ((((Polynomial.X : Polynomial ℚ) + 1) ^ 2 + 4) ^ (3714 * n))) =
        (fun t : ℝ => ((t + 1) ^ 2 + 4) ^ (3714 * n)) := by
      funext t
      rw [map_pow, map_add, map_pow, map_add, map_one, Polynomial.aeval_X, map_ofNat]
    have hminus :
        (fun t : ℝ => Polynomial.aeval t
          ((((Polynomial.X : Polynomial ℚ) - 1) ^ 2 + 4) ^ (3714 * n))) =
        (fun t : ℝ => ((t - 1) ^ 2 + 4) ^ (3714 * n)) := by
      funext t
      rw [map_pow, map_add, map_pow, map_sub, map_one, Polynomial.aeval_X, map_ofNat]
    have hcoeff : laurentCoeff n j ∈ K := by
      rw [laurentCoeff_expansion_real_complete n j hj]
      apply K.mul_mem (natCast_mem K 5)
      apply K.sum_mem
      intro i hi
      apply K.sum_mem
      intro j' hj'
      apply K.sum_mem
      intro r hr
      apply K.mul_mem
      · apply K.mul_mem
        · apply K.mul_mem
          · simpa using hpoly ((Polynomial.X : Polynomial ℚ) ^ (2 * 1857 * n)) r
          · rw [← hplus]
            exact hpoly
              ((((Polynomial.X : Polynomial ℚ) + 1) ^ 2 + 4) ^ (3714 * n)) (j' - r)
        · rw [← hminus]
          exact hpoly
            ((((Polynomial.X : Polynomial ℚ) - 1) ^ 2 + 4) ^ (3714 * n)) (i - j')
      · exact hinv (5570 * n + 1) ((5570 * (n : ℤ) - j).toNat - i)
    obtain ⟨q, hq⟩ := RingHom.mem_fieldRange.mp hcoeff
    exact ⟨q, hq.symm⟩
  · exact ⟨0, by simp only [laurentCoeff, ite_eq_right hj, Rat.cast_zero]⟩

noncomputable def laurentCoeffRat (n : ℕ) (j : ℤ) : ℚ :=
  Classical.choose (laurentCoeff_is_rational n j)

/--
@isnad1 id=eq.0h2v.s3.6e07ea1a510b from=translated src=- shape=aafa76bf vocab=ec033e18
-/
theorem laurentCoeffRat_cast (n : ℕ) (j : ℤ) :
    (laurentCoeffRat n j : ℝ) = laurentCoeff n j :=
  (Classical.choose_spec (laurentCoeff_is_rational n j)).symm

end PiIrrationality

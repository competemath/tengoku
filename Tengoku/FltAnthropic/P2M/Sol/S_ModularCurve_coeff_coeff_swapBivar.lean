import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_PhiGen

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_coeff_coeff_swapBivar.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_coeff_coeff_swapBivar

open ModularCurve Polynomial

/--
@isnad1 id=eq.0h2v.s9.233f73fc15a1 from=translated src=- shape=a5e7611f vocab=97823734
-/
theorem swapBivar_monomial (n : ℕ) (c : Polynomial ℤ) :
    swapBivar (Polynomial.monomial n c) = swapInner c * Polynomial.C Polynomial.X ^ n := by
  show (Polynomial.eval₂RingHom swapInner (Polynomial.C Polynomial.X))
      (Polynomial.monomial n c) = _
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]

/--
@isnad1 id=eq.0h2v.s7.a7ee70e9e463 from=translated src=- shape=6c9a6325 vocab=e1560782
-/
theorem coeff_swapInner (c : Polynomial ℤ) (j : ℕ) :
    (swapInner c).coeff j = Polynomial.C (c.coeff j) := by
  show ((Polynomial.aeval (R := ℤ)
      (Polynomial.X : Polynomial (Polynomial ℤ))) c).coeff j = _
  induction c using Polynomial.induction_on' with
  | add a b ha hb => simp only [map_add, Polynomial.coeff_add, ha, hb, map_add]
  | monomial m d =>
      simp only [Polynomial.aeval_monomial, Polynomial.coeff_monomial]
      rw [show (algebraMap ℤ (Polynomial (Polynomial ℤ))) d
          = Polynomial.C (Polynomial.C d) from rfl,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases h : m = j
      · subst h; simp
      · simp [h, Ne.symm h]

/--
@isnad1 id=eq.0h3v.s7.302a0c7bfc7b from=translated src=- shape=f8b7e949 vocab=8592fd60
-/
theorem solution (Φ : Polynomial (Polynomial ℤ)) (i j : ℕ) :
    ((swapBivar Φ).coeff j).coeff i = (Φ.coeff i).coeff j := by
  induction Φ using Polynomial.induction_on' with
  | add f g hf hg =>
      simp only [map_add, Polynomial.coeff_add, hf, hg]
  | monomial n c =>
      rw [swapBivar_monomial, ← Polynomial.C_pow, mul_comm,
        Polynomial.coeff_C_mul, coeff_swapInner,
        mul_comm, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_monomial]
      rcases eq_or_ne n i with rfl | h
      · simp
      · simp [h, Ne.symm h]

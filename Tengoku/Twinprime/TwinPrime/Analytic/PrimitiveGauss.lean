import Tengoku.Seed.Analysis.Fourier.ZMod
import Tengoku.Seed.NumberTheory.DirichletCharacter.Bounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The size of a primitive Gauss sum at every positive modulus

Discrete Fourier inversion applies to `ZMod q` for composite moduli as well
as prime moduli. Evaluating the double transform at `-1` gives the squared
norm of the primitive Gauss sum directly. Modulus one is included.
-/

noncomputable section

open Finset Complex
open scoped ComplexConjugate

namespace TwinPrime.Analytic

/-- Character inversion is complex conjugation, including the zero values
at nonunits.-/
theorem character_inv_apply_eq_conj {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ZMod q) : χ⁻¹ a = conj (χ a) := by
  rw [MulChar.inv_apply_eq_inv']
  by_cases ha : IsUnit a
  · apply Complex.inv_eq_conj
    simpa only [ha.unit_spec] using χ.unit_norm_eq_one ha.unit
  · simp [χ.map_nonunit ha]

/-- The primitive Gauss product identity over an arbitrary positive modulus.
The proof uses Fourier inversion over the finite ring, with no field assumption.-/
theorem primitive_gaussSum_mul_conj {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar * conj (gaussSum χ ZMod.stdAddChar) = (q : ℂ) := by
  have hconj : (∑ j : ZMod q, ZMod.stdAddChar j * χ⁻¹ (-j)) =
      conj (gaussSum χ ZMod.stdAddChar) := by
    calc
      _ = ∑ j : ZMod q, conj (χ (-j) * ZMod.stdAddChar (-j)) := by
        apply sum_congr rfl
        intro j _
        rw [map_mul, character_inv_apply_eq_conj,
          AddChar.map_neg_eq_conj, starRingEnd_self_apply]
        ring
      _ = ∑ j : ZMod q, conj (χ j * ZMod.stdAddChar j) :=
        Fintype.sum_equiv (Equiv.neg (ZMod q)) _ _ (fun _ => rfl)
      _ = _ := by rw [gaussSum, map_sum]
  have hinv := congrFun (ZMod.dft_dft (χ : ZMod q → ℂ)) (-1)
  simp only [neg_neg, map_one, smul_eq_mul, mul_one] at hinv
  have hdouble : ZMod.dft (ZMod.dft (χ : ZMod q → ℂ)) (-1) =
      gaussSum χ ZMod.stdAddChar * conj (gaussSum χ ZMod.stdAddChar) := by
    rw [ZMod.dft_apply]
    simp_rw [hχ.fourierTransform_eq_inv_mul_gaussSum, smul_eq_mul]
    simp only [mul_neg_one, neg_neg]
    calc
      _ = ∑ j : ZMod q,
          (ZMod.stdAddChar j * χ⁻¹ (-j)) * gaussSum χ ZMod.stdAddChar := by
        apply sum_congr rfl
        intro j _
        ring
      _ = (∑ j : ZMod q, ZMod.stdAddChar j * χ⁻¹ (-j)) *
          gaussSum χ ZMod.stdAddChar := by rw [sum_mul]
      _ = _ := by rw [hconj]; ring
  exact hdouble.symm.trans hinv

/-- A primitive Gauss sum has squared norm equal to the modulus, including
the primitive character at modulus one.-/
theorem norm_primitive_gaussSum_sq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (q : ℝ) := by
  have h := primitive_gaussSum_mul_conj χ hχ
  rw [Complex.mul_conj'] at h
  exact_mod_cast h

theorem norm_primitive_gaussSum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt q := by
  rw [← norm_primitive_gaussSum_sq χ hχ, Real.sqrt_sq (norm_nonneg _)]

end TwinPrime.Analytic

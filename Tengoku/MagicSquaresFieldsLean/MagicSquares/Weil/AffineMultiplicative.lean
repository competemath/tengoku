import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.SharpMultiplicative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The sharp bound for distinct roots transfers to nonconstant affine
forms with positive exponents.-/
theorem HasSplitPowerMultiplicativeWeilBound.affine
    (hWeil : HasSplitPowerMultiplicativeWeilBound F)
    {ι : Type*} [Fintype ι] (coeff : ι → F) (exponents : ι → ℕ)
    (hpos : 0 < Fintype.card ι) (hinj : Function.Injective coeff)
    (hcoeff : ∀ i, coeff i ≠ 0) (hexp : ∀ i, 0 < exponents i)
    (chi : MulChar F ℂ) (hchi : chi ≠ 1)
    (hnon : ∃ i, ¬ orderOf chi ∣ exponents i) :
    ‖∑ t : F, chi (∏ i, (1 + coeff i * t) ^ exponents i)‖ ≤
      (Fintype.card ι - 1 : ℕ) * Real.sqrt (Fintype.card F : ℝ) := by
  let e := (Fintype.equivFin ι).symm
  have hrootinj : Function.Injective (fun i : Fin (Fintype.card ι) => -(coeff (e i))⁻¹) := by
    intro i j hij
    apply e.injective
    apply hinj
    simpa using hij
  have h := hWeil (Fintype.card ι) (fun i => -(coeff (e i))⁻¹)
    (fun i => exponents (e i)) hpos hrootinj (fun i => hexp (e i)) chi hchi
    (by obtain ⟨i, hi⟩ := hnon; exact ⟨e.symm i, by simpa using hi⟩)
  have hprod (t : F) :
      (∏ i : Fin (Fintype.card ι), (t - -(coeff (e i))⁻¹) ^ exponents (e i)) =
        ∏ i : ι, (t - -(coeff i)⁻¹) ^ exponents i :=
    e.prod_comp (fun i : ι => (t - -(coeff i)⁻¹) ^ exponents i)
  simp_rw [hprod] at h
  have hfactor (t : F) :
      chi (∏ i, (1 + coeff i * t) ^ exponents i) =
        chi (∏ i, coeff i ^ exponents i) *
          chi (∏ i, (t - -(coeff i)⁻¹) ^ exponents i) := by
    rw [← map_mul, ← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [← mul_pow]
    congr 1
    simp [sub_neg_eq_add, mul_add, mul_inv_cancel₀ (hcoeff i), add_comm]
  simp_rw [hfactor]
  rw [← Finset.mul_sum, norm_mul]
  calc
    _ ≤ 1 * ‖∑ t : F, chi (∏ i, (t - -(coeff i)⁻¹) ^ exponents i)‖ :=
      mul_le_mul_of_nonneg_right (LN97.mulChar_norm_le_one _ _) (norm_nonneg _)
    _ ≤ _ := by simpa using h

end MagicSquares

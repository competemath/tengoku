import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SemialgebraicSets
import Tengoku.Seed.Analysis.Complex.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-! Real polynomial descriptions of complex polynomial equations and norm bounds. -/

namespace DuistermaatVanDerKallen
noncomputable section

def complexCoordinates {ι : Type*} (x : (ι ⊕ ι) → ℝ) (i : ι) : ℂ :=
  ⟨x (.inl i), x (.inr i)⟩

theorem polynomial_real_parts {ι : Type*} (u : MvPolynomial ι ℂ) :
    ∃ p q : MvPolynomial (ι ⊕ ι) ℝ, ∀ x : (ι ⊕ ι) → ℝ,
      (MvPolynomial.eval (complexCoordinates x) u).re = MvPolynomial.eval x p ∧
      (MvPolynomial.eval (complexCoordinates x) u).im = MvPolynomial.eval x q := by
  induction u using MvPolynomial.induction_on with
  | C c => exact ⟨MvPolynomial.C c.re, MvPolynomial.C c.im, fun x => by simp⟩
  | add u v hu hv =>
    obtain ⟨p, q, hpq⟩ := hu
    obtain ⟨r, s, hrs⟩ := hv
    refine ⟨p + r, q + s, fun x => ?_⟩
    simp [(hpq x).1, (hpq x).2, (hrs x).1, (hrs x).2]
  | mul_X u i hu =>
    obtain ⟨p, q, hpq⟩ := hu
    refine ⟨p * MvPolynomial.X (.inl i) - q * MvPolynomial.X (.inr i),
      p * MvPolynomial.X (.inr i) + q * MvPolynomial.X (.inl i), fun x => ?_⟩
    simp [Complex.mul_re, Complex.mul_im, complexCoordinates, (hpq x).1, (hpq x).2]

theorem complexCoordinates_norm_le {ι : Type*} (x : (ι ⊕ ι) → ℝ) (i : ι) (ε : ℝ) (hε : 0 ≤ ε) :
    ‖complexCoordinates x i‖ ≤ ε ↔ x (.inl i) ^ 2 + x (.inr i) ^ 2 ≤ ε ^ 2 := by
  rw [← sq_le_sq₀ (norm_nonneg _) hε, Complex.sq_norm]
  simp [Complex.normSq_apply, complexCoordinates, pow_two]

theorem complexCoordinates_norm_eq {ι : Type*} (x : (ι ⊕ ι) → ℝ) (i : ι) (ε : ℝ) (hε : 0 ≤ ε) :
    ‖complexCoordinates x i‖ = ε ↔ x (.inl i) ^ 2 + x (.inr i) ^ 2 = ε ^ 2 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) hε, Complex.sq_norm]
  simp [Complex.normSq_apply, complexCoordinates, pow_two]

theorem polynomial_root_locus_real_description {ι : Type*} (u : MvPolynomial ι ℂ) (ε : ℝ) (hε : 0 ≤ ε) (i : ι) :
    ∃ p q : MvPolynomial (ι ⊕ ι) ℝ, ∀ x : (ι ⊕ ι) → ℝ,
      ((∀ j, ‖complexCoordinates x j‖ ≤ ε) ∧
        (∀ j, j ≠ i → ‖complexCoordinates x j‖ = ε) ∧
        MvPolynomial.eval (complexCoordinates x) u = 0) ↔
      ((∀ j, x (.inl j) ^ 2 + x (.inr j) ^ 2 ≤ ε ^ 2) ∧
        (∀ j, j ≠ i → x (.inl j) ^ 2 + x (.inr j) ^ 2 = ε ^ 2) ∧
        MvPolynomial.eval x p = 0 ∧ MvPolynomial.eval x q = 0) := by
  obtain ⟨p, q, hpq⟩ := polynomial_real_parts u
  refine ⟨p, q, fun x => ?_⟩
  simp_rw [complexCoordinates_norm_le x _ ε hε, complexCoordinates_norm_eq x _ ε hε,
    Complex.ext_iff, (hpq x).1, (hpq x).2]
  simp

end
end DuistermaatVanDerKallen

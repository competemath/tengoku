import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.ComplexSemialgebraic
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SemialgebraicRational
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SphereFamily

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Polynomial sign descriptions of the actual affine torus, its induced
Euclidean spheres, and its restricted differential norm. -/

namespace DuistermaatVanDerKallen
noncomputable section

/--
@isnad1 id=ex.0h2v.s7.5cc78497da90 from=translated src=- shape=ace60909 vocab=8d39eb50
-/
theorem polynomial_normSq_real {ι : Type*} (p : MvPolynomial ι ℂ) :
    ∃ q : MvPolynomial (ι ⊕ ι) ℝ, ∀ x,
      Complex.normSq (MvPolynomial.eval (complexCoordinates x) p) = MvPolynomial.eval x q := by
  obtain ⟨r, s, hrs⟩ := polynomial_real_parts p
  refine ⟨r ^ 2 + s ^ 2, fun x => ?_⟩
  simp [Complex.normSq_apply, (hrs x).1, (hrs x).2, pow_two]

/--
@isnad1 id=iscomple.0h1v.s6.af01db57044a from=translated src=- shape=dd14031a vocab=5bef18c1
-/
theorem isComplexSemialgebraic_affineTorus (d : ℕ) :
    IsComplexSemialgebraic {x : (Fin d ⊕ Fin d) → ℂ |
      WithLp.toLp 2 x ∈ affineTorus d} := by
  have h (i : Fin d) : IsComplexSemialgebraic
      {x : (Fin d ⊕ Fin d) → ℂ | x (.inl i) * x (.inr i) = 1} := by
    have hz := IsComplexSemialgebraic.polynomial_zeroSet
      (MvPolynomial.X (.inl i) * MvPolynomial.X (.inr i) - 1 :
        MvPolynomial (Fin d ⊕ Fin d) ℂ)
    simpa [sub_eq_zero] using hz
  exact IsComplexSemialgebraic.forall_finite
    (fun i : Fin d => {x : (Fin d ⊕ Fin d) → ℂ | x (.inl i) * x (.inr i) = 1}) h

/--
@isnad1 id=iscomple.1h3v.s6.5e2c532e8054 from=translated src=- shape=f7b6cfb2 vocab=974d9ac0
-/
theorem isComplexSemialgebraic_ambientDifferentialNorm_le {d : ℕ}
    (g : Fin d → AmbientPolynomial d) {ε : ℝ} (hε : 0 ≤ ε) :
    IsComplexSemialgebraic {x : (Fin d ⊕ Fin d) → ℂ |
      ambientDifferentialNorm g (WithLp.toLp 2 x) ≤ ε} := by
  choose a ha using fun i => polynomial_normSq_real (g i)
  choose b hb using fun i : Fin d => polynomial_normSq_real
    (MvPolynomial.X (.inr i) : AmbientPolynomial d)
  let B (i : Fin d) := 1 + b i ^ 2
  have hB (x : ((Fin d ⊕ Fin d) ⊕ (Fin d ⊕ Fin d)) → ℝ) (i : Fin d) :
      MvPolynomial.eval x (B i) =
        1 + ‖complexCoordinates x (.inr i)‖ ^ 4 := by
    simp only [B, map_add, map_one, map_pow, ← hb i x, MvPolynomial.eval_X]
    rw [← Complex.sq_norm, ← pow_mul]
  have hpos : ∀ x i, 0 < MvPolynomial.eval x (B i) := by
    intro x i
    rw [hB]
    positivity
  have h := IsSemialgebraic.sum_div_le a B (MvPolynomial.C (ε ^ 2)) hpos
  unfold IsComplexSemialgebraic
  convert h using 1
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, MvPolynomial.eval_C]
  have hnn : 0 ≤ differentialNormSq
      (fun i => ambientEval (g i) (WithLp.toLp 2 (complexCoordinates x)))
      (fun i => 1 + ‖complexCoordinates x (.inr i)‖ ^ 4) := by
    apply differentialNormSq_nonneg
    intro i
    positivity
  rw [ambientDifferentialNorm, ← sq_le_sq₀ (Real.sqrt_nonneg _) hε, Real.sq_sqrt hnn]
  simp only [differentialNormSq, ambientEval, ha, hB]

/--
@isnad1 id=iscomple.1h2v.s6.570b8b4ee5df from=translated src=- shape=3954b995 vocab=fffa5ea0
-/
theorem isComplexSemialgebraic_euclidean_sphere {ι : Type*} [Fintype ι]
    {R : ℝ} (hR : 0 ≤ R) :
    IsComplexSemialgebraic {x : ι → ℂ | ‖WithLp.toLp 2 x‖ = R} := by
  classical
  choose a ha using fun i : ι => polynomial_normSq_real
    (MvPolynomial.X i : MvPolynomial ι ℂ)
  have h := IsSemialgebraic.eq (∑ i, a i) (MvPolynomial.C (R ^ 2))
  unfold IsComplexSemialgebraic
  convert h using 1
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, map_sum, MvPolynomial.eval_C]
  rw [← sq_eq_sq₀ (norm_nonneg _) hR, EuclideanSpace.norm_sq_eq]
  simp only [Complex.sq_norm, ← ha, MvPolynomial.eval_X]

end
end DuistermaatVanDerKallen

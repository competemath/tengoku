import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.AffineSemialgebraic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Polynomial-coordinate descriptions retain all free real parameters. -/

namespace DuistermaatVanDerKallen
noncomputable section

/--
@isnad1 id=eq.0h5v.s8.db0ccde22781 from=translated src=- shape=2e423cc0 vocab=b6359ce9
-/
theorem eval_real_substitution {ι κ : Type*} (p : MvPolynomial ι ℝ)
    (Z : ι → MvPolynomial κ ℝ) (x : κ → ℝ) :
    MvPolynomial.eval x (MvPolynomial.eval₂ MvPolynomial.C Z p) =
      MvPolynomial.eval (fun i => MvPolynomial.eval x (Z i)) p := by
  have hc : (MvPolynomial.eval x).comp (MvPolynomial.C : ℝ →+* MvPolynomial κ ℝ) = RingHom.id ℝ := by
    ext a
    simp
  simp [MvPolynomial.eval_eval₂, hc]

/--
@isnad1 id=ex.0h4v.s8.fb91ff2a877f from=translated src=- shape=20f0b5bb vocab=8d39eb50
-/
theorem polynomial_normSq_real_substitution {ι κ : Type*}
    (p : MvPolynomial ι ℂ) (Z : (ι ⊕ ι) → MvPolynomial κ ℝ) :
    ∃ q : MvPolynomial κ ℝ, ∀ x,
      Complex.normSq (MvPolynomial.eval (complexCoordinates (fun i => MvPolynomial.eval x (Z i))) p) =
        MvPolynomial.eval x q := by
  obtain ⟨q, hq⟩ := polynomial_normSq_real p
  exact ⟨MvPolynomial.eval₂ MvPolynomial.C Z q, fun x => by rw [eval_real_substitution, hq]⟩

/-- Squaring and clearing denominators handles a variable weight and threshold.
Nonnegative weights and thresholds are included as polynomial sign constraints.
@isnad1 id=issemial.0h6v.s8.f37b06f9bfc4 from=translated src=- shape=8aa20779 vocab=f699e1a1
-/
theorem isSemialgebraic_weighted_differential_bound {d : ℕ} {κ : Type*}
    (g : Fin d → AmbientPolynomial d)
    (Z : ((Fin d ⊕ Fin d) ⊕ (Fin d ⊕ Fin d)) → MvPolynomial κ ℝ)
    (r e : MvPolynomial κ ℝ) :
    IsSemialgebraic κ {x | 0 ≤ MvPolynomial.eval x r ∧ 0 ≤ MvPolynomial.eval x e ∧
      MvPolynomial.eval x r * ambientDifferentialNorm g
        (WithLp.toLp 2 (complexCoordinates (fun i => MvPolynomial.eval x (Z i)))) ≤
          MvPolynomial.eval x e} := by
  choose a ha using fun i => polynomial_normSq_real_substitution (g i) Z
  choose b hb using fun i : Fin d => polynomial_normSq_real_substitution
    (MvPolynomial.X (.inr i) : AmbientPolynomial d) Z
  let B (i : Fin d) := 1 + b i ^ 2
  have hB (x : κ → ℝ) (i : Fin d) : MvPolynomial.eval x (B i) =
      1 + ‖complexCoordinates (fun j => MvPolynomial.eval x (Z j)) (.inr i)‖ ^ 4 := by
    simp only [B, map_add, map_one, map_pow, ← hb i x, MvPolynomial.eval_X]
    rw [← Complex.sq_norm, ← pow_mul]
  have hpos : ∀ x i, 0 < MvPolynomial.eval x (B i) := by
    intro x i
    rw [hB]
    positivity
  have h := (IsSemialgebraic.nonneg r).inter ((IsSemialgebraic.nonneg e).inter
    (IsSemialgebraic.sum_div_le (fun i => r ^ 2 * a i) B (e ^ 2) hpos))
  convert h using 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, map_pow, map_mul]
  apply and_congr_right
  intro hr
  apply and_congr_right
  intro he
  have hnn : 0 ≤ differentialNormSq
      (fun i => ambientEval (g i) (WithLp.toLp 2 (complexCoordinates (fun j => MvPolynomial.eval x (Z j)))))
      (fun i => 1 + ‖complexCoordinates (fun j => MvPolynomial.eval x (Z j)) (.inr i)‖ ^ 4) := by
    apply differentialNormSq_nonneg
    intro i
    positivity
  rw [ambientDifferentialNorm, ← sq_le_sq₀ (mul_nonneg hr (Real.sqrt_nonneg _)) he,
    mul_pow, Real.sq_sqrt hnn]
  simp only [differentialNormSq, ambientEval, ha, hB, Finset.mul_sum, mul_div_assoc]

/-- The norm is the L2 norm of all complex coordinates.
@isnad1 id=issemial.0h4v.s8.580d2e9aaa1b from=translated src=- shape=3fd830d6 vocab=b703d2cf
-/
theorem isSemialgebraic_euclidean_norm_eq {ι κ : Type*} [Fintype ι]
    (Z : (ι ⊕ ι) → MvPolynomial κ ℝ) (r : MvPolynomial κ ℝ) :
    IsSemialgebraic κ {x | 0 ≤ MvPolynomial.eval x r ∧
      ‖WithLp.toLp 2 (complexCoordinates (fun i => MvPolynomial.eval x (Z i)))‖ =
        MvPolynomial.eval x r} := by
  classical
  choose a ha using fun i : ι => polynomial_normSq_real_substitution
    (MvPolynomial.X i : MvPolynomial ι ℂ) Z
  have h := (IsSemialgebraic.nonneg r).inter (IsSemialgebraic.eq (∑ i, a i) (r ^ 2))
  convert h using 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, map_sum, map_pow]
  apply and_congr_right
  intro hr
  rw [← sq_eq_sq₀ (norm_nonneg _) hr, EuclideanSpace.norm_sq_eq]
  simp only [Complex.sq_norm, ← ha, MvPolynomial.eval_X]

/--
@isnad1 id=issemial.0h6v.s8.995113648d5d from=translated src=- shape=5f6ca328 vocab=9ec1e0ef
-/
theorem isSemialgebraic_polynomial_dist_lt {ι κ : Type*}
    (p : MvPolynomial ι ℂ) (Z : (ι ⊕ ι) → MvPolynomial κ ℝ)
    (c : ℂ) (e : MvPolynomial κ ℝ) :
    IsSemialgebraic κ {x | 0 ≤ MvPolynomial.eval x e ∧
      dist (MvPolynomial.eval (complexCoordinates (fun i => MvPolynomial.eval x (Z i))) p) c <
        MvPolynomial.eval x e} := by
  obtain ⟨a, ha⟩ := polynomial_normSq_real_substitution (p - MvPolynomial.C c) Z
  have h := (IsSemialgebraic.nonneg e).inter (IsSemialgebraic.lt a (e ^ 2))
  convert h using 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, map_pow]
  apply and_congr_right
  intro he
  rw [dist_eq_norm, ← sq_lt_sq₀ (norm_nonneg _) he, Complex.sq_norm]
  simp only [map_sub, MvPolynomial.eval_C] at ha
  rw [ha]

end
end DuistermaatVanDerKallen

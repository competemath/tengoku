import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.NormalizedGradient
import Tengoku.Seed.Algebra.MvPolynomial.PDeriv
import Tengoku.Seed.Analysis.Calculus.FDeriv.Mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Polynomial representatives and their actual torus-coordinate partials.
Negative powers are represented by the inverse coordinates in the closed model.
The induced derivative uses both ambient halves through the chart chain rule. -/

open scoped BigOperators

namespace DuistermaatVanDerKallen

noncomputable section

/-- The ordinary ambient derivative of a polynomial, before restriction.-/
def polynomialDifferential {d : ℕ} (p : AmbientPolynomial d) (x : TorusAmbient d) :
    TorusAmbient d →L[ℂ] ℂ :=
  ∑ j : Fin d ⊕ Fin d,
    ambientEval (MvPolynomial.pderiv j p) x • PiLp.proj (𝕜 := ℂ) 2 _ j

@[simp] theorem polynomialDifferential_apply {d : ℕ} (p : AmbientPolynomial d)
    (x v : TorusAmbient d) :
    polynomialDifferential p x v =
      ∑ j, ambientEval (MvPolynomial.pderiv j p) x * v j := by
  simp [polynomialDifferential, smul_eq_mul]

/-- Every polynomial representative is real smooth on the entire ambient space.-/
theorem ambientEval_contDiff_real {d : ℕ} (p : AmbientPolynomial d) :
    ContDiff ℝ ⊤ (ambientEval p) := by
  change ContDiff ℝ ⊤ (fun x : TorusAmbient d => MvPolynomial.eval x p)
  induction p using MvPolynomial.induction_on with
  | C c => simpa using (contDiff_const (c := c) (𝕜 := ℝ) (E := TorusAmbient d))
  | add p q hp hq => simpa [ambientEval] using hp.add hq
  | mul_X p j hp =>
    have hj : ContDiff ℝ ⊤ (fun x : TorusAmbient d => x j) := by fun_prop
    simpa [ambientEval] using hp.mul hj

/-- Polynomial representative of the true partial derivative with respect to zᵢ
on the torus: `P_zᵢ − wᵢ² P_wᵢ`, not merely `P_zᵢ`.-/
def torusPartial {d : ℕ} (p : AmbientPolynomial d) (i : Fin d) : AmbientPolynomial d :=
  MvPolynomial.pderiv (.inl i) p -
    MvPolynomial.X (.inr i) ^ 2 * MvPolynomial.pderiv (.inr i) p

/-- Pullback of the ambient derivative through the proper embedding.-/
theorem polynomialDifferential_comp_torusTangentMap {d : ℕ}
    (p : AmbientPolynomial d) (z : Fin d → ℂ) :
    (polynomialDifferential p (torusEmbed z)).comp (torusTangentMap z) =
      coordinateDifferential (fun i => ambientEval (torusPartial p i) (torusEmbed z)) := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, polynomialDifferential_apply,
    Fintype.sum_sum_type, ← Finset.sum_add_distrib, coordinateDifferential_apply,
    torusTangentMap_left, torusTangentMap_right]
  apply Finset.sum_congr rfl
  intro i _
  simp [torusPartial, ambientEval, torusEmbed]
  ring

/-- Regression for extension dependence: a defining relation of the affine torus
has zero coordinate derivative on the torus, despite its nonzero ambient partials.-/
theorem torusPartial_constraint_eval {d : ℕ} (i j : Fin d)
    {z : Fin d → ℂ} (hz : ∀ k, z k ≠ 0) :
    ambientEval (torusPartial
      (MvPolynomial.X (.inl i) * MvPolynomial.X (.inr i) - 1) j) (torusEmbed z) = 0 := by
  classical
  by_cases h : i = j
  · subst j
    simp [torusPartial, ambientEval, torusEmbed]
    field_simp [hz i]
    ring
  · simp [torusPartial, ambientEval, torusEmbed, h]

/-- Regression for the induced metric: at the unit point in rank one the
coordinate differential has squared norm `1/2`, because inverse coordinates
contribute to the metric.-/
theorem restrictedDifferential_unit_rank_one :
    ‖restrictedDifferential (fun _ : Fin 1 => (1 : ℂ)) (fun _ => (1 : ℂ))‖ ^ 2 =
      (1 / 2 : ℝ) := by
  rw [restrictedDifferential_norm_sq]
  norm_num [differentialNormSq, torusWeight]

end
end DuistermaatVanDerKallen

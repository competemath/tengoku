import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.PolynomialCalculus
import Tengoku.Seed.Analysis.InnerProductSpace.Calculus
import Tengoku.Seed.Analysis.ODE.ExistUnique

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Smoothness and exact differential identities of the manuscript's explicit
normalized-gradient field for polynomial representatives on the affine torus.
Smoothness is real and joint in the base velocity and torus coordinates. -/

open scoped BigOperators ComplexConjugate Topology

namespace DuistermaatVanDerKallen

noncomputable section

/-- True coordinate partials of the Laurent restriction of an ambient polynomial.-/
def polynomialTorusGradient {d : ℕ} (p : AmbientPolynomial d) (z : Fin d → ℂ) : Fin d → ℂ :=
  fun i => ambientEval (torusPartial p i) (torusEmbed z)

/-- Squared restricted operator norm in torus coordinates.-/
def polynomialTorusNormSq {d : ℕ} (p : AmbientPolynomial d) (z : Fin d → ℂ) : ℝ :=
  differentialNormSq (polynomialTorusGradient p z) (torusWeight z)

/-- The manuscript vector field `V_a`, expressed in the original torus coordinates.-/
def polynomialVectorField {d : ℕ} (p : AmbientPolynomial d) (a : ℂ)
    (z : Fin d → ℂ) : Fin d → ℂ :=
  scalarLift (polynomialTorusGradient p z) (torusWeight z) a

/-- The chart metric coefficients are real smooth away from coordinate collapse.
@isnad1 id=contdiff.1h3v.s6.a3649b5057b8 from=translated src=- shape=e428144d vocab=fdeafda5
-/
theorem torusWeight_contDiffAt {d : ℕ} {z : Fin d → ℂ} (hz : ∀ i, z i ≠ 0)
    (i : Fin d) : ContDiffAt ℝ ⊤ (fun y => torusWeight y i) z := by
  exact contDiffAt_const.add ((((contDiffAt_apply ℝ ℂ i z).norm ℂ (hz i)).inv
    (norm_ne_zero_iff.mpr (hz i))).pow 4)

/--
@isnad1 id=contdiff.1h4v.s6.1318db0be88f from=translated src=- shape=7ccc6fb8 vocab=13f861f7
-/
theorem polynomialTorusGradient_contDiffAt {d : ℕ} (p : AmbientPolynomial d)
    {z : Fin d → ℂ} (hz : ∀ i, z i ≠ 0) (i : Fin d) :
    ContDiffAt ℝ ⊤ (fun y => polynomialTorusGradient p y i) z :=
  (ambientEval_contDiff_real (torusPartial p i)).contDiffAt.comp z
    (torusEmbed_contDiffAt_real hz)

/-- Smoothness uses the squared norm, so no square-root differentiability is needed.
@isnad1 id=contdiff.1h3v.s6.d4c971ad6074 from=translated src=- shape=f61061a1 vocab=9e1ed6ca
-/
theorem polynomialTorusNormSq_contDiffAt {d : ℕ} (p : AmbientPolynomial d)
    {z : Fin d → ℂ} (hz : ∀ i, z i ≠ 0) :
    ContDiffAt ℝ ⊤ (polynomialTorusNormSq p) z := by
  unfold polynomialTorusNormSq differentialNormSq
  apply ContDiffAt.sum
  intro i _
  have hg : ContDiffAt ℝ ⊤ (fun y => Complex.normSq (polynomialTorusGradient p y i)) z := by
    simpa only [Complex.normSq_eq_norm_sq] using
      (polynomialTorusGradient_contDiffAt p hz i).norm_sq ℂ
  exact hg.div (torusWeight_contDiffAt hz i) (ne_of_gt (torusWeight_pos z i))

/-- The actual real ODE domain in the open torus.-/
def polynomialRegularDomain {d : ℕ} (p : AmbientPolynomial d) : Set (Fin d → ℂ) :=
  {z | (∀ i, z i ≠ 0) ∧ polynomialTorusNormSq p z ≠ 0}

/--
@isnad1 id=isopen.0h2v.s5.1ded9f608a77 from=translated src=- shape=6b40eb30 vocab=bd6e6399
-/
theorem polynomialRegularDomain_isOpen {d : ℕ} (p : AmbientPolynomial d) :
    IsOpen (polynomialRegularDomain p) := by
  have hc : ContinuousOn (polynomialTorusNormSq p) {z | ∀ i, z i ≠ 0} :=
    fun _ hz => (polynomialTorusNormSq_contDiffAt p hz).continuousAt.continuousWithinAt
  exact hc.isOpen_inter_preimage (torusDomain_isOpen d) (isOpen_ne_fun continuous_id continuous_const)

/-- Joint smoothness in velocity and position, on the regular domain.
@isnad1 id=contdiff.1h4v.s7.2c988b348dde from=translated src=- shape=9b2cc065 vocab=92414102
-/
theorem polynomialVectorField_contDiffAt {d : ℕ} (p : AmbientPolynomial d)
    {a : ℂ} {z : Fin d → ℂ} (hz : z ∈ polynomialRegularDomain p) :
    ContDiffAt ℝ ⊤ (fun az : ℂ × (Fin d → ℂ) => polynomialVectorField p az.1 az.2)
      (a, z) := by
  apply contDiffAt_pi.2
  intro i
  have hg : ContDiffAt ℝ ⊤ (fun az : ℂ × (Fin d → ℂ) =>
      conj (polynomialTorusGradient p az.2 i)) (a, z) :=
    Complex.conjCLE.contDiff.contDiffAt.comp _
      ((polynomialTorusGradient_contDiffAt p hz.1 i).comp (a, z) (f := Prod.snd) contDiffAt_snd)
  have hh : ContDiffAt ℝ ⊤ (fun az : ℂ × (Fin d → ℂ) => (torusWeight az.2 i : ℂ)) (a, z) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _
      ((torusWeight_contDiffAt hz.1 i).comp (a, z) (f := Prod.snd) contDiffAt_snd)
  have hn : ContDiffAt ℝ ⊤ (fun az : ℂ × (Fin d → ℂ) =>
      (polynomialTorusNormSq p az.2 : ℂ)) (a, z) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _
      ((polynomialTorusNormSq_contDiffAt p hz.1).comp (a, z) (f := Prod.snd) contDiffAt_snd)
  change ContDiffAt ℝ ⊤ (fun az : ℂ × (Fin d → ℂ) =>
    az.1 * conj (polynomialTorusGradient p az.2 i) /
      ((torusWeight az.2 i : ℂ) * (polynomialTorusNormSq p az.2 : ℂ))) (a, z)
  simpa only [div_eq_mul_inv] using (contDiffAt_fst.mul hg).mul ((hh.mul hn).fun_inv
    (mul_ne_zero (by exact_mod_cast (ne_of_gt (torusWeight_pos z i)))
      (by exact_mod_cast hz.2)))

/-- Exact speed of the embedded vector field, measured with the proper metric.
@isnad1 id=eq.1h4v.s9.eafc567c3d21 from=translated src=- shape=ff5f8f23 vocab=8e6e7e89
-/
theorem polynomialVectorField_embedded_norm {d : ℕ} (p : AmbientPolynomial d) (a : ℂ)
    {z : Fin d → ℂ} (hz : z ∈ polynomialRegularDomain p) :
    ‖torusTangentMap z (polynomialVectorField p a z)‖ =
      ‖a‖ / ambientDifferentialNorm (torusPartial p) (torusEmbed z) := by
  rw [ambientDifferentialNorm_eq_restricted]
  exact normalizedTangentLift_norm z (polynomialTorusGradient p z) a hz.2

/-- Fixed-velocity vector field is smooth at every regular torus point.
@isnad1 id=contdiff.1h4v.s7.dc3571d62f3b from=translated src=- shape=f0db3a4b vocab=40c3d572
-/
theorem polynomialVectorField_contDiffAt_position {d : ℕ} (p : AmbientPolynomial d)
    (a : ℂ) {z : Fin d → ℂ} (hz : z ∈ polynomialRegularDomain p) :
    ContDiffAt ℝ ⊤ (polynomialVectorField p a) z :=
  (polynomialVectorField_contDiffAt p (a := a) hz).comp z
    (f := fun y => (a, y)) (contDiffAt_const.prodMk contDiffAt_id)

end
end DuistermaatVanDerKallen

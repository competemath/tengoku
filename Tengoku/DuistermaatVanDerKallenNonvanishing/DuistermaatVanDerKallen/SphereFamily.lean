import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SemialgebraicObligations
import Tengoku.Seed.Topology.Algebra.MvPolynomial
import Tengoku.Seed.Tactic.FunProp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Unconditional topological checks on the specialized small-gradient family.
Compactness does not supply a uniform number of components or path length. -/

namespace DuistermaatVanDerKallen

/--
@isnad1 id=continuo.0h2v.s6.edd9d3f3e271 from=translated src=- shape=cc4c7d09 vocab=50b423dc
-/
theorem ambientEval_continuous {d : ℕ} (p : AmbientPolynomial d) :
    Continuous (ambientEval p) :=
  p.continuous_eval.comp (continuous_pi fun i => PiLp.continuous_apply _ _ i)

/--
@isnad1 id=continuo.0h2v.s6.40253be301b6 from=translated src=- shape=e0923840 vocab=3fe525e2
-/
theorem ambientDifferentialNorm_continuous {d : ℕ}
    (g : Fin d → AmbientPolynomial d) : Continuous (ambientDifferentialNorm g) := by
  unfold ambientDifferentialNorm differentialNormSq
  apply Continuous.sqrt
  apply continuous_finsetSum
  intro i _
  apply Continuous.div
  · exact Complex.continuous_normSq.comp (ambientEval_continuous _)
  · fun_prop
  · intro x
    have : 0 < (1 : ℝ) + ‖x (Sum.inr i)‖ ^ 4 := by positivity
    exact ne_of_gt this

/--
@isnad1 id=isclosed.0h4v.s6.be2afb1ecd89 from=translated src=- shape=283a4b70 vocab=88c5b534
-/
theorem smallGradientSphere_isClosed {d : ℕ}
    (g : Fin d → AmbientPolynomial d) (R ε : ℝ) :
    IsClosed (smallGradientSphere g R ε) := by
  have hscale : Continuous (fun u : TorusAmbient d => R • u) := by fun_prop
  exact (isClosed_eq continuous_norm continuous_const).inter
    (((affineTorus_isClosed d).preimage hscale).inter
      (isClosed_le (continuous_const.mul ((ambientDifferentialNorm_continuous g).comp hscale))
        continuous_const))

/-- Compactness holds for every real pair of parameters, not merely positive ones.
@isnad1 id=iscompac.0h4v.s6.a2f17a50447b from=translated src=- shape=283a4b70 vocab=9ce0fd13
-/
theorem smallGradientSphere_isCompact {d : ℕ}
    (g : Fin d → AmbientPolynomial d) (R ε : ℝ) :
    IsCompact (smallGradientSphere g R ε) := by
  apply (isCompact_closedBall (0 : TorusAmbient d) 1).of_isClosed_subset
    (smallGradientSphere_isClosed g R ε)
  intro x hx
  simp [Metric.mem_closedBall, hx.1]

end DuistermaatVanDerKallen

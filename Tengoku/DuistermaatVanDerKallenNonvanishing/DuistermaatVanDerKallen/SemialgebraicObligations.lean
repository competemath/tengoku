import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.AffineTorus
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.ScalarLift
import Tengoku.Seed.Algebra.MvPolynomial.Eval
import Tengoku.Seed.Topology.Connected.Basic
import Tengoku.Seed.Topology.EMetricSpace.BoundedVariation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! UNPROVED geometric obligations, represented solely as propositions.
No theorem in this module establishes a projection or path bound. The polynomial
family is an explicit specialization of the manuscript's small-gradient spheres:
polynomial restrictions represent Laurent polynomials and their partials on the
closed affine torus. Independent polynomial `g` makes the required geometric
statement a little more general; it adds no hypothesis on the desired partials.
-/

open Set

namespace DuistermaatVanDerKallen

abbrev AmbientPolynomial (d : ℕ) := MvPolynomial (Fin d ⊕ Fin d) ℂ

noncomputable def ambientEval {d : ℕ} (p : AmbientPolynomial d)
    (x : TorusAmbient d) : ℂ := MvPolynomial.eval x p

noncomputable def ambientDifferentialNorm {d : ℕ} (g : Fin d → AmbientPolynomial d)
    (x : TorusAmbient d) : ℝ :=
  Real.sqrt (differentialNormSq (fun i => ambientEval (g i) x)
    (fun i => 1 + ‖x (.inr i)‖ ^ 4))

/-- The exact radius set in the common-radius step, with thresholds as parameters.-/
def radiusApproximationSet {d : ℕ} (p : AmbientPolynomial d)
    (g : Fin d → AmbientPolynomial d) (c : ℂ) (ε δ : ℝ) : Set ℝ :=
  {R | 1 < R ∧ ∃ x ∈ affineTorus d, ‖x‖ = R ∧
    R * ambientDifferentialNorm g x ≤ ε ∧ dist (ambientEval p x) c < δ}

/-- OPEN: a specialized projection-to-one-variable tail theorem.-/
def RadiusTailObligation : Prop :=
  ∀ d (p : AmbientPolynomial d) (g : Fin d → AmbientPolynomial d)
    (c : ℂ) (ε δ : ℝ), 0 < ε → 0 < δ →
    (∀ B : ℝ, ∃ R ∈ radiusApproximationSet p g c ε δ, B ≤ R) →
    ∃ B : ℝ, ∀ R, B ≤ R → R ∈ radiusApproximationSet p g c ε δ

/-- The fixed compact sphere family. The radius is ambient L2, not the ordinary
norm on the first half of the coordinates.-/
def smallGradientSphere {d : ℕ} (g : Fin d → AmbientPolynomial d)
    (R ε : ℝ) : Set (TorusAmbient d) :=
  {u | ‖u‖ = 1 ∧ R • u ∈ affineTorus d ∧
    R * ambientDifferentialNorm g (R • u) ≤ ε}

/-- OPEN: a uniform component bound and rectifiable paths, for the exact fixed
sphere family. The path image must lie in its component; its length is metric
variation on `[0,1]`. Semialgebraic parametrization is not demanded here, so this
is a necessary restricted obligation rather than full coverage of the path lemma.-/
def SpherePathObligation : Prop :=
  ∀ d (g : Fin d → AmbientPolynomial d),
    ∃ N : ℕ, 1 ≤ N ∧ ∃ L : ℝ, 1 ≤ L ∧
    ∀ R ε : ℝ, 1 < R → 0 < ε →
    ∃ label : smallGradientSphere g R ε → Fin N,
      (∀ x y, label x = label y ↔
        y.val ∈ connectedComponentIn (smallGradientSphere g R ε) x.val) ∧
      ∀ x y : smallGradientSphere g R ε, label x = label y →
        ∃ γ : ℝ → TorusAmbient d,
          ContinuousOn γ (Icc 0 1) ∧ γ 0 = x.val ∧ γ 1 = y.val ∧
          (∀ t ∈ Icc (0 : ℝ) 1,
            γ t ∈ connectedComponentIn (smallGradientSphere g R ε) x.val) ∧
          eVariationOn γ (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal L

end DuistermaatVanDerKallen

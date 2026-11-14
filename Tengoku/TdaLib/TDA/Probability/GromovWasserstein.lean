import Tengoku.TdaLib.TDA.Probability.SamplingMoments

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Distortion Gromov–Wasserstein costs for atomic probability inputs

The convention is one half of the infimum of rooted distortion moments under
arbitrary probability couplings. The two copies of a pair are independently
drawn from the same coupling. This differs from transport in a common ambient
space, and from transport between the points of one persistence diagram.
-/

noncomputable section

universe u v
namespace TDA.Probability

open scoped ENNReal

variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]

/-- Pairwise metric distortion on the joint input carrier.-/
def distortion (a b : X × Y) : ℝ≥0∞ := ENNReal.ofReal |dist a.1 b.1 - dist a.2 b.2|

/--
@isnad1 id=eq.0h3v.s4.e1c2b2fa4b47 from=translated src=- shape=8e4ede1a vocab=dfd35b7f
-/
@[simp] theorem distortion_self (a : X × Y) : distortion a a = 0 := by
  simp [distortion]

/--
@isnad1 id=eq.0h4v.s5.01855a91d0a4 from=translated src=- shape=bd75494e vocab=dfd35b7f
-/
theorem distortion_comm (a b : X × Y) : distortion a b = distortion b a := by
  simp only [distortion, dist_comm]

/-- Unrooted two-draw distortion moment for a probability coupling.-/
def Coupling.distortionMoment {μ : PMF X} {ν : PMF Y} (π : Coupling μ ν) (p : ℝ) : ℝ≥0∞ :=
  expectation π.joint (fun a => expectation π.joint (fun b => distortion a b ^ p))

/-- Distortion GW with the standard factor one half and a real finite exponent.-/
def gromovWasserstein (p : ℝ) (μ : PMF X) (ν : PMF Y) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ * ⨅ π : Coupling μ ν, π.distortionMoment p ^ p⁻¹

/-- Essential two-draw distortion for a probability coupling.-/
def Coupling.distortionInfinity {μ : PMF X} {ν : PMF Y} (π : Coupling μ ν) : ℝ≥0∞ :=
  essentialSup π.joint (fun a => essentialSup π.joint (distortion a))

/-- Infinity distortion GW retains its essential-supremum definition.-/
def gromovWassersteinInfinity (μ : PMF X) (ν : PMF Y) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ * ⨅ π : Coupling μ ν, π.distortionInfinity

/-- A singleton target has no choice of distortion moment: the coupling's
first marginal alone determines it.
@isnad1 id=eq.0h6v.s6.945dc11b0572 from=translated src=- shape=65a0bc55 vocab=aacee2ea
-/
theorem Coupling.distortionMoment_of_subsingleton [Subsingleton Y]
    {μ : PMF X} {ν : PMF Y} (π : Coupling μ ν) (p : ℝ) :
    π.distortionMoment p = expectation μ (fun x => expectation μ
      (fun x' => ENNReal.ofReal (dist x x') ^ p)) := by
  have hd (a b : X × Y) : distortion a b = ENNReal.ofReal (dist a.1 b.1) := by
    simp [distortion, Subsingleton.elim a.2 b.2, abs_of_nonneg dist_nonneg]
  simp only [Coupling.distortionMoment, hd]
  have hm (f : X → ℝ≥0∞) : expectation π.joint (fun a => f a.1) = expectation μ f := by
    rw [← expectation_map, π.fst_map]
  calc
    _ = expectation π.joint (fun a => expectation μ
        (fun x' => ENNReal.ofReal (dist a.1 x') ^ p)) := by
      congr 1
      funext a
      exact hm (fun x' => ENNReal.ofReal (dist a.1 x') ^ p)
    _ = _ := hm (fun x => expectation μ (fun x' => ENNReal.ofReal (dist x x') ^ p))

/-- The finite-p distortion distance to a singleton is one half the rooted
pairwise distance moment. It tends to zero when a remote atom's mass vanishes.
@isnad1 id=eq.0h5v.s6.40f18c597d52 from=translated src=- shape=e8d64299 vocab=87ab671e
-/
theorem gromovWasserstein_of_subsingleton [Subsingleton Y]
    (μ : PMF X) (ν : PMF Y) (p : ℝ) :
    gromovWasserstein p μ ν = (2 : ℝ≥0∞)⁻¹ *
      expectation μ (fun x => expectation μ (fun x' => ENNReal.ofReal (dist x x') ^ p)) ^ p⁻¹ := by
  simp [gromovWasserstein, Coupling.distortionMoment_of_subsingleton]

end TDA.Probability

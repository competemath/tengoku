import Tengoku.SingularityCompleteLean.Singularity.SupportedCoordinates
import Tengoku.SingularityCompleteLean.Singularity.CyclicOrbits
import Tengoku.SingularityCompleteLean.Singularity.GreenBoundary
import Tengoku.SingularityCompleteLean.Singularity.ExponentialLattice
import Tengoku.Seed.Topology.Algebra.InfiniteSum.Real

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Green boundary limits in finite cyclic-orbit coordinates

The compressed inverse is transported by an actual linear isometric equivalence.
Finite families of exponential orbit bounds supply the required summability.
The normalized geometric separator is constructed in GeometricStrip.lean.
GreenPoissonBounds.lean derives its envelopes from the distance comparison
and bounded-distance ray approaches. The geometric boundary limits remain open.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Singularity

variable {J : Type*}

/-- Exponential square envelopes are summable on any finite collection of integer orbits.-/
theorem summable_orbit_exp_sq [Fintype J] {τ : ℝ} (hτ : 0 < τ) (C : J → ℝ) :
    Summable (fun p : ℤ × J => (C p.2 * Real.exp (-τ * |(p.1 : ℝ)|)) ^ 2) := by
  apply (summable_prod_of_nonneg (fun p => sq_nonneg _)).mpr
  constructor
  · intro n
    exact (hasSum_fintype _).summable
  · simp only [tsum_fintype]
    exact summable_sum (fun j _ => summable_exp_abs_int_sq hτ (C j))

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]

/-- Cyclic coordinates give the concrete Hilbert-space equivalence needed by Fourier analysis.-/
def cyclicSupportedCoordinates (a : Γ) (b : J → Γ) (ha : ¬IsOfFinOrder a)
    (hb : ∀ j k (n : ℤ), a ^ n * b j = b k → j = k) :
    supportedL2 (cyclicOrbitUnion a b) ≃ₗᵢ[ℂ] SequenceL2 (ℤ × J) :=
  supportedCoordinatesEquiv (cyclicOrbitEquiv a b ha hb)

omit [MeasurableMul Γ] in
theorem cyclicSupportedCoordinates_apply (a : Γ) (b : J → Γ) (ha : ¬IsOfFinOrder a)
    (hb : ∀ j k (n : ℤ), a ^ n * b j = b k → j = k)
    (f : supportedL2 (cyclicOrbitUnion a b)) (n : ℤ) (j : J) :
    cyclicSupportedCoordinates a b ha hb f (n, j) = (f : GroupL2 Γ) (a ^ n * b j) := rfl

variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  {A : Set Γ} (e : (ℤ × J) ≃ A)

/-- The actual compressed Green inverse in the orbit sequence space.-/
def orbitGreenInverse : SequenceL2 (ℤ × J) →L[ℂ] SequenceL2 (ℤ × J) :=
  coordinateOperator e (walkGreenCompression s μ hμ hmass hgap A).symm.toContinuousLinearMap

/-- Normalized row in the same coordinates as the analysis operator.-/
def orbitGreenRow (x : Γ) (r : ℝ) : SequenceL2 (ℤ × J) :=
  supportedCoordinatesEquiv e (normalizedGreenRow s μ A x r)

/-- Normalized column in the same coordinates as the analysis operator.-/
def orbitGreenColumn (y : Γ) (c : ℝ) : SequenceL2 (ℤ × J) :=
  supportedCoordinatesEquiv e (normalizedGreenColumn s μ A y c)

end Singularity

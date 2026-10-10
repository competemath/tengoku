module
public import Tengoku.Causalean.Causalean.Stat.Concentration.BoundedVariation.Variation
public import Tengoku

/-!
# Clipped finite factorial-polynomial paths

A finite linear combination of deterministic continuous coefficient paths, with random scalar
factorial monomials, yields a continuous path. If the coefficients have bounded variation and the
monomials have finite second moments, clipping preserves bounded variation and gives an
integrable squared path size. Independence follows from disjoint measurable coordinate blocks.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.BoundedVariation
open scoped BigOperators

namespace Causalean.Stat.Concentration.BoundedVariation

/-- [a clipping radius and scalar value](hyp:cap,x) determine [the value clipped to the symmetric interval around zero](goal).

Scalar clipping to the symmetric interval with radius `cap`.
-/
def scalarClip (cap x : ℝ) : ℝ := min cap (max (-cap) x)

/-- A finite linear combination of continuous coefficient paths remains continuous after scalar
clipping. -/
theorem continuous_clipped_finite_sum {ι : Type*} [Fintype ι]
    (c : ι → Path) (x : ι → ℝ) (cap : ℝ) :
    Continuous (fun t : Time => scalarClip cap (∑ a, x a * c a t)) := by
  unfold scalarClip
  apply Continuous.min continuous_const
  apply Continuous.max continuous_const
  fun_prop

/-- [coefficient paths, random scalar coefficients, a clipping radius, and a sample point](hyp:c,X,cap,ω) determine [the resulting clipped continuous path](goal).

A random finite factorial-polynomial path formed from coefficient paths and scalar monomial
values, then clipped to a fixed symmetric interval.
-/
def clippedFinitePath {ι Ω : Type*} [Fintype ι]
    (c : ι → Path) (X : Ω → ι → ℝ) (cap : ℝ) (ω : Ω) : Path :=
  ⟨fun t => scalarClip cap (∑ a, X ω a * c a t),
    continuous_clipped_finite_sum c (X ω) cap⟩

/-- Measurable scalar monomials produce a measurable random continuous path when their
coefficient paths and clipping radius are deterministic. -/
theorem measurable_clippedFinitePath {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (c : ι → Path) (X : Ω → ι → ℝ)
    (hX : ∀ a, Measurable (fun ω => X ω a)) (cap : ℝ) :
    Measurable (clippedFinitePath c X cap) := by
  have hcont : Continuous (fun x : ι → ℝ =>
      clippedFinitePath c (fun _ => x) cap ()) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : (ι → ℝ) × Time =>
      scalarClip cap (∑ a, p.1 a * c a p.2))
    unfold scalarClip
    fun_prop
  have hvec : Measurable X := measurable_pi_lambda _ hX
  let : BorelSpace Path := ⟨rfl⟩
  exact hcont.measurable.comp hvec

/-- Measurable functions of independent coordinate blocks produce independent clipped finite
paths, even when every block uses the same deterministic coefficient family. -/
theorem clippedFinitePath_independent_blocks
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) (block : Fin n → Ω → (ι → ℝ))
    (hblock : iIndepFun block μ) (c : Fin n → ι → Path) (cap : Fin n → ℝ) :
    iIndepFun (fun j ω =>
      clippedFinitePath (c j) (fun ω a => block j ω a) (cap j) ω) μ := by
  have hmap (j : Fin n) : Measurable (fun x : ι → ℝ =>
      clippedFinitePath (c j) (fun _ => x) (cap j) ()) := by
    have hcont : Continuous (fun x : ι → ℝ =>
        clippedFinitePath (c j) (fun _ => x) (cap j) ()) := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun p : (ι → ℝ) × Time =>
        scalarClip (cap j) (∑ a, p.1 a * c j a p.2))
      unfold scalarClip
      fun_prop
    let : BorelSpace Path := ⟨rfl⟩
    exact hcont.measurable
  exact hblock.comp _ hmap

end Causalean.Stat.Concentration.BoundedVariation

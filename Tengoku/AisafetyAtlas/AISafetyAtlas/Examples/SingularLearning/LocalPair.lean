module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.LocalPair

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Worked models for the local-pair relations

`AISafetyAtlas/SingularLearning/LocalPair.lean` fixes two relations in which a
local-pair claim can be made — the source specification `HasExactLocalPair` and
the operational `HasLocalVolumeOrder` — and the bridge between them.

## What the bridge buys

An earlier plan listed three uniqueness obligations, each with its own
radius-picking argument. Only one needs a proof. `exactLocalPair_imp_volumeOrder`
is valid *at* the exceptional radii — where there is no exact premise at all —
because a countable set has dense complement, so any radius is squeezed between
two good ones, and the sublevel volume is monotone in the radius. Uniqueness for
the exact relation and the cross-interface comparison are then one-liners.

## Satisfiability

`hasExactLocalPair_sq` inhabits the non-degenerate branch `0 < lam`: the germ
`K(x) = x₀²` on `EuclideanSpace ℝ (Fin 1)` has local pair `(1/2, 1)`. Without it
the relations were inhabited only through the neutral `(0, 1)` convention for a
germ vanishing on a whole neighbourhood, so every theorem above held of a class
nothing had been shown to belong to.

## What is not here

Two of the transfer combinators now exist, in
`AISafetyAtlas/SingularLearning/PairTransfer.lean`: comparability of germs
(print's Lemma 6.2) and free coordinates (print's Lemma 6.4(ii)), applied to this
module's `hasLocalVolumeOrder_sq` in
`AISafetyAtlas/Examples/SingularLearning/PairTransfer.lean`. The rest of the
calculus — products of germs in disjoint variables, regular quadratic factors,
local diffeomorphisms — is still missing, as is print's Lemma 6.1, which is what
would supply a pair to transfer for a germ not already computed by hand. Those
remain real gaps and are recorded rather than papered over.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning
open MeasureTheory Filter Topology

variable {n : ℕ}

/-! ## A witness: the one-dimensional quadratic germ

Until this section every occurrence of `HasExactLocalPair` and `HasLocalVolumeOrder`
in the repository was in hypothesis position, and the only germ known to satisfy
either relation was the degenerate one, through the neutral `(0, 1)` branch for a
`K` vanishing on a whole neighbourhood. So every theorem above was conditional on
something inhabiting the non-degenerate branch `0 < lam`. The germ `K(x) = x₀²`
inhabits it, which is what turns uniqueness and the bridge from true-but-possibly-
vacuous into statements about a nonempty relation.
-/

/-- The Lebesgue volume of the `ε`-sublevel set of `x ↦ x₀²` inside the ball of radius
`δ` about the origin of `EuclideanSpace ℝ (Fin 1)`, whenever the sublevel set is small
enough to sit strictly inside the ball.

This is the only genuinely measure-theoretic step. `EuclideanSpace ℝ (Fin 1)` is
`PiLp 2 (fun _ : Fin 1 => ℝ)`, so the computation is transported to `ℝ` along the
composite of `PiLp.volume_preserving_ofLp` (the `PiLp`-to-`ι → ℝ` collapse) and
`MeasureTheory.volume_preserving_funUnique` (the `Fin 1 → ℝ ≃ ℝ` collapse), under
which the set is the interval `Icc (-√ε) (√ε)`.-/
private theorem volume_sublevel_sq {δ ε : ℝ} (hε : 0 < ε) (hδ : Real.sqrt ε < δ) :
    volume {x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) δ | x 0 ^ 2 ≤ ε}
      = ENNReal.ofReal (2 * Real.sqrt ε) := by
  have hnorm : ∀ x : EuclideanSpace ℝ (Fin 1), ‖x‖ = |x 0| := fun x => by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
  have hmp : MeasurePreserving (fun x : EuclideanSpace ℝ (Fin 1) => x 0) volume volume :=
    (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).comp
      (PiLp.volume_preserving_ofLp (ι := Fin 1))
  have hset : {x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) δ | x 0 ^ 2 ≤ ε}
      = (fun x : EuclideanSpace ℝ (Fin 1) => x 0) ⁻¹'
          Set.Icc (-Real.sqrt ε) (Real.sqrt ε) := by
    ext x
    have habs : x 0 ^ 2 ≤ ε ↔ |x 0| ≤ Real.sqrt ε := by
      rw [← Real.sqrt_sq_eq_abs, Real.sqrt_le_sqrt_iff (by positivity)]
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, Metric.mem_ball, dist_zero_right,
      hnorm]
    constructor
    · rintro ⟨-, h2⟩
      exact abs_le.1 (habs.1 h2)
    · intro h
      have h' : |x 0| ≤ Real.sqrt ε := abs_le.2 h
      exact ⟨lt_of_le_of_lt h' hδ, habs.2 h'⟩
  rw [hset, hmp.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc]
  ring_nf

end AISafetyAtlas.Examples.SingularLearning

module

public import Tengoku.Seed.MeasureTheory.Measure.Hausdorff
public import Tengoku.Seed.Topology.MetricSpace.HausdorffDimension
public import Tengoku.Seed.Analysis.Calculus.ContDiff.RCLike
public import Tengoku.Seed.Analysis.Calculus.ContDiff.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A lower-dimensional parametrized family is null

If a set in `ℝ^q` is covered by the image of a locally Lipschitz map from `ℝ^p`
with `p < q`, it is Lebesgue null. This is the measure-theoretic content of *"a
family with fewer parameters than the ambient dimension misses almost every
point"*, and it is the substitute this repository uses for the semialgebraic
dimension theory such arguments are usually phrased in.

## Primary surface

| declaration | says |
|---|---|
| `volume_image_eq_zero_of_card_lt` | the image of any set under a locally Lipschitz `ι → ℝ` to `κ → ℝ` is null when `card ι < card κ` |
| `volume_image_eq_zero_of_contDiffOn` | the same for a `C¹` map on an open chart, which is what a rational parametrization gives |
| `volume_image_eq_zero_of_contDiff` | the global `C¹` form |
| `volume_range_eq_zero_of_contDiff` | the range form |
| `volume_setOf_exists_forall_dotProduct_eq_zero` | `L` hyperplanes whose normals share a parameter with fewer than `L` coordinates meet almost no point |
| `measurableSet_exists_of_isClosed` | a projection along a σ-compact factor of a closed set is measurable |

The parameter is restricted by a predicate `P`, because the applications only
know the normals are nonzero at the parameters they actually produce.

## Why this and not semialgebraic dimension

Mathlib carries no semialgebraic sets, no o-minimality and no Tarski–Seidenberg,
so the usual route — *the bad set is a projection of a semialgebraic set of
dimension `< q`, hence null* — is unavailable. Mathlib does carry Hausdorff
dimension, including `dimH_image_le_of_locally_lipschitzOn` and
`measure_zero_of_dimH_lt`, and for an argument that can exhibit an explicit
Euclidean parametrization of the bad set that is enough: the fibre-dimension and
product-dimension facts of semialgebraic geometry are only needed to *find* the
parameter count, and a proof that writes the parametrization down does not need
them.

`MeasureTheory.hausdorffMeasure_pi_real` identifies `hausdorffMeasure q` with
`volume` on `κ → ℝ`, which is what turns the dimension bound into a statement
about Lebesgue measure.

## Provenance

Written to be lifted upstream: the declarations are named as Mathlib would name
them and the proofs use no atlas definitions.
-/

namespace AISafetyAtlas.Analysis

open MeasureTheory
open scoped ENNReal NNReal

/-! ## A parametrized family of hyperplane products

The shape a genericity argument actually meets: `L` linear conditions, one per
factor, whose normals all depend on a *single* parameter with fewer than `L`
coordinates. Each condition costs its factor one dimension, so the total is
`card α + L·k'` against an ambient `L·(k'+1)`, and the family misses almost every
point exactly when `card α < L`.

The charts are indexed by which coordinate each equation is solved for, and
`Fin.insertNth` does the solving, so no subtype bookkeeping appears. -/

section HyperplaneFamily

variable {α : Type*} [Fintype α] {L k' : ℕ}

/-- Solve the `ℓ`-th equation for the `i ℓ`-th coordinate.-/
private noncomputable def chartMap (w : (α → ℝ) → (Fin L × Fin (k' + 1) → ℝ))
    (i : Fin L → Fin (k' + 1)) (p : (α ⊕ (Fin L × Fin k')) → ℝ) :
    Fin L × Fin (k' + 1) → ℝ :=
  fun q =>
    (Fin.insertNth (i q.1)
        (-(∑ j : Fin k', p (.inr (q.1, j)) *
            w (fun x => p (.inl x)) (q.1, (i q.1).succAbove j))
          / w (fun x => p (.inl x)) (q.1, i q.1))
        (fun j => p (.inr (q.1, j))) : Fin (k' + 1) → ℝ) q.2

/-- The chart on which that division is legitimate.-/
private def chartSet (w : (α → ℝ) → (Fin L × Fin (k' + 1) → ℝ)) (i : Fin L → Fin (k' + 1)) :
    Set ((α ⊕ (Fin L × Fin k')) → ℝ) :=
  {p | ∀ ℓ, w (fun x => p (.inl x)) (ℓ, i ℓ) ≠ 0}

private theorem contDiff_restrict :
    ContDiff ℝ 1 fun p : (α ⊕ (Fin L × Fin k')) → ℝ => fun x : α => p (.inl x) :=
  contDiff_pi.2 fun x => contDiff_apply ℝ ℝ (Sum.inl x)

private theorem contDiff_wcomp {w : (α → ℝ) → (Fin L × Fin (k' + 1) → ℝ)} (hw : ContDiff ℝ 1 w)
    (q : Fin L × Fin (k' + 1)) :
    ContDiff ℝ 1 fun p : (α ⊕ (Fin L × Fin k')) → ℝ => w (fun x => p (.inl x)) q :=
  (contDiff_apply ℝ ℝ q).comp (hw.comp contDiff_restrict)

private theorem isOpen_chartSet {w : (α → ℝ) → (Fin L × Fin (k' + 1) → ℝ)}
    (hw : ContDiff ℝ 1 w) (i : Fin L → Fin (k' + 1)) : IsOpen (chartSet w i) := by
  rw [show chartSet w i
      = ⋂ ℓ : Fin L, {p : (α ⊕ (Fin L × Fin k')) → ℝ |
          w (fun x => p (.inl x)) (ℓ, i ℓ) ≠ 0} from by ext p; simp [chartSet]]
  exact isOpen_iInter_of_finite fun ℓ =>
    isOpen_ne_fun ((contDiff_wcomp hw (ℓ, i ℓ)).continuous) continuous_const

private theorem contDiffOn_chartMap {w : (α → ℝ) → (Fin L × Fin (k' + 1) → ℝ)}
    (hw : ContDiff ℝ 1 w) (i : Fin L → Fin (k' + 1)) :
    ContDiffOn ℝ 1 (chartMap w i) (chartSet w i) := by
  refine contDiffOn_pi.2 fun q => ?_
  by_cases hq : q.2 = i q.1
  · have hrw : ∀ p : (α ⊕ (Fin L × Fin k')) → ℝ, chartMap w i p q
        = -(∑ j : Fin k', p (.inr (q.1, j)) *
              w (fun x => p (.inl x)) (q.1, (i q.1).succAbove j))
            / w (fun x => p (.inl x)) (q.1, i q.1) := by
      intro p
      rw [chartMap, hq, Fin.insertNth_apply_same]
    simp only [hrw]
    refine ContDiffOn.div ?_ ?_ ?_
    · refine ContDiffOn.neg (ContDiff.contDiffOn (ContDiff.sum fun j _ =>
        (contDiff_apply ℝ ℝ (Sum.inr (q.1, j))).mul
          (contDiff_wcomp hw (q.1, (i q.1).succAbove j))))
    · exact (contDiff_wcomp hw (q.1, i q.1)).contDiffOn
    · exact fun p hp => hp q.1
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hq
    have hrw : ∀ p : (α ⊕ (Fin L × Fin k')) → ℝ,
        chartMap w i p q = p (.inr (q.1, j)) := by
      intro p
      rw [chartMap, ← hj, Fin.insertNth_apply_succAbove]
    simp only [hrw]
    exact (contDiff_apply ℝ ℝ (Sum.inr (q.1, j))).contDiffOn

end HyperplaneFamily

/-! ## Projections that stay measurable

A genericity argument states its bad set as *"there exists a rival such that…"*,
and a Tonelli step then needs that set to be measurable. The projection of a
Borel set is analytic, and Mathlib has analytic sets but **not** their universal
measurability — only Suslin's analytic-plus-coanalytic criterion. What it does
have is that projection along a compact factor is closed, and every finite-
dimensional real space is σ-compact, which is enough. -/

end AISafetyAtlas.Analysis

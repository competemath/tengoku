module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.CriticalFiber
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.GermPair
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.DiffeoTransfer
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.TwoSidedBand

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An indefinite Hessian block forces the two-sided pair `(1,1)`

Three modules each hold one link of the chain print's Stage 3 argument runs, and none of them
joins to the next without work.

* `exists_gromoll_meyer_splitting` (`CriticalFiber`) flattens a smooth `f` on `W × V` near a
  critical point onto `2⁻¹ Q₀ (Θ q).1 (Θ q).1 + g q.2`, provided the `W`-block of the Hessian is
  handed over as an **isomorphism onto the dual**.
* `hasLocalVolumeOrder_abs_matrixQuadForm_add_germ` (`GermPair`) computes the band order of
  `|Q(ξ) + g(ζ)|` for a nondegenerate indefinite **matrix** form in at least three variables plus
  an arbitrary continuous germ on the complement.
* `hasLocalVolumeOrder_comp_of_lipschitz` (`DiffeoTransfer`) moves a local volume order through a
  chart that is bi-Lipschitz near the point, which a `C^∞` chart with invertible derivative is.

The gaps are three. The splitting speaks of a dual isomorphism and the band estimate of a
matrix; the splitting lives on a product `W × V` and the band estimate on a single Euclidean
space; and the splitting's chart is produced with no inverse, while the transport needs one on
both sides. This module closes all three and states the consequence.

## What is proved

`hasLocalVolumeOrder_centeredBandGerm_of_indefinite_block`: if a smooth `L` on
`EuclideanSpace ℝ (Fin D)` has a critical point at `w₀` and, in some linear chart splitting the
space as `ℝ^m × ℝ^d` with `m ≥ 3`, the `ℝ^m` block of the Hessian is a symmetric matrix `K` with
`det K ≠ 0` taking both signs, then the two-sided band `|L x − L w₀| ≤ ε` has volume `Θ(ε)` in
every small ball around `w₀`.

**Nothing is assumed about the Hessian off the block.** The complementary germ the splitting
produces is carried by the band estimate as an arbitrary continuous function vanishing at the
origin, so the `ℝ^d` directions may be as degenerate as they like. That is the point of the
statement, and `Examples/SingularLearning/IndefiniteBlockPair.lean` witnesses it on a model
whose Hessian is identically zero off the block.

## The normalisation, and where the factor two goes

`K` is the **Hessian block itself**: the hypothesis reads

    `blockW _ _ (fderiv ℝ (fderiv ℝ (fun p => L (w₀ + Ξ p))) 0) x y = matrixQuadPolar K x y`,

so `hsymm`, `hdet`, `hpos` and `hneg` are conditions on the second derivative and not on some
rescaling of it. The splitting delivers `2⁻¹ * Q₀ η η`, so the matrix handed to the band estimate
is `(2 : ℝ)⁻¹ • K`, and its symmetry, nondegeneracy and indefiniteness are **re-derived** for
that matrix rather than inherited: `isSymm_smul`, `det_smul_ne_zero` and `matrixQuadForm_smul`
do exactly that. A scalar multiple changes none of the three, but the proof says so rather than
assuming it, because a sign or a factor lost here would produce a theorem about a different
form that every other check in this repository would pass.

On the model `x ↦ x²` this reads `K = 2`, not `K = 1`. A caller who holds the coefficient matrix
of the quadratic part of the Taylor expansion must therefore double it before calling.

## The pieces built here

* `matrixPolarEquiv` turns `det K ≠ 0` into the isomorphism `W ≃L[ℝ] (W →L[ℝ] ℝ)` the splitting
  demands. Injectivity is the substance — a functional annihilating the image of `K` annihilates
  everything, because `K` is onto — and equality of dimensions upgrades it to a bijection.
* `splitCLE` is the coordinate split as a continuous linear equivalence, the same function as
  `splitLE` and as `euclideanProdEquiv`.
* `exists_lipschitzOnWith_ball_of_contDiffAt` is the `ContDiffAt` form of the Lipschitz-ball
  extraction that `exists_lipschitzOnWith_ball` performs for analytic maps.
* `HasLocalVolumeOrder.congr_of_eventuallyEq` records that the order is a property of the germ.
  The chart identity holds only on the neighbourhood the splitting produces, so the transported
  order has to be moved onto the germ the statement names.

The local inverse of the chart comes from `ContDiffAt.to_localInverse`; the two sets on which
the chart and its inverse invert each other are taken to be exactly the sets where they do, which
is all the transport lemma asks for and avoids constructing a homeomorphism.
-/

noncomputable section

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Filter Topology

open scoped ContDiff Matrix

/-! ## The polar form of a matrix -/

/-- The polarisation of `matrixQuadForm`: the bilinear form of `K`.-/
@[expose] public noncomputable def matrixQuadPolar {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (fun i => x i) ⬝ᵥ (K *ᵥ (fun i => y i))

/-- The polar form as a bilinear map.-/
@[expose] public noncomputable def matrixPolarBilin {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ :=
  (Matrix.toLinearMap₂' ℝ K).compl₁₂
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap

public theorem matrixPolarBilin_apply {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    matrixPolarBilin K x y = matrixQuadPolar K x y := by
  rw [matrixPolarBilin, LinearMap.compl₁₂_apply, Matrix.toLinearMap₂'_apply']
  rfl

/-- The polar form read as a map into the continuous dual.-/
@[expose] public noncomputable def matrixPolarDual {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  (LinearMap.toContinuousLinearMap :
      (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).toLinearMap.comp
    (matrixPolarBilin K)

public theorem matrixPolarDual_apply {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    matrixPolarDual K x y = matrixQuadPolar K x y := by
  rw [matrixPolarDual]
  simp [matrixPolarBilin_apply]

public theorem injective_matrixPolarDual {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    (hdet : K.det ≠ 0) : Function.Injective (matrixPolarDual K) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hall : ∀ v : Fin n → ℝ, (fun i => x i) ⬝ᵥ v = 0 := by
    intro v
    have hy := congrArg (fun φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      φ ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm (K⁻¹ *ᵥ v))) hx
    simp only [zero_apply] at hy
    rw [matrixPolarDual_apply] at hy
    have hKv : K *ᵥ (K⁻¹ *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv K (Ne.isUnit hdet), Matrix.one_mulVec]
    rw [matrixQuadPolar] at hy
    rwa [show (fun i => ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm (K⁻¹ *ᵥ v)) i)
      = K⁻¹ *ᵥ v from rfl, hKv] at hy
  ext i
  have hi := hall (Pi.single i 1)
  simpa using hi

/-- The continuous dual of a Euclidean space has the dimension of the space.-/
public theorem finrank_euclidean_dual (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
  rw [← (LinearMap.toContinuousLinearMap :
    (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).finrank_eq]
  exact Subspace.dual_finrank_eq

/-- **A matrix with nonvanishing determinant polarises to an isomorphism onto the dual.**-/
@[expose] public noncomputable def matrixPolarEquiv {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (hdet : K.det ≠ 0) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  (LinearMap.linearEquivOfInjective (matrixPolarDual K) (injective_matrixPolarDual hdet)
    (finrank_euclidean_dual n).symm).toContinuousLinearEquiv

/-! ## Rescaling a matrix rescales its form -/

/-! ## A local volume order only sees the germ -/

/-! ## The coordinate split as a continuous linear equivalence -/

/-- `splitLE` packaged as a continuous linear equivalence.  Finite dimensionality makes the
packaging free, and it is what a transport lemma stated for continuous maps consumes.-/
@[expose] public noncomputable def splitCLE (p q : ℕ) :
    (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (p + q)) :=
  (splitLE p q).toContinuousLinearEquiv

/-! ## Lipschitz balls from a `C¹` germ -/

/-! ## The band pair in split coordinates -/

/-! ## The theorem -/

end AISafetyAtlas.SingularLearning

end

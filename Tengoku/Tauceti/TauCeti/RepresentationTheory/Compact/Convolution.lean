/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.RepresentationTheory.Compact.Averaging
public import Tengoku

/-!
# Convolution operators on `L²` of a compact group

For a continuous kernel `k : C(G, 𝕜)` on a compact group `G` and an `L²` function `f`, the
convolution

`(k * f) x = ∫ y, k (x * y⁻¹) * f y ∂(haarProb G)`

makes sense at *every* point `x`, not merely almost everywhere: the integral is the `L²` pairing of
`f` against the continuous function `y ↦ conj (k (x * y⁻¹))`, and that function varies continuously
with `x` in the uniform norm. Convolution therefore smooths `L²(G)` into `C(G)`, and the resulting
map `convolutionCLM k : L²(G) →L[𝕜] C(G)` is bounded by the uniform norm of the kernel.

Composing with `ContinuousMap.toLp` gives the convolution operator `convolutionOperator k` on
`L²(G)`. Its properties are proved here: it is self-adjoint when the kernel is symmetric
(`k g⁻¹ = conj (k g)`), it commutes with right translation, and it is a **compact operator**.
Together these say that the eigenspace of a symmetric convolution operator at a nonzero eigenvalue
is a *finite-dimensional* right-translation-invariant subspace of `L²(G)` all of whose elements
have continuous representatives, and that such eigenspaces exist; the eigenspaces at *all*
eigenvalues, the possibly infinite-dimensional kernel included, together span a dense subspace.
This is how the Peter-Weyl theorem manufactures finite-dimensional representations of `G` without
presupposing that any exist.

## Main definitions

* `TauCeti.convolutionCLM`: convolution against a continuous kernel, as a bounded linear map
  `Lp 𝕜 2 (haarProb G) →L[𝕜] C(G, 𝕜)`.
* `TauCeti.convolutionOperator`: the convolution operator `f ↦ k * f` on `Lp 𝕜 2 (haarProb G)`.

## Main statements

* `TauCeti.convolutionCLM_apply_apply`: the pointwise formula
  `(k * f) x = ∫ y, k (x * y⁻¹) * f y`.
* `TauCeti.convolutionCLM_toLp_apply`: the translated formula
  `(k * f) x = ∫ z, k z * f (z⁻¹ * x)` when `f` is continuous.
* `TauCeti.norm_convolutionCLM_apply_le`: `‖k * f‖_∞ ≤ ‖k‖_∞ * ‖f‖₂`, so convolution against a
  continuous kernel is bounded from `L²(G)` into the uniform norm of `C(G)`.
* `TauCeti.isSelfAdjoint_convolutionOperator`: a symmetric kernel gives a self-adjoint operator.
* `TauCeti.convolutionCLM_compMeasurePreserving_mul_right`: convolution commutes with right
  translation.
* `TauCeti.isCompactOperator_convolutionCLM` and `TauCeti.isCompactOperator_convolutionOperator`:
  convolution against a continuous kernel is a compact operator, into `C(G)` and into `L²(G)`.
* `TauCeti.finiteDimensional_eigenspace_convolutionOperator`: consequently the eigenspace of
  `convolutionOperator k` at a nonzero eigenvalue is finite-dimensional.
* `TauCeti.ae_eq_smul_convolutionCLM_of_mem_eigenspace`: an eigenvector at a nonzero eigenvalue is
  almost everywhere equal to the continuous function `μ⁻¹ • (k * f)`.
* `TauCeti.convolutionCLM_eq_zero_of_mem_eigenspace_zero`: an eigenvector at the eigenvalue `0`
  convolves to the zero function.
* `TauCeti.compMeasurePreserving_mul_right_mem_eigenspace_convolutionOperator`: the eigenspaces are
  invariant under right translation.
* `TauCeti.exists_hasEigenvalue_ne_zero_convolutionOperator`: a nonzero symmetric convolution
  operator has a nonzero eigenvalue, so such an eigenspace really exists.
* `TauCeti.orthogonalComplement_iSup_eigenspaces_convolutionOperator_eq_bot`: the eigenspaces of a
  symmetric convolution operator, at every eigenvalue, span a dense subspace of `L²(G)`.

## Implementation notes

Compactness is read off the same kernel sections, with no separate uniform-continuity argument:
the value `(k * f) x` is the `L²` pairing of `f` against the section at `x`, and the sections
depend continuously on `x` *in the uniform norm*, so the images of the unit ball are equicontinuous
by inspection. Arzelà-Ascoli (`BoundedContinuousFunction.arzela_ascoli`) then applies, in
`G →ᵇ 𝕜`, to which `C(G, 𝕜)` is isometric because `G` is compact.

Mathlib's `convolution` (`Mathlib/Analysis/Convolution.lean`) is the convolution of two functions
on an *additive* group against a bilinear pairing, and does not apply here: `G` is multiplicative,
and one of the two arguments is an `L²` class rather than a function. The kernel sections
`y ↦ conj (k (x * y⁻¹))` are assembled with `ContinuousMap.curry`, whose continuity is exactly the
statement that they depend continuously on `x`, so no uniform-continuity argument is needed.

Self-adjointness is proved by writing `convolutionOperator k H`, for a *continuous* `H`, as the
Bochner integral of the kernel sections weighted by `H`, and then extending to all of `L²(G)` by
density (`ContinuousMap.toLp_denseRange`). The more direct Fubini argument on `G × G` is not
available: the product of two Borel spaces is Borel only under a second-countability hypothesis,
which a compact group need not satisfy, whereas a continuous function on a compact space is
integrable with no such hypothesis (`TauCeti.integrable_continuousMap`).

The conjugation in the kernel sections is bookkeeping for Mathlib's convention that the inner
product is conjugate linear in its first argument; it is invisible in the pointwise formula
`convolutionCLM_apply_apply`.

## References

This is the opening of Layer 5 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap), which names
`convolutionOperator`, its self-adjointness for a symmetric kernel (there spelled
`convolutionOperator_isSelfAdjoint`, renamed here to `isSelfAdjoint_convolutionOperator` for the
predicate-prefix convention), its compactness (`convolutionOperator_isCompact`) and the finite
dimensionality of its nonzero eigenspaces (`convolutionOperator_eigenspace_finiteDimensional`) as
milestones on the non-circular route to the Peter-Weyl theorem.

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC (2016), §5.2.
* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapters 3-4.
-/

public section

open MeasureTheory
open scoped BoundedContinuousFunction InnerProductSpace

namespace TauCeti

section CompactGroup

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-! ### Preliminaries on `L²` against normalized Haar measure -/

/-- Normalized Haar measure is a probability measure, so passing from the uniform norm to the `L²`
norm is a contraction. -/
private theorem norm_toLp_le (F : C(G, 𝕜)) :
    ‖ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜 F‖ ≤ ‖F‖ := by
  have hmass : measureUnivNNReal (haarProb G) = 1 :=
    ENNReal.coe_inj.1 (by simp [coe_measureUnivNNReal])
  have hop : ‖(ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜)‖ ≤ 1 := by
    simpa [hmass] using ContinuousMap.toLp_norm_le (E := 𝕜) (p := 2) (𝕜 := 𝕜) (haarProb G)
  calc ‖ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜 F‖
      ≤ ‖(ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜)‖ * ‖F‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖F‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg F)
    _ = ‖F‖ := one_mul _

/-- Mathlib's `L2.inner_def` computes an inner product in `L²` as the integral of the pointwise
inner products `⟪a, b⟫ = conj a * b`. This is its specialization to a first argument coming from a
continuous function. -/
private theorem inner_toLp_left (F : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) :
    ⟪ContinuousMap.toLp 2 (haarProb G) 𝕜 F, f⟫_𝕜
      = ∫ x, (starRingEnd 𝕜) (F x) * f x ∂(haarProb G) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (haarProb G) (𝕜 := 𝕜) F] with x hx
  rw [hx, RCLike.inner_apply]
  ring

/-! ### The kernel sections

The section of the kernel `k` at `x` is `y ↦ conj (k (x * y⁻¹))`. Currying the continuous function
`(x, y) ↦ conj (k (x * y⁻¹))` on `G × G` is exactly the statement that the section depends
continuously on `x` in the uniform norm. -/

/-- The conjugated kernel sections `x ↦ (y ↦ conj (k (x * y⁻¹)))`, as a continuous map into
`C(G, 𝕜)`. -/
private noncomputable def convSectionCM (k : C(G, 𝕜)) : C(G, C(G, 𝕜)) :=
  ContinuousMap.curry
    (star (k.comp ⟨fun p : G × G => p.1 * p.2⁻¹, continuous_fst.mul continuous_snd.inv⟩))

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem convSectionCM_apply (k : C(G, 𝕜)) (x y : G) :
    convSectionCM k x y = (starRingEnd 𝕜) (k (x * y⁻¹)) :=
  (rfl)

omit [MeasurableSpace G] [BorelSpace G] in
private theorem norm_convSectionCM_le (k : C(G, 𝕜)) (x : G) : ‖convSectionCM k x‖ ≤ ‖k‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg k)).2 fun y => by
    rw [convSectionCM_apply, RCLike.norm_conj]
    exact k.norm_coe_le_norm _

/-- The conjugated kernel sections, read in `L²(G)`. -/
private noncomputable def convSection (k : C(G, 𝕜)) : C(G, Lp 𝕜 2 (haarProb G)) :=
  ⟨fun x => ContinuousMap.toLp 2 (haarProb G) 𝕜 (convSectionCM k x),
    (ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜).continuous.comp (convSectionCM k).continuous⟩

private theorem convSection_apply (k : C(G, 𝕜)) (x : G) :
    convSection k x = ContinuousMap.toLp 2 (haarProb G) 𝕜 (convSectionCM k x) :=
  (rfl)

private theorem norm_convSection_le (k : C(G, 𝕜)) (x : G) : ‖convSection k x‖ ≤ ‖k‖ :=
  (norm_toLp_le _).trans (norm_convSectionCM_le k x)

/-! ### Convolution as a map into continuous functions -/

private noncomputable def convolutionₗ (k : C(G, 𝕜)) : Lp 𝕜 2 (haarProb G) →ₗ[𝕜] C(G, 𝕜) where
  toFun f := ⟨fun x => ⟪convSection k x, f⟫_𝕜, (convSection k).continuous.inner continuous_const⟩
  map_add' f₁ f₂ := by ext x; exact inner_add_right (convSection k x) f₁ f₂
  map_smul' c f := by ext x; exact inner_smul_right (convSection k x) f c

private theorem norm_convolutionₗ_le (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) :
    ‖convolutionₗ k f‖ ≤ ‖k‖ * ‖f‖ :=
  (ContinuousMap.norm_le _ (by positivity)).2 fun x =>
    (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_convSection_le k x) (norm_nonneg f))

/-- **Convolution against a continuous kernel**, as a bounded linear map from `L²(G)` into `C(G)`.

The value at `x` is the `L²` pairing of `f` against the kernel section at `x`, so it is defined at
every point of `G` and depends continuously on that point: convolving an `L²` class against a
continuous kernel produces a genuine continuous function, not another almost-everywhere class. -/
noncomputable def convolutionCLM (k : C(G, 𝕜)) : Lp 𝕜 2 (haarProb G) →L[𝕜] C(G, 𝕜) :=
  LinearMap.mkContinuous (convolutionₗ k) ‖k‖ (norm_convolutionₗ_le k)

private theorem convolutionCLM_apply_apply' (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) (x : G) :
    convolutionCLM k f x = ⟪convSection k x, f⟫_𝕜 :=
  (rfl)

/-- **The pointwise formula for convolution against a continuous kernel.** -/
theorem convolutionCLM_apply_apply (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) (x : G) :
    convolutionCLM k f x = ∫ y, k (x * y⁻¹) * f y ∂(haarProb G) := by
  rw [convolutionCLM_apply_apply', convSection_apply, inner_toLp_left]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [convSectionCM_apply, RCLike.conj_conj]

private theorem integrable_convolution_integrand (k : C(G, 𝕜))
    (f : Lp 𝕜 2 (haarProb G)) (x : G) :
    Integrable (fun y => k (x * y⁻¹) * f y) (haarProb G) := by
  refine (L2.integrable_inner (convSection k x) f).congr ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (haarProb G) (𝕜 := 𝕜)
    (convSectionCM k x)] with y hy
  rw [convSection_apply, hy, RCLike.inner_apply, convSectionCM_apply, RCLike.conj_conj,
    mul_comm]

/-- Convolution is zero when its kernel is zero. -/
@[simp]
theorem convolutionCLM_zero :
    convolutionCLM (G := G) (0 : C(G, 𝕜)) = 0 := by
  ext f x
  simp [convolutionCLM_apply_apply]

/-- Convolution is additive in its kernel. -/
@[simp]
theorem convolutionCLM_add (k₁ k₂ : C(G, 𝕜)) :
    convolutionCLM (k₁ + k₂) = convolutionCLM k₁ + convolutionCLM k₂ := by
  ext f x
  simp only [add_apply, ContinuousMap.add_apply, convolutionCLM_apply_apply]
  rw [← integral_add (integrable_convolution_integrand k₁ f x)
    (integrable_convolution_integrand k₂ f x)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => add_mul _ _ _)

/-- Convolution is compatible with scalar multiplication of its kernel. -/
@[simp]
theorem convolutionCLM_smul (c : 𝕜) (k : C(G, 𝕜)) :
    convolutionCLM (c • k) = c • convolutionCLM k := by
  ext f x
  simp only [smul_apply, ContinuousMap.smul_apply, smul_eq_mul, convolutionCLM_apply_apply]
  rw [← integral_const_mul c]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => mul_assoc _ _ _)

/-! ### The convolution operator on `L²(G)` -/

/-- **The convolution operator** `f ↦ k * f` on `L²(G)`, for a continuous kernel `k`.

It factors through `C(G)`: `convolutionCLM` produces a continuous function, and
`ContinuousMap.toLp` reads that function back into `L²(G)`. -/
noncomputable def convolutionOperator (k : C(G, 𝕜)) :
    Lp 𝕜 2 (haarProb G) →L[𝕜] Lp 𝕜 2 (haarProb G) :=
  (ContinuousMap.toLp 2 (haarProb G) 𝕜).comp (convolutionCLM k)

/-- The convolution operator is `convolutionCLM` followed by `ContinuousMap.toLp`. -/
theorem convolutionOperator_apply (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) :
    convolutionOperator k f = ContinuousMap.toLp 2 (haarProb G) 𝕜 (convolutionCLM k f) :=
  (rfl)

/-- The convolution operator is zero when its kernel is zero. -/
@[simp]
theorem convolutionOperator_zero :
    convolutionOperator (G := G) (0 : C(G, 𝕜)) = 0 := by
  ext f
  simp [convolutionOperator_apply]

/-- The convolution operator is additive in its kernel. -/
@[simp]
theorem convolutionOperator_add (k₁ k₂ : C(G, 𝕜)) :
    convolutionOperator (k₁ + k₂) = convolutionOperator k₁ + convolutionOperator k₂ := by
  ext f
  simp [convolutionOperator_apply]

/-- The convolution operator is compatible with scalar multiplication of its kernel. -/
@[simp]
theorem convolutionOperator_smul (c : 𝕜) (k : C(G, 𝕜)) :
    convolutionOperator (c • k) = c • convolutionOperator k := by
  ext f
  simp [convolutionOperator_apply]

/-! ### Self-adjointness for a symmetric kernel

For a *continuous* weight `H` the kernel sections may be averaged against `H`, giving a Bochner
integral in `C(G)` and, after `ContinuousMap.toLp`, one in `L²(G)`. Symmetry of the kernel
identifies that average with `k * H`, which is the adjoint relation on the dense subspace of
continuous functions; the general case follows because both sides of the relation are continuous in
their second argument. -/

/-- The kernel sections weighted by a continuous function `H`. -/
private noncomputable def weightedSectionsCM (k H : C(G, 𝕜)) : C(G, C(G, 𝕜)) :=
  ⟨fun x => H x • convSectionCM k x, H.continuous.smul (convSectionCM k).continuous⟩

/-- The kernel sections weighted by a continuous function `H`, read in `L²(G)`. -/
private noncomputable def weightedSections (k H : C(G, 𝕜)) : C(G, Lp 𝕜 2 (haarProb G)) :=
  ⟨fun x => H x • convSection k x, H.continuous.smul (convSection k).continuous⟩

/-! ### Equivariance under right translation -/

/-! ### Compactness of the convolution operator

Convolution against a continuous kernel carries the closed unit ball of `L²(G)` to a family of
continuous functions bounded by `‖k‖` and equicontinuous: the increment of `k * f` between two
points is controlled by the distance between the corresponding kernel sections, uniformly in `f`.
The Arzelà-Ascoli theorem makes that family relatively compact in `C(G)`, hence in `L²(G)`. -/

/-- The image of the closed unit ball of `L²(G)` under convolution against `k`, carried by the
isometry `ContinuousMap.isometryEquivBoundedOfCompact` into the bounded continuous functions on
`G`, where Mathlib's Arzelà-Ascoli theorem lives. -/
private noncomputable def convolutionUnitBallImage (k : C(G, 𝕜)) : Set (G →ᵇ 𝕜) :=
  (fun f : Lp 𝕜 2 (haarProb G) =>
      ContinuousMap.isometryEquivBoundedOfCompact G 𝕜 (convolutionCLM k f)) ''
    Metric.closedBall 0 1

/-! ### The eigenspaces of a convolution operator

Compactness bounds the dimension of each nonzero eigenspace; the pointwise formula shows every
eigenvector at a nonzero eigenvalue is a continuous function; and equivariance makes the
eigenspaces right-translation invariant. Together these are the three properties that turn a
symmetric convolution operator into a source of finite-dimensional representations of `G`. The
eigenspace at `0` is the complementary case: it convolves to nothing at all. -/

/-! ### The spectral consequences for a symmetric kernel

For a symmetric kernel the convolution operator is both compact and self-adjoint, so Mathlib's
spectral theory of compact self-adjoint operators applies to it. Two consequences matter for
Peter-Weyl: unless the operator vanishes it *has* a nonzero eigenvalue, and its eigenspaces
together span a dense subspace of `L²(G)`. -/

end CompactGroup

end TauCeti

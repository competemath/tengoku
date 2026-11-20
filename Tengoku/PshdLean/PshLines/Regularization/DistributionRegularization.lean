import Tengoku.PshdLean.PshLines.PshRegularizationData
import Tengoku.PshdLean.PshLines.Regularization.AdaptedKernelCoordinates
import Tengoku.PshdLean.PshLines.Regularization.AdaptedKernelNeighborhood
import Tengoku.PshdLean.PshLines.Regularization.AdaptedRadialKernel
import Tengoku.Seed.Geometry.Manifold.PartitionOfUnity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Local decreasing regularization of arbitrary distributions

A distribution with nonnegative constant-direction Levi derivatives admits, on a
neighborhood of every point of its domain, a decreasing sequence of globally
smooth plurisubharmonic regularizations converging weakly to it. The
construction pairs the distribution with smooth families of translated test
functions, uses normalized kernels radial for an auxiliary Hermitian norm,
establishes monotonicity as their radii decrease and weak convergence against
every test function, and extends smoothly after shrinking to a relatively
compact inner domain.

The existence proof is completed in `DistributionRegularizationFinal`.

Source: Demailly, Complex Analytic and Differential Geometry,
I.4.18--4.20 and I.5.8.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions Manifold NNReal Topology

namespace PshLines.Regularization

open AdaptedRadialKernel
open FirstPass

/-- A compact subset of an open finite-dimensional real vector space admits a
smooth test-function cutoff which equals one on a neighborhood of the compact
set and takes values in `[0, 1]`.
@isnad1 id=ex.2h3v.s8.eccc7ea05636 from=translated src=- shape=6ac416c2 vocab=6544c470
-/
theorem exists_testFunction_eq_one_nhds_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Ω : Opens E} {K : Set E}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ χ : 𝓓(Ω, ℝ),
      (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  have hKintV : K ⊆ interior V := by simpa [hVo.interior_eq] using hKV
  obtain ⟨f, hfK, hfV, hfrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (n := (⊤ : ℕ∞)) (𝓘(ℝ, E)) hK.isClosed hKintV
  have hsupp : Function.support f ⊆ V := by
    intro x hx
    by_contra hxV
    exact hx (hfV x hxV)
  let χ : 𝓓(Ω, ℝ) :=
    ⟨f, f.contMDiff.contDiff,
      HasCompactSupport.of_support_subset_isCompact hVc
        (hsupp.trans subset_closure),
      (closure_mono hsupp).trans hVΩ⟩
  exact ⟨χ, hfK, hfrange⟩

section AdaptedKernelData

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]

/-- The geometric and cutoff data supporting the canonical adapted radial
kernels around one point of an open domain.-/
structure AdaptedRadialKernelData (μ : Measure E) (Ω : Opens E) (x : E) where
  radius : ℝ
  radius_pos : 0 < radius
  inner : Opens E
  compact : Compacts E
  center_mem : x ∈ inner
  inner_le : inner ≤ Ω
  compact_subset : (compact : Set E) ⊆ Ω
  coordinate_buffer :
    ∀ z ∈ closure (inner : Set E), ∀ y : E,
      ‖adaptedComplexModelEquiv (y - z)‖ ≤ radius → y ∈ compact
  cutoff : 𝓓(Ω, ℝ)
  cutoff_one_on_compact : ∀ y ∈ compact, cutoff y = 1
  cutoff_mem_Icc : ∀ y, cutoff y ∈ Set.Icc (0 : ℝ) 1

/-- The normalized kernel family carried by adapted regularization data.-/
noncomputable def AdaptedRadialKernelData.kernel
    {μ : Measure E} {Ω : Opens E} {x : E}
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) : E → ℝ :=
  adaptedRadialKernel μ D.radius D.radius_pos j

/-- The buffered cutoff is one at every point reached by translating a center
in the closed inner domain by a vector in the adapted coordinate ball.
@isnad1 id=eq.2h7v.s10.939907517015 from=translated src=- shape=29235063 vocab=957be09d
-/
theorem AdaptedRadialKernelData.cutoff_eq_one_of_coordinate_displacement
    {μ : Measure E} {Ω : Opens E} {x : E}
    (D : AdaptedRadialKernelData μ Ω x) {z y : E}
    (hz : z ∈ closure (D.inner : Set E))
    (hy : ‖adaptedComplexModelEquiv (y - z)‖ ≤ D.radius) :
    D.cutoff y = 1 :=
  D.cutoff_one_on_compact y (D.coordinate_buffer z hz y hy)

/-- The closed inner domain is contained in the compact buffer.
@isnad1 id=le.0h5v.s8.cf27a2e0fea0 from=translated src=- shape=e35646e7 vocab=88fe5182
-/
theorem AdaptedRadialKernelData.closure_inner_subset_compact
    {μ : Measure E} {Ω : Opens E} {x : E}
    (D : AdaptedRadialKernelData μ Ω x) :
    closure (D.inner : Set E) ⊆ D.compact := by
  intro z hz
  exact D.coordinate_buffer z hz z (by simp [D.radius_pos.le])

/-- The adapted regularization data exist around every point of the domain.
@isnad1 id=nonempty.1h4v.s8.9b0546b109eb from=translated src=- shape=99b2f5ef vocab=679b3866
-/
theorem exists_adaptedRadialKernelData
    (μ : Measure E) [μ.IsAddHaarMeasure] {Ω : Opens E} {x : E}
    (hx : x ∈ Ω) : Nonempty (AdaptedRadialKernelData μ Ω x) := by
  let AReal : E ≃L[ℝ] ComplexModel (Module.finrank ℂ E) :=
    ((adaptedComplexModelEquiv (E := E)).toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv
  obtain ⟨R, hR, U, K, hxU, hUΩ, hKΩ, hbuffer⟩ :=
    exists_open_closure_coordinateBall_neighborhood AReal hx
  obtain ⟨χ, hχK, hχrange⟩ :=
    exists_testFunction_eq_one_nhds_compact K.isCompact hKΩ
  refine ⟨{
    radius := R
    radius_pos := hR
    inner := U
    compact := K
    center_mem := hxU
    inner_le := hUΩ
    compact_subset := hKΩ
    coordinate_buffer := by simpa [AReal] using hbuffer
    cutoff := χ
    cutoff_one_on_compact := ?_
    cutoff_mem_Icc := hχrange }⟩
  intro y hy
  exact hχK.self_of_nhdsSet y hy

variable {μ : Measure E} [BorelSpace E] [μ.IsAddHaarMeasure]
  {Ω : Opens E} {x : E}

/--
@isnad1 id=contdiff.0h6v.s8.b2628fc7ab99 from=translated src=- shape=693774cd vocab=d60ee054
-/
theorem AdaptedRadialKernelData.kernel_contDiff
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (D.kernel j) :=
  adaptedRadialKernel_contDiff μ D.radius D.radius_pos j

/--
@isnad1 id=le.0h7v.s8.f02b850262f7 from=translated src=- shape=05285674 vocab=7d105fd6
-/
theorem AdaptedRadialKernelData.kernel_nonneg
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) (y : E) :
    0 ≤ D.kernel j y :=
  adaptedRadialKernel_nonneg μ D.radius D.radius_pos j y

/--
@isnad1 id=eq.0h6v.s8.ca9e6862b54b from=translated src=- shape=6eb8c154 vocab=a6198956
-/
theorem AdaptedRadialKernelData.kernel_integral_one
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) :
    ∫ y : E, D.kernel j y ∂μ = 1 :=
  adaptedRadialKernel_integral_one μ D.radius D.radius_pos j

/--
@isnad1 id=hascompa.0h6v.s8.ed8f0af20f74 from=translated src=- shape=1eac17a2 vocab=60bd7686
-/
theorem AdaptedRadialKernelData.kernel_hasCompactSupport
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) :
    HasCompactSupport (D.kernel j) :=
  adaptedRadialKernel_hasCompactSupport μ D.radius D.radius_pos j

/--
@isnad1 id=integrab.0h6v.s8.b79422b2e23d from=translated src=- shape=7663fbc0 vocab=761f8d27
-/
theorem AdaptedRadialKernelData.kernel_integrable
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) :
    Integrable (D.kernel j) μ :=
  adaptedRadialKernel_integrable μ D.radius D.radius_pos j

/--
@isnad1 id=le.0h6v.s10.0567feeb7452 from=translated src=- shape=b3141a5e vocab=0cbdd4a5
-/
theorem AdaptedRadialKernelData.kernel_tsupport_subset
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) :
    tsupport (D.kernel j) ⊆
      {y | ‖adaptedComplexModelEquiv y‖ ≤ D.radius / ((j : ℝ) + 1)} :=
  adaptedRadialKernel_tsupport_subset_norm μ D.radius D.radius_pos j

/--
@isnad1 id=eq.1h8v.s11.97c0d4ea21eb from=translated src=- shape=99801703 vocab=f5a765c4
-/
theorem AdaptedRadialKernelData.kernel_unitary
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ)
    (a : ℂ) (ha : ‖a‖ = 1) (y : E) :
    D.kernel j
        (adaptedComplexModelEquiv.symm (a • adaptedComplexModelEquiv y)) =
      D.kernel j y :=
  adaptedRadialKernel_unitary μ D.radius D.radius_pos j a ha y

/--
@isnad1 id=eq.0h7v.s8.bd2a34f841e8 from=translated src=- shape=3d8b703d vocab=de459a51
-/
theorem AdaptedRadialKernelData.kernel_even
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) (y : E) :
    D.kernel j (-y) = D.kernel j y := by
  simpa using D.kernel_unitary j (-1 : ℂ) (by simp) y

/--
@isnad1 id=eq.0h8v.s11.b7b2ce608689 from=translated src=- shape=ee81756c vocab=c80b4172
-/
theorem AdaptedRadialKernelData.kernel_scale
    (D : AdaptedRadialKernelData μ Ω x) (a b : ℕ) (y : E) :
    D.kernel b y =
      (((b : ℝ) + 1) / ((a : ℝ) + 1)) ^
          Module.finrank ℝ (ComplexModel (Module.finrank ℂ E)) *
        D.kernel a
          (adaptedComplexModelEquiv.symm
            (((((b : ℝ) + 1) / ((a : ℝ) + 1)) : ℝ) •
              adaptedComplexModelEquiv y)) :=
  adaptedRadialKernel_scale μ D.radius D.radius_pos a b y

/-- In complex dimension zero the adapted kernel family is constant in its
scale index.
@isnad1 id=eq.1h7v.s8.9f58c76f0303 from=translated src=- shape=5c52615f vocab=ad4779aa
-/
theorem AdaptedRadialKernelData.kernel_eq_of_finrank_complex_eq_zero
    (D : AdaptedRadialKernelData μ Ω x) (hE : Module.finrank ℂ E = 0)
    (a b : ℕ) : D.kernel a = D.kernel b := by
  let _ : FiniteDimensional ℂ E := finiteDimensional_complex_of_real
  let _ : Subsingleton E := Module.finrank_zero_iff.mp hE
  funext y
  have hs := D.kernel_scale a b y
  have hdim :
      Module.finrank ℝ (ComplexModel (Module.finrank ℂ E)) = 0 := by
    rw [hE]
    exact Module.finrank_zero_of_subsingleton
  have hpoint :
      adaptedComplexModelEquiv.symm
          (((((b : ℝ) + 1) / ((a : ℝ) + 1)) : ℝ) •
            adaptedComplexModelEquiv y) = y :=
    Subsingleton.elim _ _
  rw [hdim, pow_zero, one_mul, hpoint] at hs
  exact hs.symm

end AdaptedKernelData

/-- Multiply a translated smooth kernel by a fixed test cutoff.  The cutoff
makes the result an actual test function on `Ω` for every translation
parameter, without any support assumption on the kernel.-/
def cutoffTranslatedTestFunction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (z : E) : 𝓓(Ω, ℝ) :=
  ⟨fun y ↦ χ y * κ (y - z),
    χ.contDiff.mul (hκ.comp (contDiff_id.sub contDiff_const)),
    χ.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans χ.tsupport_subset⟩

/--
@isnad1 id=eq.1h6v.s8.36f65ceaa512 from=translated src=- shape=fa1ce36e vocab=41107e8c
-/
@[simp]
theorem cutoffTranslatedTestFunction_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (z y : E) :
    cutoffTranslatedTestFunction χ κ hκ z y = χ y * κ (y - z) := rfl

/--
@isnad1 id=le.1h5v.s8.49e4b63a72e7 from=translated src=- shape=78ecffeb vocab=4b617908
-/
theorem cutoffTranslatedTestFunction_tsupport_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (z : E) :
    tsupport (cutoffTranslatedTestFunction χ κ hκ z) ⊆ tsupport χ :=
  tsupport_mul_subset_left

/-- On the closed inner domain, the fixed cutoff does not alter the translated
adapted kernel.  This is the local identity that lets the distributional
transpose be computed with a single compact support.
@isnad1 id=eq.1h8v.s8.32a11537d1e5 from=translated src=- shape=9606fd5d vocab=0d085034
-/
theorem AdaptedRadialKernelData.cutoffTranslatedTestFunction_eq_kernel
    {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {x : E}
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) {z y : E}
    (hz : z ∈ closure (D.inner : Set E)) :
    cutoffTranslatedTestFunction D.cutoff (D.kernel j) (D.kernel_contDiff j) z y =
      D.kernel j (y - z) := by
  rw [cutoffTranslatedTestFunction_apply]
  by_cases hkernel : D.kernel j (y - z) = 0
  · simp [hkernel]
  have hsupport : y - z ∈ tsupport (D.kernel j) :=
    subset_tsupport (D.kernel j) hkernel
  have hcoordinate := D.kernel_tsupport_subset j hsupport
  have hscale : D.radius / ((j : ℝ) + 1) ≤ D.radius := by
    have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by norm_num
    exact div_le_self D.radius_pos.le hj
  have hcutoff : D.cutoff y = 1 :=
    D.cutoff_eq_one_of_coordinate_displacement hz (hcoordinate.trans hscale)
  rw [hcutoff, one_mul]

/-- The same cutoff-translation family bundled in one fixed-support test space.
This is the domain on which the finite-order distribution estimate applies.-/
def cutoffTranslatedKernelSupportedIn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (z : E) :
    ContDiffMapSupportedIn E ℝ ⊤ K :=
  .of_support_subset (f := fun y : E ↦ χ y * κ (y - z))
    (χ.contDiff.mul (hκ.comp (contDiff_id.sub contDiff_const)))
    (subset_closure.trans (tsupport_mul_subset_left.trans hχK))

/--
@isnad1 id=eq.2h7v.s8.b60dbbb5de62 from=translated src=- shape=7b2af4cf vocab=e5a47143
-/
@[simp]
theorem cutoffTranslatedKernelSupportedIn_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (z y : E) :
    cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z y =
      χ y * κ (y - z) := by
  rfl

/--
@isnad1 id=eq.3h6v.s8.40441e3c3d13 from=translated src=- shape=206a963a vocab=90d2b752
-/
theorem ofSupportedIn_cutoffTranslatedKernelSupportedIn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω) (z : E) :
    TestFunction.ofSupportedIn hKΩ
        (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z) =
      cutoffTranslatedTestFunction χ κ hκ z := by
  ext y
  rfl

section LocalizedAdaptedKernel

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {x : E}

/-- The compact support of the single cutoff used for every translated
adapted kernel.-/
def AdaptedRadialKernelData.cutoffCompact
    (D : AdaptedRadialKernelData μ Ω x) : Compacts E :=
  ⟨tsupport D.cutoff, D.cutoff.hasCompactSupport⟩

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/--
@isnad1 id=le.0h5v.s8.a078afc1befc from=translated src=- shape=ccc410c1 vocab=2e1e9dd7
-/
theorem AdaptedRadialKernelData.cutoffCompact_subset
    (D : AdaptedRadialKernelData μ Ω x) :
    (D.cutoffCompact : Set E) ⊆ Ω :=
  D.cutoff.tsupport_subset

/-- A translated adapted kernel represented in one fixed-support smooth
function space, independently of its center and scale.-/
def AdaptedRadialKernelData.localizedKernelSupportedIn
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) (z : E) :
    ContDiffMapSupportedIn E ℝ ⊤ D.cutoffCompact :=
  cutoffTranslatedKernelSupportedIn D.cutoff (D.kernel j)
    (D.kernel_contDiff j) D.cutoffCompact (by rfl) z

/--
@isnad1 id=eq.0h8v.s9.17ffa032e994 from=translated src=- shape=61bddd58 vocab=7ad211d1
-/
@[simp]
theorem AdaptedRadialKernelData.localizedKernelSupportedIn_apply
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) (z y : E) :
    D.localizedKernelSupportedIn j z y =
      D.cutoff y * D.kernel j (y - z) :=
  rfl

/--
@isnad1 id=eq.0h7v.s8.b64873ca86d9 from=translated src=- shape=51e1d622 vocab=ccf2f559
-/
theorem AdaptedRadialKernelData.ofSupportedIn_localizedKernelSupportedIn
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) (z : E) :
    TestFunction.ofSupportedIn D.cutoffCompact_subset
        (D.localizedKernelSupportedIn j z) =
      cutoffTranslatedTestFunction D.cutoff (D.kernel j)
        (D.kernel_contDiff j) z :=
  ofSupportedIn_cutoffTranslatedKernelSupportedIn D.cutoff (D.kernel j)
    (D.kernel_contDiff j) D.cutoffCompact (by rfl) D.cutoffCompact_subset z

/-- On the closed inner domain, the fixed-support representative evaluates to
the untruncated translated adapted kernel.
@isnad1 id=eq.1h8v.s8.b8e0ef5cbfa3 from=translated src=- shape=44145299 vocab=8064b166
-/
theorem AdaptedRadialKernelData.localizedKernelSupportedIn_eq_kernel
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) {z y : E}
    (hz : z ∈ closure (D.inner : Set E)) :
    D.localizedKernelSupportedIn j z y = D.kernel j (y - z) := by
  rw [localizedKernelSupportedIn_apply]
  simpa only [cutoffTranslatedTestFunction_apply] using
    D.cutoffTranslatedTestFunction_eq_kernel j hz

/-- The distributional transpose applied to the fixed-support translated
kernel.  Smoothness and Levi positivity of this scalar function are isolated
as the next regularization obligations.-/
def AdaptedRadialKernelData.distributionRegularizedValue
    (D : AdaptedRadialKernelData μ Ω x) (T : 𝓓'(Ω, ℝ))
    (j : ℕ) (z : E) : ℝ :=
  T (TestFunction.ofSupportedIn D.cutoffCompact_subset
    (D.localizedKernelSupportedIn j z))

end LocalizedAdaptedKernel

/-- On a fixed compact set, a distribution is controlled by finitely many of the
standard derivative seminorms on smooth functions supported in that compact set.
@isnad1 id=ex.1h4v.s10.57231d8caaa8 from=translated src=- shape=a842b562 vocab=8ea12f91
-/
theorem exists_finite_seminorm_bound_on_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (K : Compacts E)
    (hKΩ : (K : Set E) ⊆ Ω) :
    ∃ (s : Finset ℕ) (C : ℝ≥0), C ≠ 0 ∧
      ∀ φ : ContDiffMapSupportedIn E ℝ ⊤ K,
        |T (TestFunction.ofSupportedIn hKΩ φ)| ≤
          (C : ℝ) *
            (s.sup (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) φ := by
  let TK := T.comp (TestFunction.ofSupportedInCLM ℝ hKΩ)
  let q : Seminorm ℝ (ContDiffMapSupportedIn E ℝ ⊤ K) :=
    (normSeminorm ℝ ℝ).comp TK.toLinearMap
  have hq : Continuous q := continuous_norm.comp TK.continuous
  obtain ⟨s, C, hC, hbound⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℝ E ℝ ⊤ K) q hq
  refine ⟨s, C, hC, fun φ ↦ ?_⟩
  have h := hbound φ
  change |T ((TestFunction.ofSupportedInCLM ℝ hKΩ) φ)| ≤
    (C : ℝ) * (s.sup (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) φ
  change |T ((TestFunction.ofSupportedInCLM ℝ hKΩ) φ)| ≤
    (C : ℝ) * (s.sup (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) φ at h
  exact h

/-- A distribution has finite order on every fixed compact subset of its domain:
one common derivative order controls its value on all smooth functions supported
in that compact set.
@isnad1 id=ex.1h4v.s10.db63aabea577 from=translated src=- shape=ccac18ac vocab=64fdc23c
-/
theorem exists_finite_order_seminorm_bound_on_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (K : Compacts E)
    (hKΩ : (K : Set E) ⊆ Ω) :
    ∃ (m : ℕ) (C : ℝ≥0), C ≠ 0 ∧
      ∀ φ : ContDiffMapSupportedIn E ℝ ⊤ K,
        |T (TestFunction.ofSupportedIn hKΩ φ)| ≤
          (C : ℝ) *
            ((Finset.Iic m).sup
              (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) φ := by
  obtain ⟨s, C, hC, hbound⟩ := exists_finite_seminorm_bound_on_compact T K hKΩ
  refine ⟨s.sup id, C, hC, fun φ ↦ (hbound φ).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  have hseminorm :
      s.sup (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K) ≤
        (Finset.Iic (s.sup id)).sup
          (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K) :=
    Finset.sup_mono s.subset_Iic_sup_id
  exact hseminorm φ

end PshLines.Regularization

import Tengoku.NavierStokesEuler.Euler.MeanCurlIntegration

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The localized weak Newtonian potential produces the source's actual curl field `w`.
Its complement is distributionally harmonic wherever the cutoff is one.
-/

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit EulerVectorCalculus
  EulerMeanSolenoidal EulerMeanCutoffCurl EulerMeanGradientTest EulerMeanBoundary
  EulerMeanCurlTensor EulerMeanVectorIdentities EulerMeanCurlIntegration
open scoped ContDiff

/-- Distributional harmonicity of an actual ordinary L² vector field on a set. -/
def WeakHarmonicOn (U : Set Space) (u : EulerMeanSolenoidal.L2) : Prop :=
  ∀ φ : Space → Space, HasCompactSupport φ → ContDiff ℝ ∞ φ →
    tsupport φ ⊆ U → (∫ x, ⟪u x, Δ φ x⟫_ℝ) = 0

/--
@isnad1 id=eq.0h2v.s13.dc0e50868012 from=translated src=- shape=ac43022c vocab=52b3a2cd
-/
theorem l2_test_pairing (u : L2) (f : Test) :
    ⟪u, testValue f⟫_ℝ = ∫ x, ⟪u x, (f : Space → Space) x⟫_ℝ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [testValue_ae f] with x hx
  rw [hx]

def divergenceGradient (f : Test) : L2 :=
  EulerMeanSolenoidal.testGradient (divergence (f : Space → Space))
    (divergence_compact f f.smooth f.compact) (divergence_smooth f f.smooth)

/--
@isnad1 id=eventual.0h1v.s12.e54b7a83ca19 from=translated src=- shape=35c6dd53 vocab=14f884d3
-/
theorem divergenceGradient_ae (f : Test) :
    divergenceGradient f =ᵐ[volume] gradient (divergence (f : Space → Space)) :=
  EulerMeanSolenoidal.testGradient_ae _ _ _

/--
@isnad1 id=mem.0h1v.s14.255695ade7f6 from=translated src=- shape=86238ede vocab=07dbcd95
-/
theorem divergenceGradient_mem (f : Test) : divergenceGradient f ∈ gradientSpace :=
  testGradient_mem _ _ _

/--
@isnad1 id=eq.0h1v.s14.c2c377db0672 from=translated src=- shape=0ecca779 vocab=1d2a38bf
-/
theorem testValue_curlcurl (f : Test) :
    testValue (curlTest (curlTest f)) = divergenceGradient f - testValue (laplacianTest f) := by
  apply Lp.ext
  filter_upwards [testValue_ae (curlTest (curlTest f)), divergenceGradient_ae f,
    testValue_ae (laplacianTest f), Lp.coeFn_sub (divergenceGradient f) (testValue (laplacianTest f))]
    with x hcc hg hl hs
  rw [hcc, hs]
  change vectorCurl (vectorCurl (f : Space → Space)) x =
    divergenceGradient f x - testValue (laplacianTest f) x
  rw [hg, hl, vectorCurl_vectorCurl f f.smooth]
  rfl

/--
@isnad1 id=eq.1h2v.s15.e15b59f56b30 from=translated src=- shape=a9f17be5 vocab=6c89702c
-/
theorem solenoidal_curlcurl_pairing (z : L2) (hz : z ∈ solenoidalSpace) (f : Test) :
    ⟪z, testValue (curlTest (curlTest f))⟫_ℝ = -⟪z, testValue (laplacianTest f)⟫_ℝ := by
  rw [testValue_curlcurl, inner_sub_right]
  have hg : ⟪z, divergenceGradient f⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hz (divergenceGradient f) (divergenceGradient_mem f)
  rw [hg, zero_sub]

/--
@isnad1 id=eq.2h3v.s11.c042e6443dc5 from=translated src=- shape=f4d86262 vocab=c682836d
-/
theorem cutoff_curlTest_eq (χ : Cutoff) (U : Set Space)
    (hχ : ∀ x ∈ U, χ.field x = 1) (f : Test) (hf : tsupport (f : Space → Space) ⊆ U) :
    (fun x => χ.field x • (curlTest f : Space → Space) x) = vectorCurl (f : Space → Space) := by
  funext x
  by_cases hx : x ∈ U
  · change χ.field x • vectorCurl (f : Space → Space) x = _
    rw [hχ x hx, one_smul]
  · have hs : x ∉ tsupport (vectorCurl (f : Space → Space)) :=
      fun h => hx (hf (vectorCurl_support f h))
    change χ.field x • vectorCurl (f : Space → Space) x = _
    rw [image_eq_zero_of_notMem_tsupport hs, smul_zero]

/-- The actual curl tensor of any homogeneous potential remains solenoidal.
@isnad1 id=mem.0h1v.s18.155e902497ea from=translated src=- shape=1612efa8 vocab=107c2a05
-/
theorem homogeneous_curl_solenoidal (u : homogeneousSpace) :
    curlTensor (u : GradientTensor) ∈ solenoidalSpace := by
  refine homogeneousGradient_dense.induction_on u ?_ ?_
  · exact gradientSpace.isClosed_orthogonal.preimage
      (curlTensor.continuous.comp continuous_subtype_val)
  · intro f
    change curlTensor (EulerMeanGradientTest.testGradient f) ∈ solenoidalSpace
    rw [curlTensor_test_eq]
    exact curl_mem_solenoidal _ ((contDiff_piLp 2).mp f.smooth) (test_memLp (curlTest f))

/--
@isnad1 id=mem.0h2v.s15.2cbc3f6f77af from=translated src=- shape=755866bc vocab=7c172cd7
-/
theorem harmonicPart_solenoidal (χ : Cutoff) (z : L2) :
    harmonicPart χ z ∈ solenoidalSpace := homogeneous_curl_solenoidal (weakPotential χ z)

/-- The source's `z - w` is genuinely weakly harmonic where the actual cutoff equals one.
@isnad1 id=weakharm.2h3v.s15.ffc82bd2ff5b from=translated src=- shape=4c9de9fc vocab=5d274cfa
-/
theorem weakHarmonicOn_sub_harmonicPart (χ : Cutoff) (U : Set Space) (z : L2)
    (hz : z ∈ solenoidalSpace) (hχ : ∀ x ∈ U, χ.field x = 1) :
    WeakHarmonicOn U (z - harmonicPart χ z) := by
  intro φ hc hs hsupport
  let f : Test := ⟨φ, hs, hc⟩
  have h₁ : ⟪weakPotential χ z, homogeneousGradient (curlTest f)⟫_ℝ =
      ⟪z, testValue (curlTest (curlTest f))⟫_ℝ := by
    rw [weakPotential_pairing, cutoff_curlTest_eq χ U hχ f hsupport, l2_test_pairing]
    rfl
  have h₂ := homogeneous_curl_pairing (weakPotential χ z) f
  have h₃ := solenoidal_curlcurl_pairing z hz f
  have hi : ⟪z - harmonicPart χ z, testValue (laplacianTest f)⟫_ℝ = 0 := by
    rw [inner_sub_left]
    change ⟪z, testValue (laplacianTest f)⟫_ℝ -
      ⟪curlTensor (weakPotential χ z : GradientTensor), testValue (laplacianTest f)⟫_ℝ = 0
    linarith
  exact (l2_test_pairing (z - harmonicPart χ z) (laplacianTest f)).symm.trans hi

/-- A quantitative decomposition constructed from the cutoff and the given solenoidal field.
@isnad1 id=ex.2h3v.s19.df1e78fff364 from=translated src=- shape=b2d1d67d vocab=381b7a9e
-/
theorem exists_weak_harmonic_decomposition (χ : Cutoff) (U : Set Space) (z : L2)
    (hz : z ∈ solenoidalSpace) (hχ : ∀ x ∈ U, χ.field x = 1) :
    ∃ w : L2, w = harmonicPart χ z ∧ w ∈ solenoidalSpace ∧
      ‖w‖ ≤ 6 * ‖weakPotential χ z‖ ∧ WeakHarmonicOn U (z - w) :=
  ⟨harmonicPart χ z, rfl, harmonicPart_solenoidal χ z, harmonicPart_norm_le χ z,
    weakHarmonicOn_sub_harmonicPart χ U z hz hχ⟩

end EulerMeanHarmonic

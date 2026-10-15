/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

-- Import our functional analysis utilities
module

-- Bochner library provides the cylinder σ-algebra MeasurableSpace instance on WeakDual
public import Tengoku.LeanPool.LeanPool.OSforGFF.Minlos.NuclearSpace
public import Tengoku
public import Tengoku.LeanPool.LeanPool.OSforGFF.General.FunctionalAnalysis

/-!
# Basic Definitions

Core type definitions for the formalization:

- `SpaceTime` = EuclideanSpace ℝ (Fin 4), the Euclidean 4-space ℝ⁴
- `OSforGFF.TestFunction` / `TestFunctionℂ` = real/complex Schwartz functions on ℝ⁴
- `FieldConfiguration` = tempered distributions S'(ℝ⁴) (WeakDual of Schwartz space)
- `distributionPairing` / `distributionPairingℂReal` = ⟨ω, f⟩ pairings
- `GJGeneratingFunctional` = Z[J] = ∫ exp(i⟨ω, J⟩) dμ(ω)
-/

@[expose] public section

/-- Spacetime dimension. Currently set to 4 (Euclidean ℝ⁴).
    Changing this value requires corresponding changes throughout the project;
    see `docs/dimension_dependence.md` for a detailed inventory.
-/
abbrev STDimension := 4
/-- The `SpaceTime` declaration. -/
abbrev SpaceTime := EuclideanSpace ℝ (Fin STDimension)

noncomputable instance : InnerProductSpace ℝ SpaceTime := by infer_instance

/-- The `getTimeComponent` declaration. -/
abbrev getTimeComponent (x : SpaceTime) : ℝ :=
 x ⟨0, by simp +arith⟩

open MeasureTheory NNReal ENNReal Complex
open TopologicalSpace Measure

-- Also open FunLike for SchwartzMap function application
open DFunLike (coe)

noncomputable section

variable {𝕜 : Type} [RCLike 𝕜]

/-- The `μ` declaration. -/
abbrev μ : Measure SpaceTime := volume    -- Lebesgue, just named “μ”

/- Distributions and test functions -/

/-- The `OSforGFF.TestFunction` declaration. -/
abbrev OSforGFF.TestFunction : Type := SchwartzMap SpaceTime ℝ
/-- Test functions over an arbitrary scalar field. -/
abbrev TestFunction𝕜 : Type := SchwartzMap SpaceTime 𝕜
/-- The `TestFunctionℂ` declaration. -/
abbrev TestFunctionℂ := TestFunction𝕜 (𝕜 := ℂ)

/- Space-time and test function setup -/

variable (x : SpaceTime)

/- Probability distribution over field configurations (distributions) -/
/-- Continuous bilinear pointwise multiplication on complex scalars. -/
def pointwiseMulCLM : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ

/-- Multiplication lifted to the Schwartz space. -/
def schwartzMul (g : TestFunctionℂ) : TestFunctionℂ →L[ℂ] TestFunctionℂ :=
  (SchwartzMap.bilinLeftCLM pointwiseMulCLM (SchwartzMap.hasTemperateGrowth_general g))

/-! ## Glimm-Jaffe Distribution Framework

The proper mathematical foundation for quantum field theory uses
tempered distributions as field configurations, following Glimm and Jaffe.
This section adds the distribution-theoretic definitions alongside
the existing L2 framework for comparison and gradual transition.
-/

/-- Field configurations as tempered distributions (dual to Schwartz space).
    This follows the Glimm-Jaffe approach where the field measure is supported
    on the space of distributions, not L2 functions.

    Using WeakDual gives the correct weak-* topology on the dual space.
-/
abbrev FieldConfiguration := WeakDual ℝ (SchwartzMap SpaceTime ℝ)

-- MeasurableSpace on FieldConfiguration = WeakDual ℝ OSforGFF.TestFunction
-- is the cylinder σ-algebra
-- provided by the bochner library: ⨆ f, (borel ℝ).comap (eval f)

/-- The fundamental pairing between a field configuration (distribution) and a test function.
    This is ⟨ω, f⟩ in the Glimm-Jaffe notation.

    Note: FieldConfiguration = WeakDual ℝ (SchwartzMap SpaceTime ℝ) has the correct
    weak-* topology, making evaluation maps x ↦ ω(x) continuous for each test function x.
-/
def distributionPairing (ω : FieldConfiguration) (f : OSforGFF.TestFunction) : ℝ := ω f

/--
@isnad1 id=eq.0h3v.s9.02b87781c4c2 from=translated src=- shape=897af36f vocab=92406ffc
-/
@[simp] lemma distributionPairing_add (ω₁ ω₂ : FieldConfiguration) (a : OSforGFF.TestFunction) :
    distributionPairing (ω₁ + ω₂) a = distributionPairing ω₁ a + distributionPairing ω₂ a := rfl

/--
@isnad1 id=eq.0h3v.s10.31084d03782a from=translated src=- shape=34fd784b vocab=e14c230d
-/
@[simp] lemma distributionPairing_smul (s : ℝ) (ω : FieldConfiguration)
    (a : OSforGFF.TestFunction) :
    distributionPairing (s • ω) a = s * distributionPairing ω a :=
  -- This follows from the definition of scalar multiplication in WeakDual
  rfl

/--
@isnad1 id=eq.0h3v.s10.1384da770097 from=translated src=- shape=d2411dc6 vocab=75e30ae3
-/
lemma pairing_smul_real (ω : FieldConfiguration) (s : ℝ) (a : OSforGFF.TestFunction) :
  ω (s • a) = s * (ω a) :=
  -- This follows from the linearity of the dual pairing
  map_smul ω s a

/-- The `distributionPairingCLM` declaration. -/
@[simp] def distributionPairingCLM (a : OSforGFF.TestFunction) : FieldConfiguration →L[ℝ] ℝ where
  toFun ω := distributionPairing ω a
  map_add' ω₁ ω₂ := by
    -- WeakDual addition is pointwise: (ω₁ + ω₂) a = ω₁ a + ω₂ a
    rfl
  map_smul' s ω := by
    -- WeakDual scalar multiplication is pointwise: (s • ω) a = s * (ω a)
    rfl
  cont := by
    -- The evaluation map is continuous by definition of WeakDual topology
    exact WeakDual.eval_continuous a

/--
@isnad1 id=eq.0h2v.s11.7fae86da8fdb from=translated src=- shape=66288e40 vocab=66d4291c
-/
lemma distributionPairingCLM_apply (a : OSforGFF.TestFunction) (ω : FieldConfiguration) :
    distributionPairingCLM a ω = distributionPairing ω a := rfl

variable [SigmaFinite μ]

/-! ## Glimm-Jaffe Generating Functional

The generating functional in the distribution framework:
Z[J] = ∫ exp(i⟨ω, J⟩) dμ(ω)
where the integral is over field configurations ω (distributions).
-/

/-- The Glimm-Jaffe generating functional: Z[J] = ∫ exp(i⟨ω, J⟩) dμ(ω)
    This is the fundamental object in constructive QFT.
-/
def GJGeneratingFunctional (dμ_config : ProbabilityMeasure FieldConfiguration)
  (J : OSforGFF.TestFunction) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (distributionPairing ω J : ℂ)) ∂dμ_config.toMeasure

/-- Helper function to create a Schwartz map from a complex test function by applying a
    continuous linear map.
    This factors out the common pattern for extracting real/imaginary parts.
-/
def schwartzCompCLM (f : TestFunctionℂ) (L : ℂ →L[ℝ] ℝ) : OSforGFF.TestFunction :=
  SchwartzMap.mk (fun x => L (f x)) (by
    -- L is a continuous linear map, hence smooth
    exact ContDiff.comp L.contDiff f.smooth'
  ) (by
    -- Polynomial growth: since |L(z)| ≤ ||L|| * |z|, derivatives are controlled
    intro k n
    obtain ⟨C, hC⟩ := f.decay' k n
    use C * ‖L‖
    intro x
    -- iteratedFDeriv of L ∘ f equals L.compContinuousMultilinearMap (iteratedFDeriv f)
    rw [show (fun y => L (f y)) = L ∘ f.toFun from rfl,
      ContinuousLinearMap.iteratedFDeriv_comp_left L f.smooth'.contDiffAt
        (WithTop.coe_le_coe.mpr le_top)]
    -- Use the norm bound: ‖L.compContinuousMultilinearMap m‖ ≤ ‖L‖ * ‖m‖
    calc ‖x‖ ^ k * ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ n f.toFun x)‖
        ≤ ‖x‖ ^ k * (‖L‖ * ‖iteratedFDeriv ℝ n f.toFun x‖) := by
          apply mul_le_mul_of_nonneg_left
          · exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le L _
          · exact pow_nonneg (norm_nonneg _) _
      _ = ‖L‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f.toFun x‖) := by ring
      _ ≤ ‖L‖ * C := by
          apply mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
      _ = C * ‖L‖ := by ring
  )

omit [SigmaFinite μ]

/-- Evaluate `schwartzCompCLM` pointwise.
@isnad1 id=eq.0h3v.s8.9c15a8a30059 from=translated src=- shape=6d3f928e vocab=3d1e8e36
-/
@[simp] lemma schwartz_comp_clm_apply (f : TestFunctionℂ) (L : ℂ →L[ℝ] ℝ) (x : SpaceTime) :
  (schwartzCompCLM f L) x = L (f x) := rfl

/-- Decompose a complex test function into its real and imaginary parts as real test functions.
    This is more efficient than separate extraction functions.
-/
def complexTestFunctionDecompose (f : TestFunctionℂ) :
    OSforGFF.TestFunction × OSforGFF.TestFunction :=
  (schwartzCompCLM f Complex.reCLM, schwartzCompCLM f Complex.imCLM)

/-- First component of the decomposition evaluates to the real part pointwise.
@isnad1 id=eq.0h2v.s7.d99682bc6291 from=translated src=- shape=c944137c vocab=b377b9c7
-/
@[simp] lemma complex_testfunction_decompose_fst_apply
  (f : TestFunctionℂ) (x : SpaceTime) :
  (complexTestFunctionDecompose f).1 x = (f x).re := by
  simp [complexTestFunctionDecompose]

/-- Second component of the decomposition evaluates to the imaginary part pointwise.
@isnad1 id=eq.0h2v.s7.6972270e8fac from=translated src=- shape=c944137c vocab=5dd6d5ea
-/
@[simp] lemma complex_testfunction_decompose_snd_apply
  (f : TestFunctionℂ) (x : SpaceTime) :
  (complexTestFunctionDecompose f).2 x = (f x).im := by
  simp [complexTestFunctionDecompose]

/-- Coerced-to-ℂ version (useful for complex-side algebra).
@isnad1 id=eq.0h2v.s7.9b9f015f8961 from=translated src=- shape=008a5389 vocab=a51cd546
-/
lemma complex_testfunction_decompose_fst_apply_coe
  (f : TestFunctionℂ) (x : SpaceTime) :
  ((complexTestFunctionDecompose f).1 x : ℂ) = ((f x).re : ℂ) := by
  simp [complexTestFunctionDecompose]

/-- Coerced-to-ℂ version (useful for complex-side algebra).
@isnad1 id=eq.0h2v.s7.85581bcae630 from=translated src=- shape=008a5389 vocab=c29b13c3
-/
lemma complex_testfunction_decompose_snd_apply_coe
  (f : TestFunctionℂ) (x : SpaceTime) :
  ((complexTestFunctionDecompose f).2 x : ℂ) = ((f x).im : ℂ) := by
  simp [complexTestFunctionDecompose]

/-- Recomposition at a point via the decomposition.
@isnad1 id=eq.0h2v.s8.760cd9dc0235 from=translated src=- shape=e34d7dab vocab=ac40a900
-/
lemma complex_testfunction_decompose_recompose
  (f : TestFunctionℂ) (x : SpaceTime) :
  f x = ((complexTestFunctionDecompose f).1 x : ℂ)
          + Complex.I * ((complexTestFunctionDecompose f).2 x : ℂ) := by
  -- Reduce to the standard identity z = re z + i im z
  simpa [mul_comm] using (Complex.re_add_im (f x)).symm

/-- Complex version of the pairing: real field configuration with complex test function
    We extend the pairing by treating the complex test function as f(x) = f_re(x) + i*f_im(x)
    and defining ⟨ω, f⟩ = ⟨ω, f_re⟩ + i*⟨ω, f_im⟩
-/
def distributionPairingℂReal (ω : FieldConfiguration) (f : TestFunctionℂ) : ℂ :=
  -- Extract real and imaginary parts using our efficient decomposition
  let ⟨f_re, f_im⟩ := complexTestFunctionDecompose f
  -- Pair with the real field configuration and combine
  (ω f_re : ℂ) + Complex.I * (ω f_im : ℂ)

/-- Complex version of the generating functional -/
def GJGeneratingFunctionalℂ (dμ_config : ProbabilityMeasure FieldConfiguration)
  (J : TestFunctionℂ) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (distributionPairingℂReal ω J)) ∂dμ_config.toMeasure

/-- The mean field in the Glimm-Jaffe framework -/
def GJMean (dμ_config : ProbabilityMeasure FieldConfiguration)
  (φ : OSforGFF.TestFunction) : ℝ :=
  ∫ ω, distributionPairing ω φ ∂dμ_config.toMeasure

/-! ## Spatial Geometry and Energy Operators -/

/-- Spatial coordinates: ℝ^{d-1} (space without time) as EuclideanSpace for L2 norm -/
abbrev SpatialCoords := EuclideanSpace ℝ (Fin (STDimension - 1))

/-- L² space on spatial slices (real-valued) -/
abbrev SpatialL2 := Lp ℝ 2 (volume : Measure SpatialCoords)

/-- Extract spatial part of spacetime coordinate -/
def spatialPart (x : SpaceTime) : SpatialCoords :=
  (EuclideanSpace.equiv (Fin (STDimension - 1)) ℝ).symm
    (fun i => x ⟨i.val + 1, by simp [STDimension]; omega⟩)

/-- The energy function `spatialEnergy m k = √(‖k‖² + m²)` on spatial momentum space. -/
def spatialEnergy (m : ℝ) (k : SpatialCoords) : ℝ :=
  Real.sqrt (‖k‖^2 + m^2)

end

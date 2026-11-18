import Tengoku.Seed.MeasureTheory.Measure.Haar.Unique
import Tengoku.Seed.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Tengoku.Seed.Topology.ContinuousMap.Compact
import Tengoku.Seed.MeasureTheory.Function.LocallyIntegrable
import Tengoku.XzMathieuSu2Counterexamples.XZMathieuSU2Counterexamples.Basic
import Tengoku.XzMathieuSu2Counterexamples.XZMathieuSU2Counterexamples.RepresentativeFunctions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Normalized Haar measure and integration on representative functions.
The representative-function correspondence is developed separately.
-/

noncomputable section

open MeasureTheory TopologicalSpace

namespace XZMathieuSU2Counterexamples

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Haar measure normalized on the entire compact group, not an arbitrary compact set.-/
def normalizedHaar : Measure G :=
  Measure.haarMeasure (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts G)

instance : (normalizedHaar G).IsHaarMeasure := by
  unfold normalizedHaar
  infer_instance

instance : IsProbabilityMeasure (normalizedHaar G) where
  measure_univ := Measure.haarMeasure_self

/-- Normalized Haar measure on a compact group is also right invariant.-/
instance : (normalizedHaar G).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    let ν := (normalizedHaar G).map (fun x => x * g)
    have hν : IsProbabilityMeasure ν :=
      Measure.isProbabilityMeasure_map_iff (continuous_id.mul continuous_const).measurable.aemeasurable
        |>.mpr inferInstance
    have h := Measure.isMulInvariant_eq_smul_of_compactSpace ν (normalizedHaar G)
    have hc : Measure.haarScalarFactor ν (normalizedHaar G) = 1 := by
      apply ENNReal.coe_injective
      have hu := congrArg (fun μ : Measure G => μ Set.univ) h
      simpa using hu.symm
    simpa [hc] using h

/-- Normalized Haar integration on continuous complex-valued functions.-/
def haarIntegral (f : C(G, ℂ)) : ℂ := ∫ g, f g ∂normalizedHaar G

/--
@isnad1 id=integrab.0h2v.s6.486ffc407771 from=translated src=- shape=1b1c0986 vocab=721f358e
-/
theorem haar_integrable (f : C(G, ℂ)) : Integrable f (normalizedHaar G) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Haar integration as a linear functional; compactness supplies integrability.-/
def haarIntegralLinear : C(G, ℂ) →ₗ[ℂ] ℂ where
  toFun := haarIntegral G
  map_add' f h := integral_add (haar_integrable G f) (haar_integrable G h)
  map_smul' c f := integral_smul c f

/-- Normalized Haar integration restricted to the actual representative algebra.-/
def representativeIntegral : representativeFunctions (G := G) →ₗ[ℂ] ℂ :=
  (haarIntegralLinear G).comp (representativeFunctions (G := G)).val.toLinearMap

/-- The exact Mathieu property of the compact group, on representative functions.-/
def HasMathieuProperty : Prop := IsMathieuSubspace (LinearMap.ker (representativeIntegral G))

/-- Fixed representative functions with vanishing pure and nonvanishing marked
moments refute the group Mathieu property.
@isnad1 id=not.2h3v.s12.7fbeee7950a2 from=translated src=- shape=2ca53598 vocab=bd385e0d
-/
theorem not_mathieu_of_representative_witness (f h : representativeFunctions (G := G))
    (hpure : ∀ m : ℕ, 1 ≤ m → representativeIntegral G (f ^ m) = 0)
    (hmarked : ∀ m : ℕ, 1 ≤ m → representativeIntegral G (h * f ^ m) ≠ 0) :
    ¬ HasMathieuProperty G :=
  not_isMathieuSubspace_of_witness (LinearMap.ker (representativeIntegral G)) f h hpure hmarked

/--
@isnad1 id=eq.0h1v.s11.78f43b7f6581 from=translated src=- shape=99a6c6d9 vocab=7b5a7d23
-/
theorem representativeIntegral_one : representativeIntegral G 1 = 1 := by
  change (∫ _ : G, (1 : ℂ) ∂normalizedHaar G) = 1
  simp

variable {G} {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [MeasurableSpace H] [BorelSpace H]

/--
@isnad1 id=eq.2h3v.s7.f53ba93b0119 from=translated src=- shape=26d38585 vocab=69fea357
-/
theorem map_normalizedHaar (π : G →* H) (hπ : Continuous π) (hs : Function.Surjective π) :
    Measure.map π (normalizedHaar G) = normalizedHaar H :=
  (π.measurePreserving hπ hs (by simp)).map_eq

/-- The exact normalized integral pullback identity for continuous functions.
@isnad1 id=eq.2h4v.s8.efc99b32b01e from=translated src=- shape=f070a011 vocab=a89c69c9
-/
theorem haar_pullback (π : G →* H) (hπ : Continuous π) (hs : Function.Surjective π)
    (f : C(H, ℂ)) :
    (∫ g, f (π g) ∂normalizedHaar G) = ∫ h, f h ∂normalizedHaar H := by
  rw [← map_normalizedHaar π hπ hs]
  exact (integral_map_of_stronglyMeasurable hπ.measurable
    f.continuous.stronglyMeasurable).symm

/-- Manuscript-facing pullback identity on representative functions.
@isnad1 id=eq.2h4v.s12.79fcb82740e1 from=translated src=- shape=ac00c4fa vocab=81879ccd
-/
theorem representativeIntegral_pullback (π : G →* H) (hπ : Continuous π)
    (hs : Function.Surjective π) (f : representativeFunctions (G := H)) :
    representativeIntegral G (representativePullback π hπ f) = representativeIntegral H f :=
  haar_pullback π hπ hs f.val

/-- The Mathieu property passes to a continuous surjective group quotient.
@isnad1 id=hasmathi.3h3v.s7.6fc6b943ff7d from=translated src=- shape=6eacf2cd vocab=12807d5d
-/
theorem HasMathieuProperty.of_surjective (hG : HasMathieuProperty G)
    (π : G →* H) (hπ : Continuous π) (hs : Function.Surjective π) : HasMathieuProperty H := by
  have hker : LinearMap.ker (representativeIntegral H) =
      (LinearMap.ker (representativeIntegral G)).comap (representativePullback π hπ).toLinearMap := by
    ext f
    simp only [LinearMap.mem_ker, Submodule.mem_comap, AlgHom.toLinearMap_apply,
      representativeIntegral_pullback π hπ hs]
  unfold HasMathieuProperty
  rw [hker]
  exact IsMathieuSubspace.comap (A := representativeFunctions (G := H))
    (B := representativeFunctions (G := G)) hG (representativePullback π hπ)

/-- A quotient which fails the Mathieu property forces the source to fail it too.
@isnad1 id=not.3h3v.s7.f053ff1ca6df from=translated src=- shape=f5029b78 vocab=12807d5d
-/
theorem not_mathieuProperty_of_quotient (π : G →* H) (hπ : Continuous π)
    (hs : Function.Surjective π) (hH : ¬ HasMathieuProperty H) : ¬ HasMathieuProperty G :=
  fun hG => hH (hG.of_surjective π hπ hs)

/-- The fixed witnesses themselves pull back, with no representative-function
closure or integration hypotheses left to discharge.
@isnad1 id=not.4h5v.s13.790253dd1b77 from=translated src=- shape=4234d2d5 vocab=bb6ffd7c
-/
theorem representative_counterexample_pullback (π : G →* H) (hπ : Continuous π)
    (hs : Function.Surjective π) (f h : representativeFunctions (G := H))
    (hpure : ∀ m : ℕ, 1 ≤ m → representativeIntegral H (f ^ m) = 0)
    (hmarked : ∀ m : ℕ, 1 ≤ m → representativeIntegral H (h * f ^ m) ≠ 0) :
    ¬ HasMathieuProperty G :=
  counterexample_pullback (A := representativeFunctions (G := H))
    (B := representativeFunctions (G := G)) (representativePullback π hπ) (representativeIntegral H)
    (representativeIntegral G) (representativeIntegral_pullback π hπ hs) f h hpure hmarked

end XZMathieuSU2Counterexamples

/- Adapted from MathieuProperty/Haar.lean at d7199cfcc342b3e0c332982740d1f3beecf01ab8.
Copyright (c) 2026 long-mathematics; MIT license, see LICENSE. -/

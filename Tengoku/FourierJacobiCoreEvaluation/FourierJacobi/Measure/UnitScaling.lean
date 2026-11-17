import Tengoku.FourierJacobiCoreEvaluation.FourierJacobi.Measure.MultiplicativeHaar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The actual additive Haar scaling character of every nonzero local-field scalar. -/

noncomputable section

open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal NNReal Pointwise

namespace FourierJacobi.Measure

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/--
@isnad1 id=t2space.0h1v.s4.7e1ccb55d0cf from=translated src=- shape=7ddc04c7 vocab=d124730f
-/
local instance unitScaling_t2Space : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/--
@isnad1 id=eq.1h2v.s8.896f54629c2d from=translated src=- shape=0d25a763 vocab=31611861
-/
theorem valuationRingUnits_smul_integers (u : Kˣ) (hu : u ∈ valuationRingUnits K) :
    u • (𝒪[K] : Set K) = (𝒪[K] : Set K) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · intro hx
    have h := (𝒪[K]).mul_mem hu.1 hx
    change (u : K) * (((u⁻¹ : Kˣ) : K) * x) ∈ 𝒪[K] at h
    simpa only [SetLike.mem_coe, ← mul_assoc, Units.mul_inv, one_mul] using h
  · intro hx
    exact (𝒪[K]).mul_mem hu.2 hx

variable [MeasurableSpace K] [BorelSpace K]

/--
@isnad1 id=regular.0h1v.s5.d16cac4bed37 from=translated src=- shape=21c02aa3 vocab=861596bc
-/
local instance unitScaling_additiveHaar_regular : (additiveHaar K).Regular := by
  unfold additiveHaar
  infer_instance

/--
@isnad1 id=eq.1h2v.s8.854624dee5f3 from=translated src=- shape=890a36b1 vocab=f42d777e
-/
theorem distribHaarChar_valuationRingUnits (u : Kˣ) (hu : u ∈ valuationRingUnits K) :
    distribHaarChar K u = 1 := by
  have h := distribHaarChar_mul (additiveHaar K) u (𝒪[K] : Set K)
  rw [valuationRingUnits_smul_integers K u hu, additiveHaar_integers, mul_one] at h
  exact ENNReal.coe_injective h

/-- The additive Haar scaling character is derived for every actual scalar,
using its canonical integer valuation; no scaling law is assumed.
@isnad1 id=eq.1h3v.s8.5cb2966d71c4 from=translated src=- shape=83839eff vocab=f70b7b53
-/
theorem distribHaarChar_eq_of_canonicalValuation (u : Kˣ) (n : ℤ)
    (hu : localFieldValuation K (u : K) = (n : WithTop ℤ)) :
    distribHaarChar K u = ((residueCardinality K : ℝ≥0)⁻¹) ^ n := by
  obtain ⟨π, hπ⟩ := exists_integral_canonical_uniformizer K
  have hs : u ∈ unitValuationShell K n := hu
  rw [unitValuationShell_eq_uniformizer_smul K π hπ n] at hs
  obtain ⟨v, hv, rfl⟩ := Set.mem_smul_set.mp hs
  simp only [smul_eq_mul, map_mul, map_zpow,
    canonicalUniformizer_distribHaarChar K π hπ,
    distribHaarChar_valuationRingUnits K v hv, mul_one]

/--
@isnad1 id=eq.1h4v.s8.10cc85fcfd48 from=translated src=- shape=8f291c7e vocab=ff9cce57
-/
theorem additiveHaar_smul_of_canonicalValuation (u : Kˣ) (n : ℤ)
    (hu : localFieldValuation K (u : K) = (n : WithTop ℤ)) (s : Set K) :
    additiveHaar K (u • s) =
      (↑(((residueCardinality K : ℝ≥0)⁻¹) ^ n) : ℝ≥0∞) * additiveHaar K s := by
  rw [← distribHaarChar_mul, distribHaarChar_eq_of_canonicalValuation K u n hu]

/--
@isnad1 id=eq.1h3v.s7.7c8137d71c79 from=translated src=- shape=70a26666 vocab=0899a9ea
-/
theorem additiveHaar_smul_valuationRingUnits (u : Kˣ)
    (hu : u ∈ valuationRingUnits K) (s : Set K) :
    additiveHaar K (u • s) = additiveHaar K s := by
  rw [← distribHaarChar_mul, distribHaarChar_valuationRingUnits K u hu]
  simp only [ENNReal.coe_one, one_mul]

/--
@isnad1 id=eq.1h4v.s7.84d5a0151bb6 from=translated src=- shape=7e354982 vocab=132c4f1f
-/
theorem additiveHaar_real_smul_of_canonicalValuation (u : Kˣ) (n : ℤ)
    (hu : localFieldValuation K (u : K) = (n : WithTop ℤ)) (s : Set K) :
    (additiveHaar K).real (u • s) =
      (residueCardinality K : ℝ) ^ (-n) * (additiveHaar K).real s := by
  rw [Measure.real, additiveHaar_smul_of_canonicalValuation K u n hu,
    ENNReal.toReal_mul, ENNReal.coe_toReal]
  simp only [NNReal.coe_zpow, NNReal.coe_inv, NNReal.coe_natCast, inv_zpow, zpow_neg]
  rfl

end FourierJacobi.Measure

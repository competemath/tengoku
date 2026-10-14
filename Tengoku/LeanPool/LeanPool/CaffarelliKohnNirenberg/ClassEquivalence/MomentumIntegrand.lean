/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.DivergenceFreeIntegrand

/-!
# The integrand of the weak momentum identity

The weak momentum clause of `def:sws` pairs an identity with an integrability
side condition on its integrand, stated on the closed support of the
vector-valued test field `φ`.  The integrand has five terms: the time
derivative term `uᵢ ∂ₜφᵢ`, the nonlinear term `uᵢ uⱼ ∂ⱼφᵢ`, the viscous term
`Duᵢⱼ ∂ⱼφᵢ`, the pressure term `p ∂ᵢφᵢ` and the force term `fᵢ φᵢ`.

This file proves that side condition from the data clauses alone.  The closed
support is compact, so Lebesgue measure restricted to it is finite; on a finite
measure every exponent above `1` is integrable, and a product of two square
integrable factors is integrable by the Cauchy-Schwarz inequality.  That is all
the nonlinear term needs: no parabolic interpolation enters here, because the
test field confines the integral to a set of finite measure.  Each term is then
an integrable field times a bounded derivative of the test field.

Nothing about the identities of `def:sws` is used, so the conclusion is
available while those identities are still being established.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

variable {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
variable {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
variable {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}

/-! ### Components of a vector-valued test field -/

/-- Each component of a vector-valued space-time test field is a scalar
space-time test field on the same carrier.
@isnad1 id=mem.1h4v.s7.cf6515d7b978 from=translated src=- shape=a507cde1 vocab=0273f64a
-/
theorem component_mem_spaceTimeTestFunction {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) Ω I) (i : Fin 3) :
    (fun w : Vec3 × ℝ => φ w i) ∈ spaceTimeTestFunction (V := ℝ) Ω I := by
  obtain ⟨hd, hc, hs⟩ := hφ
  refine ⟨(ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).contDiff.comp hd, ?_, ?_⟩
  · exact hc.comp_left (g := fun v : Vec3 => v i) rfl
  · exact (tsupport_component_subset φ i fun z hz => by rw [hz]; rfl).trans hs

/-! ### The fields of the momentum integrand on a compact set -/

variable {K : Set ParabolicPoint}

/-- A product of two velocity components is integrable on a compact subset of
the carrier: both factors are square integrable there, and the Cauchy-Schwarz
inequality pairs the exponents `2` and `2` into `1`.
@isnad1 id=integrab.3h10v.s6.d222afad2a23 from=translated src=- shape=09141d5c vocab=78c6cf0d
-/
theorem velocity_pair_integrableOn_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) (i j : Fin 3) :
    IntegrableOn (fun z => u z i * u z j) K volume := by
  have hu : MemLp u 2 (volume.restrict K) :=
    velocity_memLp_two_on_compact_of_data hdata hK hKsub
  exact (hu.continuousLinearMap_comp (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)).integrable_mul
    (hu.continuousLinearMap_comp (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ))

/-- Each entry of the velocity gradient is integrable on a compact subset of
the carrier.
@isnad1 id=integrab.3h10v.s6.4f63a2ca6aa8 from=translated src=- shape=eea65e73 vocab=7582742f
-/
theorem gradient_entry_integrableOn_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) (i j : Fin 3) :
    IntegrableOn (fun z => Du z i j) K volume := by
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict_of_isCompact hK
  exact (((gradient_memLp_two_on_compact_of_data hdata hK hKsub).continuousLinearMap_comp
    (ContinuousLinearMap.proj i : (Fin 3 → Vec3) →L[ℝ] Vec3)).continuousLinearMap_comp
    (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)).integrable (by norm_num)

/-- The pressure is integrable on a compact subset of the carrier: it is
`L^{3/2}` there and the restricted measure is finite.
@isnad1 id=integrab.3h8v.s6.e0233ce1820b from=translated src=- shape=0ab8d3e8 vocab=7582742f
-/
theorem pressure_integrableOn_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) :
    IntegrableOn p K volume := by
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict_of_isCompact hK
  refine (pressure_memLp_threeHalves_on_compact_of_data hdata hK hKsub).integrable ?_
  rw [ENNReal.one_le_ofReal]
  norm_num

/-- Each component of the force is integrable on a compact subset of the
carrier: it is `L^q` there with `q > 5 / 2 > 1`, and the restricted measure is
finite.
@isnad1 id=integrab.3h9v.s6.226094cc6055 from=translated src=- shape=b9bf4be5 vocab=7582742f
-/
theorem force_component_integrableOn_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) (i : Fin 3) :
    IntegrableOn (fun z => f z i) K volume := by
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict_of_isCompact hK
  refine ((force_memLp_on_compact_of_data hdata hK hKsub).continuousLinearMap_comp
    (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)).integrable ?_
  rw [ENNReal.one_le_ofReal]
  linarith only [hdata.five_halves_lt_exponent]

/-! ### The five terms of the momentum integrand -/

section Terms

variable (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
  (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I)
  {φ : Vec3 × ℝ → Vec3} (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) Ω I)

include hdata hK hKsub hφ

/-- The time-derivative term of the momentum integrand is integrable on a
compact subset of the carrier.
@isnad1 id=integrab.4h9v.s8.5d2672607b04 from=translated src=- shape=f069bf4b vocab=0ad41f9a
-/
theorem momentum_timeTerm_integrableOn_of_data :
    IntegrableOn (fun z => ∑ i, u z i * timePartial (fun w => φ w i) z) K volume := by
  refine integrable_finsetSum Finset.univ fun i _ => ?_
  have hcomp := component_mem_spaceTimeTestFunction hφ i
  obtain ⟨C, hC⟩ := exists_bound_timePartial_of_mem_spaceTimeTestFunction hcomp
  exact (velocity_component_integrableOn_compact_of_data hdata hK hKsub i).mul_bdd
    (c := C) (g := fun z : ParabolicPoint => timePartial (fun w => φ w i) z)
    (contDiff_timePartial hcomp.1).continuous.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => hC z)

/-- The nonlinear term of the momentum integrand is integrable on a compact
subset of the carrier.
@isnad1 id=integrab.4h9v.s8.b36ef9902cd8 from=translated src=- shape=86ea4822 vocab=468df46a
-/
theorem momentum_nonlinearTerm_integrableOn_of_data :
    IntegrableOn
      (fun z => ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z) K volume := by
  refine integrable_finsetSum Finset.univ fun i _ => ?_
  refine integrable_finsetSum Finset.univ fun j _ => ?_
  have hcomp := component_mem_spaceTimeTestFunction hφ i
  obtain ⟨C, hC⟩ := exists_bound_spatialPartial_of_mem_spaceTimeTestFunction hcomp j
  exact (velocity_pair_integrableOn_compact_of_data hdata hK hKsub i j).mul_bdd
    (c := C) (g := fun z : ParabolicPoint => spatialPartial (fun w => φ w i) j z)
    (spatialPartial_contDiff hcomp.1 j).continuous.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => hC z)

/-- The viscous term of the momentum integrand is integrable on a compact
subset of the carrier.
@isnad1 id=integrab.4h9v.s8.70ef4c8b8d21 from=translated src=- shape=b0040a83 vocab=468df46a
-/
theorem momentum_viscousTerm_integrableOn_of_data :
    IntegrableOn
      (fun z => ∑ i, ∑ j, Du z i j * spatialPartial (fun w => φ w i) j z) K volume := by
  refine integrable_finsetSum Finset.univ fun i _ => ?_
  refine integrable_finsetSum Finset.univ fun j _ => ?_
  have hcomp := component_mem_spaceTimeTestFunction hφ i
  obtain ⟨C, hC⟩ := exists_bound_spatialPartial_of_mem_spaceTimeTestFunction hcomp j
  exact (gradient_entry_integrableOn_compact_of_data hdata hK hKsub i j).mul_bdd
    (c := C) (g := fun z : ParabolicPoint => spatialPartial (fun w => φ w i) j z)
    (spatialPartial_contDiff hcomp.1 j).continuous.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => hC z)

/-- The pressure term of the momentum integrand is integrable on a compact
subset of the carrier.
@isnad1 id=integrab.4h9v.s8.c73ad8c06914 from=translated src=- shape=68ea6316 vocab=468df46a
-/
theorem momentum_pressureTerm_integrableOn_of_data :
    IntegrableOn
      (fun z => p z * ∑ i, spatialPartial (fun w => φ w i) i z) K volume := by
  have hterms : IntegrableOn
      (fun z => ∑ i, p z * spatialPartial (fun w => φ w i) i z) K volume := by
    refine integrable_finsetSum Finset.univ fun i _ => ?_
    have hcomp := component_mem_spaceTimeTestFunction hφ i
    obtain ⟨C, hC⟩ := exists_bound_spatialPartial_of_mem_spaceTimeTestFunction hcomp i
    exact (pressure_integrableOn_compact_of_data hdata hK hKsub).mul_bdd
      (c := C) (g := fun z : ParabolicPoint => spatialPartial (fun w => φ w i) i z)
      (spatialPartial_contDiff hcomp.1 i).continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hC z)
  simpa only [← Finset.mul_sum] using hterms

/-- The force term of the momentum integrand is integrable on a compact subset
of the carrier.
@isnad1 id=integrab.4h9v.s8.bf26fb69bc3e from=translated src=- shape=75cf9ab3 vocab=f94c4678
-/
theorem momentum_forceTerm_integrableOn_of_data :
    IntegrableOn (fun z => ∑ i, f z i * φ z i) K volume := by
  refine integrable_finsetSum Finset.univ fun i _ => ?_
  have hcomp := component_mem_spaceTimeTestFunction hφ i
  obtain ⟨C, hC⟩ := exists_bound_of_mem_spaceTimeTestFunction hcomp
  exact (force_component_integrableOn_compact_of_data hdata hK hKsub i).mul_bdd
    (c := C) (g := fun z : ParabolicPoint => φ z i)
    hcomp.1.continuous.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => hC z)

end Terms

/-! ### The momentum integrand -/

/-- The integrand of the weak momentum clause of `def:sws` is integrable on the
closed support of the test field.  Only the data clauses are used.
@isnad1 id=integrab.2h8v.s9.fd82563c6720 from=translated src=- shape=f031558b vocab=ec5d998a
-/
theorem momentum_integrand_integrableOn_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {φ : Vec3 × ℝ → Vec3} (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) Ω I) :
    IntegrableOn (fun z =>
        (-(∑ i, u z i * timePartial (fun w => φ w i) z))
          - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
          + ∑ i, ∑ j, (Du z i j) * spatialPartial (fun w => φ w i) j z
          - p z * ∑ i, spatialPartial (fun w => φ w i) i z
          - ∑ i, f z i * φ z i) (tsupport φ) volume := by
  have hK : IsCompact (tsupport (show ParabolicPoint → Vec3 from φ)) :=
    isCompact_tsupport_parabolic hφ.2.1
  have hKsub : tsupport (show ParabolicPoint → Vec3 from φ) ⊆ spaceTimeSet Ω I :=
    tsupport_parabolic_subset_spaceTimeSet hφ
  exact ((((momentum_timeTerm_integrableOn_of_data hdata hK hKsub hφ).neg.sub
    (momentum_nonlinearTerm_integrableOn_of_data hdata hK hKsub hφ)).add
    (momentum_viscousTerm_integrableOn_of_data hdata hK hKsub hφ)).sub
    (momentum_pressureTerm_integrableOn_of_data hdata hK hKsub hφ)).sub
    (momentum_forceTerm_integrableOn_of_data hdata hK hKsub hφ)

end CKN

import Tengoku.OpenaiMath.OAI.Geometry.PinnedDistances.VarianceRates

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12
universe u13 u14

section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace WeakPinned.Bounded

variable {E : Type u1} {X : Type u2} {J : Type u3} [MeasurableSpace E] [MeasurableSpace X]
  [TopologicalSpace E] [TopologicalSpace X] [BorelSpace E] [BorelSpace X]
  [SecondCountableTopology E] [SecondCountableTopology X]
  [HasOuterApproxClosed E] [HasOuterApproxClosed X] [Fintype J]

omit [SecondCountableTopology E] in
lemma weak_product_limit
    (Rn : ℕ → ProbabilityMeasure (E × (J → X))) (R : ProbabilityMeasure (E × (J → X)))
    (Qn : ℕ → ProbabilityMeasure E) (Q : ProbabilityMeasure E)
    (αn : ℕ → J → ProbabilityMeasure X) (β : J → ProbabilityMeasure X)
    (hR : Tendsto Rn atTop (𝓝 R)) (hQ : Tendsto Qn atTop (𝓝 Q))
    (hα : ∀ j,Tendsto (fun n => αn n j) atTop (𝓝 (β j)))
    (herr : ∀ (f : E →ᵇ ℝ) (g : J → X →ᵇ ℝ),
      Tendsto (fun n => (∫ p,f p.1*(∏ j,g j (p.2 j)) ∂ (Rn n : Measure (E × (J → X))))-
        (∫ e,f e ∂ (Qn n : Measure E))*(∏ j,∫ x,g j x ∂ (αn n j : Measure X))) atTop (𝓝 0)) :
    (R : Measure (E × (J → X)))=(Q : Measure E).prod (Measure.pi (fun j => (β j : Measure X))) := by
  apply Measure.eq_prod_of_integral_mul_prod_boundedContinuousFunction
  intro f g
  let F : E × (J → X) →ᵇ ℝ :=
    f.compContinuous ⟨Prod.fst,continuous_fst⟩ *
      ∏ j,(g j).compContinuous ⟨fun p : E × (J → X) => p.2 j,by fun_prop⟩
  have hRf := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hR F
  have hQf := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hQ f
  have hβg (j) := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp (hα j) (g j)
  have ht := hRf.sub (hQf.mul (tendsto_finsetProd Finset.univ (fun j _ => hβg j)))
  have hF (p : E × (J → X)) : F p=f p.1 * ∏ j,g j (p.2 j) := by simp [F]
  simp only [hF] at ht
  have he := tendsto_nhds_unique ht (herr f g)
  rw [integral_fintype_prod_eq_prod]
  exact sub_eq_zero.mp he

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace WeakPinned.Bounded

lemma weak_pair_product_limit {X : Type u4} {Y : Type u5} [MeasurableSpace X] [MeasurableSpace Y]
    [TopologicalSpace X] [TopologicalSpace Y] [BorelSpace X] [BorelSpace Y]
    [HasOuterApproxClosed X] [HasOuterApproxClosed Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    (Rn : ℕ → ProbabilityMeasure (X × Y)) (R : ProbabilityMeasure (X × Y))
    (μn : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (νn : ℕ → ProbabilityMeasure Y) (ν : ProbabilityMeasure Y)
    (hR : Tendsto Rn atTop (𝓝 R)) (hμ : Tendsto μn atTop (𝓝 μ)) (hν : Tendsto νn atTop (𝓝 ν))
    (herr : ∀ (f : X →ᵇ ℝ) (g : Y →ᵇ ℝ),
      Tendsto (fun n => (∫ p,f p.1*g p.2 ∂ (Rn n : Measure (X × Y)))-
        (∫ x,f x ∂ (μn n : Measure X))*(∫ y,g y ∂ (νn n : Measure Y))) atTop (𝓝 0)) :
    (R : Measure (X × Y))=(μ : Measure X).prod (ν : Measure Y) := by
  apply Measure.eq_prod_of_integral_mul_boundedContinuousFunction
  intro f g
  let F : X × Y →ᵇ ℝ := f.compContinuous ⟨Prod.fst,continuous_fst⟩ *
    g.compContinuous ⟨Prod.snd,continuous_snd⟩
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hR F).sub
    ((ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ f).mul
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν g))
  exact sub_eq_zero.mp (tendsto_nhds_unique ht (herr f g))

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace WeakPinned.Bounded

variable {E : Type u9} {X : Type u10} {T : Type u11} [MeasurableSpace E] [MeasurableSpace X] [MeasurableSpace T]
  [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace T]
  [BorelSpace E] [BorelSpace X] [BorelSpace T]
  [SecondCountableTopology E] [SecondCountableTopology X]
  [HasOuterApproxClosed E] [HasOuterApproxClosed X]

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal BoundedContinuousFunction
namespace WeakPinned.Bounded

variable {X : Type u12} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X]

lemma measure_le_of_continuous_lintegral (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : X →ᵇ ℝ≥0,(∫⁻ x,f x ∂ μ)≤∫⁻ x,f x ∂ ν) : μ≤ν := by
  have hclosed (K : Set X) (hK : IsClosed K) : μ K≤ν K := by
    exact le_of_tendsto_of_tendsto
      (HasOuterApproxClosed.tendsto_lintegral_apprSeq hK μ)
      (HasOuterApproxClosed.tendsto_lintegral_apprSeq hK ν)
      (Eventually.of_forall (fun n => h (hK.apprSeq n)))
  apply Measure.le_iff.mpr
  intro s hs
  rw [hs.measure_eq_iSup_isClosed_of_ne_top (measure_ne_top μ s)]
  exact iSup_le (fun K => iSup_le (fun hKs => iSup_le (fun hK => (hclosed K hK).trans (measure_mono hKs))))

lemma weak_domination (μn νn : ℕ → ProbabilityMeasure X) (μ ν : ProbabilityMeasure X)
    (hμ : Tendsto μn atTop (𝓝 μ)) (hν : Tendsto νn atTop (𝓝 ν)) (c : ℝ≥0)
    (hle : ∀ n,(μn n : Measure X)≤(c:ℝ≥0∞) • (νn n : Measure X)) :
    (μ : Measure X)≤(c:ℝ≥0∞) • (ν : Measure X) := by
  have : IsFiniteMeasure ((c:ℝ≥0∞) • (ν:Measure X)) := (ν:Measure X).smul_finite ENNReal.coe_ne_top
  apply measure_le_of_continuous_lintegral
  intro f
  have hμf := ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mp hμ f
  have hνf := ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mp hν f
  rw [lintegral_smul_measure]
  apply le_of_tendsto_of_tendsto hμf
    (ENNReal.Tendsto.const_mul hνf (Or.inr ENNReal.coe_ne_top))
  filter_upwards [] with n
  simpa only [lintegral_smul_measure,smul_eq_mul] using lintegral_mono' (hle n) (le_refl (fun x => (f x:ℝ≥0∞)))

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace WeakPinned.Bounded
variable {X : Type u13} {Y : Type u14} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace X] [TopologicalSpace Y] [BorelSpace X] [BorelSpace Y]
  [HasOuterApproxClosed Y]

end WeakPinned.Bounded

end
end

end OAI

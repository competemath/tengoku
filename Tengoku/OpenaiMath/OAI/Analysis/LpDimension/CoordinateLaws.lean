import Tengoku.OpenaiMath.OAI.Analysis.LpDimension.RampRetraction

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace
universe u uE

namespace SubpolynomialLp

variable {E : Type uE}

def coordinateLaw (μ : Measure (E → ℝ)) (e : E) : Measure ℝ := μ.map (fun v => v e)

lemma coordinateLaw_integral (μ : Measure (E → ℝ)) (e : E) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂coordinateLaw μ e) = ∫ v, f (v e) ∂μ :=
  integral_map (measurable_pi_apply e).aemeasurable hf.aestronglyMeasurable

lemma coordinateLaw_abs_moment (μ : Measure (E → ℝ)) (e : E) (p : ℝ) :
    (∫ x, |x|^p ∂coordinateLaw μ e) = ∫ v, |v e|^p ∂μ :=
  coordinateLaw_integral μ e _ (by fun_prop)

lemma coordinateLaw_sq_moment (μ : Measure (E → ℝ)) (e : E) :
    (∫ x, x^2 ∂coordinateLaw μ e) = ∫ v, (v e)^2 ∂μ :=
  coordinateLaw_integral μ e _ (by fun_prop)

lemma coordinateLaw_exp_moment (μ : Measure (E → ℝ)) (e : E) (s J : ℝ) :
    (∫ x, Real.exp (s*x/J) ∂coordinateLaw μ e) = ∫ v, Real.exp (s*v e/J) ∂μ :=
  coordinateLaw_integral μ e _ (by fun_prop)

lemma coordinateLaw_integrable (μ : Measure (E → ℝ)) (e : E) (f : ℝ → ℝ) (hf : Measurable f) :
    Integrable f (coordinateLaw μ e) ↔ Integrable (fun v => f (v e)) μ :=
  integrable_map_measure hf.aestronglyMeasurable (measurable_pi_apply e).aemeasurable

lemma coordinateLaw_ae (μ : Measure (E → ℝ)) (e : E) (P : ℝ → Prop)
    (hP : MeasurableSet {x | P x}) : (∀ᵐ x ∂coordinateLaw μ e, P x) ↔ ∀ᵐ v ∂μ, P (v e) :=
  ae_map_iff (measurable_pi_apply e).aemeasurable hP

lemma coordinateLaw_symmetric (μ : Measure (E → ℝ))
    (hs : μ.map (fun v => -v)=μ) (e : E) : (coordinateLaw μ e).map (fun x => -x)=coordinateLaw μ e := by
  rw [coordinateLaw,Measure.map_map (by fun_prop) (by fun_prop)]
  have hh := congrArg (fun ν : Measure (E → ℝ) => ν.map (fun v => v e)) hs
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hh
  exact hh

lemma convolutionPower_submodule [Fintype E] (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ]
    (V : Submodule ℝ (E → ℝ)) (hμ : ∀ᵐ v ∂μ, v ∈ V) (n : ℕ) :
    ∀ᵐ v ∂convolutionPower μ n, v ∈ V := by
  have hV : MeasurableSet (V : Set (E → ℝ)) := V.closed_of_finiteDimensional.measurableSet
  induction n with
  | zero => simp [convolutionPower]
  | succ n ih =>
    rw [convolutionPower,Measure.conv]
    apply (ae_map_iff (show AEMeasurable (fun x : (E → ℝ) × (E → ℝ) => x.1+x.2) _ by fun_prop)
      (show MeasurableSet {v : E → ℝ | v ∈ V} from hV)).mpr
    apply (Measure.ae_prod_iff_ae_ae (p := fun z : (E → ℝ) × (E → ℝ) => z.1+z.2 ∈ V)
      (hV.preimage (by fun_prop))).mpr
    exact ih.mono (fun x hx => hμ.mono (fun y hy => V.add_mem hx hy))

lemma bounded_coordinate_power_integrable (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ]
    (e : E) (p B : ℝ) (hp : 0 ≤ p) (hB : ∀ᵐ v ∂μ, |v e| ≤ B) :
    Integrable (fun v => |v e|^p) μ := by
  apply Integrable.of_bound (show Measurable (fun v : E → ℝ => |v e|^p) by fun_prop).aestronglyMeasurable (|B|^p)
  filter_upwards [hB] with v hv
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) (hv.trans (le_abs_self B)) hp

end SubpolynomialLp

end

end OAI

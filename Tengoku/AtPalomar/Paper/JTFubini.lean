module

public import Tengoku.AtPalomar.Paper.JTVariational
public import Tengoku.Seed.MeasureTheory.Integral.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! # The actual CDF/first-variation pairing identity

Fubini turns integration of a tail integral against a probability measure
into time integration against its cumulative mass. Atoms are retained in
the CDF; the boundary of the tail interval is null for Lebesgue measure.
-/

open Set MeasureTheory Filter
open scoped Topology

namespace Paper

/-- The Fubini identity underlying the JT first-variation formula, for
genuine probability measures and genuine Lebesgue interval integrals.
@isnad1 id=eq.1h2v.s7.5e9e94621a15 from=translated src=- shape=48d44756 vocab=ac164320
-/
theorem parisiCDF_tail_pairing (μ : ParisiMeasure) (g : ℝ → ℝ)
    (hg : IntegrableOn g (Ioc (0 : ℝ) 1) volume) :
    (∫ x : Overlap, (∫ s in (x : ℝ)..1, g s) ∂(μ : Measure Overlap)) =
      ∫ s in (0 : ℝ)..1, g s * parisiCDF μ s := by
  let τ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  let K : Overlap → ℝ → ℝ := fun x s => if (x : ℝ) ≤ s then g s else 0
  have hS : MeasurableSet {p : Overlap × ℝ | (p.1 : ℝ) ≤ p.2} :=
    (isClosed_le (continuous_subtype_val.comp continuous_fst) continuous_snd).measurableSet
  have hK : Integrable (Function.uncurry K) ((μ : Measure Overlap).prod τ) := by
    have hi := (hg.comp_snd (μ : Measure Overlap)).indicator hS
    have hfun : Function.uncurry K =
        {p : Overlap × ℝ | (p.1 : ℝ) ≤ p.2}.indicator (fun p => g p.2) := by
      funext p
      rfl
    rw [hfun]
    exact hi
  have hleft : ∀ x : Overlap, (∫ s, K x s ∂τ) = ∫ s in (x : ℝ)..1, g s := by
    intro x
    change (∫ s, (Ici (x : ℝ)).indicator g s ∂τ) = _
    rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
    change (∫ s, g s ∂(volume.restrict (Ioc (0 : ℝ) 1)).restrict (Ioi (x : ℝ))) = _
    rw [Measure.restrict_restrict measurableSet_Ioi, inter_comm, Ioc_inter_Ioi,
      sup_of_le_right x.property.1, intervalIntegral.integral_of_le x.property.2]
  have hright : ∀ s : ℝ, (∫ x : Overlap, K x s ∂(μ : Measure Overlap)) =
      g s * parisiCDF μ s := by
    intro s
    change (∫ x : Overlap, {x : Overlap | (x : ℝ) ≤ s}.indicator
      (fun _ => g s) x ∂(μ : Measure Overlap)) = _
    rw [integral_indicator_const _
      (isClosed_le continuous_subtype_val continuous_const).measurableSet]
    simp only [parisiCDF, Measure.real, smul_eq_mul, mul_comm]
  calc
    (∫ x : Overlap, (∫ s in (x : ℝ)..1, g s) ∂(μ : Measure Overlap)) =
        ∫ x : Overlap, ∫ s, K x s ∂τ ∂(μ : Measure Overlap) := by
      congr 1
      ext x
      exact (hleft x).symm
    _ = ∫ s, ∫ x : Overlap, K x s ∂(μ : Measure Overlap) ∂τ :=
      integral_integral_swap hK
    _ = ∫ s in (0 : ℝ)..1, g s * parisiCDF μ s := by
      simp_rw [hright]
      exact (intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)).symm

/-- The paper's `G_μ` pairs with a competitor exactly by the CDF formula.
This is deterministic and does not assume a PDE/SDE identification of `f`.
@isnad1 id=eq.1h3v.s7.ddfb22257ae4 from=translated src=- shape=9256dc64 vocab=5ffbabeb
-/
theorem parisiG_integral_eq_cdf (β : ℝ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) (μ : ParisiMeasure) :
    (∫ x : Overlap, parisiG β f (x : ℝ) ∂(μ : Measure Overlap)) =
      ∫ s in (0 : ℝ)..1, β ^ 2 / 2 * (f s - s) * parisiCDF μ s := by
  apply parisiCDF_tail_pairing
  exact (parisiIntegrable (β := β) hf (by constructor <;> norm_num)
    (by constructor <;> norm_num)).1

end Paper

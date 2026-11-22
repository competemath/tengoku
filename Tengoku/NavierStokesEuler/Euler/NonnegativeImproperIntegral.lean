import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.Basic
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Set

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Unbounded finite partial integrals of a nonnegative function force
its extended integral on the half-open interval to be infinite. Local
integrability is explicit, so no totalized real integral is used as a
substitute for an improper integral. -/

noncomputable section

namespace EulerNonnegativeImproperIntegral

open Set MeasureTheory
open scoped ENNReal

/--
@isnad1 id=le.4h3v.s7.51678915a29d from=translated src=- shape=14710a9b vocab=53d93f80
-/
theorem ofReal_partial_le_lintegral (f : ℝ → ℝ) {S T : ℝ}
    (hS : 0 ≤ S) (hST : S < T) (hf : IntervalIntegrable f volume 0 S)
    (hnonneg : ∀ x ∈ Ioc (0 : ℝ) S, 0 ≤ f x) :
    ENNReal.ofReal (∫ x in (0 : ℝ)..S, f x) ≤
      ∫⁻ x in Ico (0 : ℝ) T, ENNReal.ofReal (f x) := by
  rw [intervalIntegral.integral_of_le hS,
    ofReal_integral_eq_lintegral_ofReal hf.1
      (ae_restrict_of_forall_mem measurableSet_Ioc hnonneg)]
  exact lintegral_mono_set (fun _ hx => ⟨hx.1.le,hx.2.trans_lt hST⟩)

/--
@isnad1 id=eq.3h2v.s7.230370c77135 from=translated src=- shape=e996a42d vocab=966a237c
-/
theorem lintegral_eq_top_of_unbounded_partials (f : ℝ → ℝ) (T : ℝ)
    (hf : ∀ S : ℝ, 0 < S → S < T → IntervalIntegrable f volume 0 S)
    (hnonneg : ∀ x ∈ Ico (0 : ℝ) T, 0 ≤ f x)
    (hunbounded : ∀ K : ℝ, ∃ S : ℝ, 0 < S ∧ S < T ∧
      K < ∫ x in (0 : ℝ)..S, f x) :
    (∫⁻ x in Ico (0 : ℝ) T, ENNReal.ofReal (f x))=⊤ := by
  by_contra hfinite
  obtain ⟨S,hS,hST,hK⟩ := hunbounded
    (∫⁻ x in Ico (0 : ℝ) T, ENNReal.ofReal (f x)).toReal
  have hb := ofReal_partial_le_lintegral f hS.le hST (hf S hS hST)
    (fun x hx => hnonneg x ⟨hx.1.le,hx.2.trans_lt hST⟩)
  exact (not_lt_of_ge hb) ((ENNReal.lt_ofReal_iff_toReal_lt hfinite).mpr hK)

end EulerNonnegativeImproperIntegral

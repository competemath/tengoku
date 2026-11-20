import Tengoku.Lmlf.LMLF.Integral.Improper.Basic
import Tengoku.Seed.MeasureTheory.Integral.IntegralEqImproper

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Filter MeasureTheory Set
open scoped Interval

noncomputable section

namespace LMLF.Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem canonicalPrimitivePackage
    [CompleteSpace E] (f : ℝ → E) (k : ℝ) (S : Finset ℝ)
    (hS : ∀ c ∈ S, k < c) (hf : IntegrableOn f (Ioi k)) :
    IsFiniteExceptionalPrimitive f k S (fun t => ∫ x in k..t, f x) ∧
      Tendsto (fun t => ∫ x in k..t, f x) atTop
        (nhds (∫ x in Ioi k, f x)) := by
  let P : ℝ → E := fun t => ∫ x in k..t, f x
  have htail := hf.continuousOn_Ici_primitive_Ioi
  have hPcont : ContinuousOn P (Ici k) := by
    exact (continuousOn_const.sub htail).congr fun t ht =>
      (intervalIntegral.integral_Ioi_sub_Ioi hf ht).symm
  have hP : IsFiniteExceptionalPrimitive f k S P := by
    refine ⟨hS, hPcont, ?_, ?_⟩
    · simp [P]
    · intro a b hka hab _
      have habOn : IntegrableOn f (Ioc a b) :=
        hf.mono_set (fun x hx => lt_of_le_of_lt hka hx.1)
      have habInt : IntervalIntegrable f volume a b :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 habOn
      have hkaInt : IntervalIntegrable f volume k a := by
        apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hka).2
        exact hf.mono_set (fun x hx => hx.1)
      refine ⟨habInt, ?_⟩
      have hadd :=
        intervalIntegral.integral_add_adjacent_intervals hkaInt habInt
      change (∫ x in k..b, f x) - ∫ x in k..a, f x = _
      rw [← hadd]
      abel
  refine ⟨hP, ?_⟩
  exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi k hf tendsto_id

/-- IMP-001-T07.
@isnad1 id=hasimpro.2h4v.s6.0fd576b5fd0b from=translated src=- shape=95582a95 vocab=350db8a2
-/
theorem HasImproperIntegralAtTopExcept.of_integrableOn_Ioi
    [CompleteSpace E] (f : ℝ → E) (k : ℝ) (S : Finset ℝ)
    (hS : ∀ c ∈ S, k < c) (hf : IntegrableOn f (Ioi k)) :
    HasImproperIntegralAtTopExcept f k S (∫ t in Ioi k, f t) := by
  apply hasImproperIntegralAtTopExcept_iff_exists_primitive.mpr
  exact ⟨fun t => ∫ x in k..t, f x, canonicalPrimitivePackage f k S hS hf⟩

end LMLF.Integral

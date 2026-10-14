/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Tengoku

/-!
# Support Restrict

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set
open CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace CKN.Foundation.Measure

/-- If a function is almost everywhere strongly measurable with respect to the
restricted measure `volume.restrict s` and its support is contained in the
measurable set `s`, then it is almost everywhere strongly measurable with
respect to the ambient `volume`.
@isnad1 id=aestrong.3h2v.s8.0d1974af8171 from=translated src=- shape=4cbfd084 vocab=4ea1e2d7
-/
theorem aestronglyMeasurable_of_restrict_of_support
    {h : Vec3 → ℝ} {s : Set Vec3} (hs : MeasurableSet s)
    (hmeas : AEStronglyMeasurable h (volume.restrict s))
    (hsupp : Function.support h ⊆ s) :
    AEStronglyMeasurable h volume := by
  have h1 : AEMeasurable (s.indicator h) volume :=
    (aemeasurable_indicator_iff hs).2 hmeas.aemeasurable
  have heq : s.indicator h = h := by
    funext y
    by_cases hy : y ∈ s
    · simp [Set.indicator_of_mem hy]
    · have hz : h y = 0 := by
        by_contra hne
        exact hy (hsupp hne)
      simp [Set.indicator_of_notMem hy, hz]
  rw [heq] at h1
  exact h1.aestronglyMeasurable

/-- A continuous compactly supported multiplier localizes an integrable function.
@isnad1 id=integrab.4h5v.s6.4a4bd2dd5ab5 from=translated src=- shape=1bb70c9e vocab=5334ac9e
-/
theorem integrable_mul_of_tsupport_subset {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {μ : Measure α} {s : Set α} {f g : α → ℝ}
    (hf : IntegrableOn f s μ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupport : tsupport g ⊆ s) : Integrable (fun x => f x * g x) μ := by
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
  have hmul : IntegrableOn (fun x => f x * g x) s μ :=
    hf.mul_bdd hg.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x)
  exact hmul.integrable_of_forall_notMem_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (f := g) (fun h => hx (hsupport h)), mul_zero])

end CKN.Foundation.Measure

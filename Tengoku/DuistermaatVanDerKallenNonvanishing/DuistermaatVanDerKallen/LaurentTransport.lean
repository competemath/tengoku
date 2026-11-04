import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.LaurentGeometry
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.ODEContinuation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Existence of the manuscript's normalized-gradient transport throughout a
closed base segment. Compact control is proved for every partial solution before
applying continuation. Smooth dependence and the fiber diffeomorphism are separate. -/

open Set
open scoped Topology

namespace DuistermaatVanDerKallen

noncomputable section

/-- Uniqueness of Laurent segment solutions, including both endpoints.
@isnad1 id=eqon.3h5v.s8.aa5e774b396d from=translated src=- shape=1e5200c5 vocab=e07c120c
-/
theorem laurent_segment_unique {d : ℕ} (f : MultiLaurent d) (a : ℂ)
    {γ η : ℝ → (Fin d → ℂ)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ laurentRegularDomain f ∧
      HasDerivAt γ (laurentVectorField f a (γ t)) t)
    (hη : ∀ t ∈ Icc (0 : ℝ) 1, η t ∈ laurentRegularDomain f ∧
      HasDerivAt η (laurentVectorField f a (η t)) t)
    (hinit : γ 0 = η 0) : EqOn γ η (Icc (0 : ℝ) 1) :=
  ode_unique_on_closed_interval
    (fun y hy => (polynomialVectorField_contDiffAt_position
      (laurentRepresentative f) a hy).of_le (by simp))
    (fun t ht => (hγ t ht).2.continuousAt.continuousWithinAt)
    (fun t ht => (hη t ht).2.continuousAt.continuousWithinAt)
    (fun t ht => (hγ t (Ico_subset_Icc_self ht)).2)
    (fun t ht => (hη t (Ico_subset_Icc_self ht)).2)
    (fun t ht => (hγ t ht).1) (fun t ht => (hη t ht).1) hinit

/-- Reversing the base velocity negates the explicit scalar lift.
@isnad1 id=eq.0h4v.s5.0c8e36c068f3 from=translated src=- shape=64b4f7f5 vocab=5c6cebbd
-/
theorem laurentVectorField_neg {d : ℕ} (f : MultiLaurent d) (a : ℂ) (z : Fin d → ℂ) :
    laurentVectorField f (-a) z = -laurentVectorField f a z := by
  funext i
  simp only [laurentVectorField, polynomialVectorField, scalarLift, Pi.neg_apply]
  ring

/-- Time reversal of a segment solution solves the reversed normalized-gradient ODE.
@isnad1 id=and.2h5v.s8.d3e75af351c3 from=translated src=- shape=41892b9d vocab=b54d1fdc
-/
theorem laurent_segment_reverse {d : ℕ} (f : MultiLaurent d) (a : ℂ)
    {γ : ℝ → (Fin d → ℂ)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ laurentRegularDomain f ∧
      HasDerivAt γ (laurentVectorField f a (γ t)) t) :
    ∀ t ∈ Icc (0 : ℝ) 1, γ (1 - t) ∈ laurentRegularDomain f ∧
      HasDerivAt (fun u => γ (1 - u)) (laurentVectorField f (-a) (γ (1 - t))) t := by
  intro t ht
  have hrev : 1 - t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
  refine ⟨(hγ _ hrev).1, ?_⟩
  rw [laurentVectorField_neg]
  simpa only [Function.comp_def, id_eq, neg_one_smul] using
    (hγ _ hrev).2.scomp t ((hasDerivAt_id t).const_sub 1)

/-- Any solution of the reversed segment retraces the forward solution.
This gives the inverse identity without presupposing a chosen global flow.
@isnad1 id=eqon.3h5v.s8.293ec9b88cff from=translated src=- shape=f382e74b vocab=b4ff9059
-/
theorem laurent_segment_reverse_inverse {d : ℕ} (f : MultiLaurent d) (a : ℂ)
    {γ η : ℝ → (Fin d → ℂ)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ laurentRegularDomain f ∧
      HasDerivAt γ (laurentVectorField f a (γ t)) t)
    (hη : ∀ t ∈ Icc (0 : ℝ) 1, η t ∈ laurentRegularDomain f ∧
      HasDerivAt η (laurentVectorField f (-a) (η t)) t)
    (hinit : η 0 = γ 1) : EqOn η (fun t => γ (1 - t)) (Icc (0 : ℝ) 1) :=
  laurent_segment_unique f (-a) hη (laurent_segment_reverse f a hγ) (by simpa using hinit)

end
end DuistermaatVanDerKallen

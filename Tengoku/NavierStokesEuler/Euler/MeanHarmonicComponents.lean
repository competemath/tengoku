import Tengoku.NavierStokesEuler.Euler.MeanMollifierLimit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Scalar test functions and component energies for actual R³ vector fields. -/

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit
open scoped ContDiff

/--
@isnad1 id=memlp.1h2v.s9.5a9268c48307 from=translated src=- shape=f5ca9ea1 vocab=84bc5584
-/
theorem scalar_component_memLp (u : Space → Space) (hu : MemLp u 2 volume)
    (i : Fin 3) : MemLp (fun x => u x i) 2 volume :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp_memLp' hu

/--
@isnad1 id=eq.1h3v.s9.532690befe36 from=translated src=- shape=8dbdd21a vocab=9d7431f8
-/
theorem laplacian_scalar_smul_vector (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (v : Space) (x : Space) :
    Δ (fun y => φ y • v) x = Δ φ x • v := by
  let L : ℝ →L[ℝ] Space := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  exact ((hφ.of_le (by simp)).contDiffAt).laplacian_CLM_comp_left (l := L)

/-- Testing a vector distribution along each fixed coordinate gives scalar weak harmonicity.
@isnad1 id=scalarwe.1h3v.s10.705e9fccf71a from=translated src=- shape=938e1dc5 vocab=db554c55
-/
theorem scalarWeakHarmonicOn_of_vector_tests (U : Set Space) (u : Space → Space)
    (hu : ∀ φ : Space → Space, HasCompactSupport φ → ContDiff ℝ ∞ φ → tsupport φ ⊆ U →
      (∫ x, ⟪u x, Δ φ x⟫_ℝ) = 0) (i : Fin 3) :
    ScalarWeakHarmonicOn U (fun x => u x i) := by
  intro φ hc hs ht
  let e : Space := EuclideanSpace.single i 1
  have hcs : HasCompactSupport (fun x => φ x • e) := hc.smul_right (f' := fun _ => e)
  have hss : ContDiff ℝ ∞ (fun x => φ x • e) := hs.smul contDiff_const
  have hts : tsupport (fun x => φ x • e) ⊆ U :=
    (tsupport_smul_subset_left φ (fun _ => e)).trans ht
  have H := hu (fun x => φ x • e) hcs hss hts
  calc
    _ = ∫ x, ⟪u x, Δ (fun y => φ y • e) x⟫_ℝ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [laplacian_scalar_smul_vector φ hs e x]
      simp only [inner_smul_right, e, EuclideanSpace.inner_single_right, one_mul,
        RCLike.conj_to_real]
      ring
    _ = 0 := H

/--
@isnad1 id=eq.1h1v.s10.92fe1fb7ca0a from=translated src=- shape=20b809fa vocab=d14ed3e5
-/
theorem sum_component_energy (u : Space → Space) (hu : MemLp u 2 volume) :
    (∑ i : Fin 3, lpNorm (fun x => u x i) 2 volume ^ 2) = lpNorm u 2 volume ^ 2 := by
  simp_rw [lpNorm_sq_eq_integral_sq _ (scalar_component_memLp u hu _)]
  rw [lpNorm_sq_eq_integral_norm_sq u hu,
    ← integral_finsetSum _ (fun i _ => (memLp_two_iff_integrable_sq
      (scalar_component_memLp u hu i).aestronglyMeasurable).1 (scalar_component_memLp u hu i))]
  apply integral_congr_ae
  filter_upwards [] with x
  exact (EuclideanSpace.real_norm_sq_eq (u x)).symm

/-- Uniform component bounds combine without a dimension-dependent loss in the energy.
@isnad1 id=eventual.2h3v.s11.ef2f9d8feead from=translated src=- shape=d68432c2 vocab=3eb5072a
-/
theorem ae_vector_bound_of_component_bounds (u : Space → Space) (hu : MemLp u 2 volume)
    (U : Set Space) (C : ℝ)
    (hc : ∀ i : Fin 3, ∀ᵐ x ∂volume,
      x ∈ U → u x i ^ 2 ≤ C * lpNorm (fun y => u y i) 2 volume ^ 2) :
    ∀ᵐ x ∂volume, x ∈ U → ‖u x‖ ^ 2 ≤ C * lpNorm u 2 volume ^ 2 := by
  have hall : ∀ᵐ x ∂volume, ∀ i : Fin 3,
      x ∈ U → u x i ^ 2 ≤ C * lpNorm (fun y => u y i) 2 volume ^ 2 :=
    ae_all_iff.2 hc
  filter_upwards [hall] with x hx
  intro hxU
  rw [EuclideanSpace.real_norm_sq_eq, ← sum_component_energy u hu, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => hx i hxU)

end EulerMeanHarmonic

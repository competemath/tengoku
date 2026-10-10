import Tengoku.Degiorgi.DeGiorgi.Foundations
import Tengoku.Degiorgi.DeGiorgi.WholeSpaceSobolev
import Tengoku

/-!
# Chapter 02: Sobolev Weak-Derivative Layer

This module defines weak derivatives and proves their basic closure and
uniqueness properties.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal Convolution Pointwise

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- `HasWeakPartialDeriv i g f Ω` means that `g` is the weak partial derivative
of `f` with respect to coordinate `i` on `Ω`. -/
def HasWeakPartialDeriv (i : Fin d) (g f : E → ℝ) (Ω : Set E) : Prop :=
  ∀ φ : E → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ Ω →
    ∫ x in Ω, f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) =
      -∫ x in Ω, g x * φ x

/-- Alternate name for `HasWeakPartialDeriv`. -/
abbrev HasWeakPartialDeriv' (i : Fin d) (g f : E → ℝ) (Ω : Set E) : Prop :=
  HasWeakPartialDeriv (d := d) i g f Ω

/-- `HasWeakGrad G f Ω` means that `G` is the weak gradient of `f` on `Ω`. -/
def HasWeakGrad (G : E → E) (f : E → ℝ) (Ω : Set E) : Prop :=
  ∀ i : Fin d, HasWeakPartialDeriv i (fun x => G x i) f Ω

/-- `HasWeakDiv g F Ω` means that `g` is the weak divergence of `F` on `Ω`. -/
def HasWeakDiv (g : E → ℝ) (F : E → E) (Ω : Set E) : Prop :=
  ∀ φ : E → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ Ω →
    ∫ x in Ω, (∑ i, F x i * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) =
      -∫ x in Ω, g x * φ x

omit [NeZero d] in
/-- Classical `C¹` derivatives give weak derivatives on open sets. -/
theorem HasWeakPartialDeriv.of_contDiff {Ω : Set E} (hΩ : IsOpen Ω)
    {i : Fin d} {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    HasWeakPartialDeriv i (fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)) f Ω := by
  let _ := hΩ
  intro φ hφ hφ_supp hφ_sub
  let v := EuclideanSpace.single i (1 : ℝ)
  have h_fderiv_supp : tsupport (fun x => (fderiv ℝ φ x) v) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v).trans hφ_sub
  have hf_diff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hφ_diff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hf_cont : Continuous f := hf_diff.continuous
  have hφ_cont : Continuous φ := hφ_diff.continuous
  have hfderiv_φ_cont : Continuous (fun x => (fderiv ℝ φ x) v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfderiv_f_cont : Continuous (fun x => (fderiv ℝ f x) v) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hφ_fderiv_supp : HasCompactSupport (fun x => (fderiv ℝ φ x) v) :=
    hφ_supp.fderiv_apply (𝕜 := ℝ) v
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero, setIntegral_eq_integral_of_forall_compl_eq_zero]
  ·
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      ((hfderiv_f_cont.mul hφ_cont).integrable_of_hasCompactSupport hφ_supp.mul_left)
      ((hf_cont.mul hfderiv_φ_cont).integrable_of_hasCompactSupport hφ_fderiv_supp.mul_left)
      ((hf_cont.mul hφ_cont).integrable_of_hasCompactSupport hφ_supp.mul_left)
      (fun x _ => hf_diff x) (fun x _ => hφ_diff x)
  ·
    intro x hx
    have : x ∉ tsupport φ := fun h => hx (hφ_sub h)
    simp only [mul_eq_zero]
    right
    by_contra hf'
    exact this (subset_tsupport φ (mem_support.mpr hf'))
  ·
    intro x hx
    have : x ∉ tsupport (fun x => (fderiv ℝ φ x) v) := fun h => hx (h_fderiv_supp h)
    simp only [mul_eq_zero]
    right
    by_contra hf'
    exact this (subset_tsupport _ (mem_support.mpr hf'))

omit [NeZero d] in
theorem HasWeakPartialDeriv.restrict {Ω Ω' : Set E}
    (hΩ' : IsOpen Ω') (h_sub : Ω' ⊆ Ω)
    {i : Fin d} {g f : E → ℝ}
    (hf : HasWeakPartialDeriv i g f Ω) :
    HasWeakPartialDeriv i g f Ω' := by
  let _ := hΩ'
  intro φ hφ_smooth hφ_compact hφ_supp
  have hφ_supp_Ω : tsupport φ ⊆ Ω := hφ_supp.trans h_sub
  have key := hf φ hφ_smooth hφ_compact hφ_supp_Ω
  have h1 : ∀ x, x ∉ Ω' → f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) = 0 := by
    intro x hx
    have hx_notin : x ∉ tsupport φ := fun h => hx (hφ_supp h)
    have hφ_eq : φ =ᶠ[𝓝 x] 0 :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hx_notin |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [Filter.EventuallyEq.fderiv_eq hφ_eq]
    simp
  have h2 : ∀ x, x ∉ Ω' → g x * φ x = 0 := by
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hφ_supp h))]
  have h3 : ∀ x, x ∉ Ω → f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) = 0 :=
    fun x hx => h1 x (fun h => hx (h_sub h))
  have h4 : ∀ x, x ∉ Ω → g x * φ x = 0 :=
    fun x hx => h2 x (fun h => hx (h_sub h))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero h1,
    setIntegral_eq_integral_of_forall_compl_eq_zero h2,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero h3,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero h4,
    key]

end DeGiorgi

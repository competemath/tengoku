import Tengoku.Hellingerrepolean4.Hellinger.F2Model

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The transformed product noise is an explicit additional convolution.
This is the probabilistic comparison used after selecting quotient columns. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.ShearNoise
open F2Model ChannelSections

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/--
@isnad1 id=eq.0h3v.s6.775548af9b39 from=translated src=- shape=db0dfd64 vocab=07535ad4
-/
theorem mean_add (f : (ι → F2) → ℝ) (z : ι → F2) :
    mean (fun x => f (x + z)) = mean f :=
  mean_comp_equiv (Equiv.addRight z) f

/--
@isnad1 id=eq.1h5v.s7.fca795a6f3dc from=translated src=- shape=3621b95b vocab=c9f624b4
-/
theorem noise_apply_shift (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (f : (ι → F2) → ℝ) (y z : ι → F2) :
    (noise ι ρ hρ).apply (fun x => f (x + z)) y =
      (noise ι ρ hρ).apply f (y + z) := by
  rw [noise_apply_additive, noise_apply_additive]
  apply Finset.sum_congr rfl
  intro e _
  congr 2
  abel

def shearFunction (g : (ι → F2) → ℝ) (D : (κ → F2) →ₗ[F2] (ι → F2))
    (x : (ι → F2) × (κ → F2)) : ℝ := g (x.1 + D x.2)

def extraNoise (ρ : ℝ) (D : (κ → F2) →ₗ[F2] (ι → F2))
    (h : (ι → F2) → ℝ) (v : ι → F2) : ℝ :=
  ∑ e : κ → F2, errorMass ρ e * h (v + D e)

/--
@isnad1 id=eq.1h7v.s9.ee6de73c43af from=translated src=- shape=589e346e vocab=7099ac67
-/
theorem product_shear_posterior (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (g : (ι → F2) → ℝ) (D : (κ → F2) →ₗ[F2] (ι → F2))
    (y : ι → F2) (z : κ → F2) :
    (productChannel (noise ι ρ hρ) (noise κ ρ hρ)).apply (shearFunction g D) (y, z) =
      extraNoise ρ D ((noise ι ρ hρ).apply g) (y + D z) := by
  rw [productChannel_apply]
  simp only [shearFunction, noise_apply_shift]
  rw [noise_apply_additive]
  simp only [extraNoise, map_add, add_assoc]

/--
@isnad1 id=eq.0h4v.s8.480656d7a359 from=translated src=- shape=1d65b225 vocab=41f9494b
-/
theorem mean_shear (g : (ι → F2) → ℝ) (D : (κ → F2) →ₗ[F2] (ι → F2)) :
    mean (shearFunction g D) = mean g := by
  rw [mean_prod_swap]
  simp only [shearFunction, mean_add, mean_const]

/--
@isnad1 id=eq.1h5v.s8.6fcdac914278 from=translated src=- shape=72f7272f vocab=6a48c25c
-/
theorem extraNoise_mean (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (D : (κ → F2) →ₗ[F2] (ι → F2)) (g : (ι → F2) → ℝ) :
    mean (extraNoise ρ D g) = mean g := by
  unfold mean extraNoise
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have hsum (e : κ → F2) : (∑ x, g (x + D e)) = ∑ x, g x :=
    Equiv.sum_comp (Equiv.addRight (D e)) g
  simp_rw [hsum]
  rw [← Finset.sum_mul, errorMass_sum ρ hρ, one_mul]

/--
@isnad1 id=le.3h6v.s8.4963856570d3 from=translated src=- shape=3744ede4 vocab=4eb4100b
-/
theorem extraNoise_convex_mean_le (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (D : (κ → F2) →ₗ[F2] (ι → F2)) (g : (ι → F2) → ℝ)
    (hg : ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1)
    (Ψ : ℝ → ℝ) (hΨ : ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) Ψ) :
    mean (fun v => Ψ (extraNoise ρ D g v)) ≤ mean (fun v => Ψ (g v)) := by
  have hp (v : ι → F2) :
      Ψ (extraNoise ρ D g v) ≤ extraNoise ρ D (fun x => Ψ (g x)) v := by
    exact hΨ.map_sum_le (fun e _ => errorMass_nonneg ρ hρ e)
      (by simpa using errorMass_sum (ι := κ) ρ hρ) (fun e _ => hg (v + D e))
  exact (mean_mono _ _ hp).trans_eq (extraNoise_mean ρ hρ D _)

/--
@isnad1 id=le.3h6v.s9.f831b4802901 from=translated src=- shape=32dcf0bf vocab=7cb924f7
-/
theorem shear_convex_comparison (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (g : (ι → F2) → ℝ) (hg : ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1)
    (D : (κ → F2) →ₗ[F2] (ι → F2))
    (Ψ : ℝ → ℝ) (hΨ : ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) Ψ) :
    mean (fun y => Ψ ((productChannel (noise ι ρ hρ) (noise κ ρ hρ)).apply
      (shearFunction g D) y)) ≤ mean (fun y => Ψ ((noise ι ρ hρ).apply g y)) := by
  rw [mean_prod_swap]
  simp_rw [product_shear_posterior]
  have hm (z : κ → F2) :
      mean (fun y => Ψ (extraNoise ρ D ((noise ι ρ hρ).apply g) (y + D z))) =
        mean (fun y => Ψ (extraNoise ρ D ((noise ι ρ hρ).apply g) y)) :=
    mean_add (fun y => Ψ (extraNoise ρ D ((noise ι ρ hρ).apply g) y)) (D z)
  simp_rw [hm, mean_const]
  exact extraNoise_convex_mean_le ρ hρ D _ (fun x =>
    (noise ι ρ hρ).apply_mem_Icc g hg x) Ψ hΨ

end Hellinger.ShearNoise

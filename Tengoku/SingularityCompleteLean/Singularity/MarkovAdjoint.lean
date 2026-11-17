import Tengoku.SingularityCompleteLean.Singularity.Markov
import Tengoku.Seed.Analysis.InnerProductSpace.Adjoint

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The reflected law and the right Markov adjoint

These identities hold for arbitrary real finite weights. Neither symmetry,
laziness, nor a spectral gap is required.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]

/-- The a.e. formula for a single right translation.
@isnad1 id=eventual.0h3v.s11.6557e812677a from=translated src=- shape=91a0d168 vocab=fc67b457
-/
theorem rightTranslation_apply_ae (g : Γ) (f : GroupL2 Γ) :
    (rightTranslation g f : Γ → ℂ) =ᵐ[Measure.count] fun x => f (x * g) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_right Measure.count g)

/-- Composition has the order dictated by the right-translation convention.
@isnad1 id=eq.0h4v.s12.fabf8a503a5e from=translated src=- shape=86d8832b vocab=b9a5bde3
-/
theorem rightTranslation_mul (g h : Γ) (f : GroupL2 Γ) :
    rightTranslation g (rightTranslation h f) = rightTranslation (g * h) f := by
  apply Lp.ext
  have hcomp := (measurePreserving_mul_right Measure.count g).quasiMeasurePreserving.ae
    (rightTranslation_apply_ae h f)
  filter_upwards [rightTranslation_apply_ae g (rightTranslation h f), hcomp,
    rightTranslation_apply_ae (g * h) f] with x hx hy hz
  rw [hx, hy, hz, mul_assoc]

/-- Translation by the identity acts as the identity.
@isnad1 id=eq.0h2v.s11.0a2e36863bf9 from=translated src=- shape=90a28e51 vocab=868f270d
-/
theorem rightTranslation_one (f : GroupL2 Γ) : rightTranslation (1 : Γ) f = f := by
  apply Lp.ext
  simpa only [mul_one] using rightTranslation_apply_ae (1 : Γ) f

/-- The adjoint of right translation by g is right translation by g⁻¹.
@isnad1 id=eq.0h2v.s16.dac662ed47e1 from=translated src=- shape=3946cef3 vocab=2606e06a
-/
theorem rightTranslation_adjoint (g : Γ) :
    (rightTranslation g).toContinuousLinearMap.adjoint =
      (rightTranslation g⁻¹).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro h
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (rightTranslation g h) f = inner ℂ h (rightTranslation g⁻¹ f)
  have hi : rightTranslation g (rightTranslation g⁻¹ f) = f := by
    rw [rightTranslation_mul, mul_inv_cancel, rightTranslation_one]
  calc
    inner ℂ (rightTranslation g h) f =
        inner ℂ (rightTranslation g h) (rightTranslation g (rightTranslation g⁻¹ f)) := by rw [hi]
    _ = inner ℂ h (rightTranslation g⁻¹ f) := (rightTranslation g).inner_map_map _ _

/-- The adjoint formula, with the original jump labels retained.
@isnad1 id=eq.0h3v.s16.1d2bbf2c3570 from=translated src=- shape=74d833e6 vocab=2ecbf5a5
-/
theorem rightMarkov_adjoint (s : Finset Γ) (μ : Γ → ℝ) :
    (rightMarkov s μ).adjoint =
      ∑ g ∈ s, (μ g : ℂ) • (rightTranslation g⁻¹).toContinuousLinearMap := by
  simp only [rightMarkov, map_sum, map_smulₛₗ, rightTranslation_adjoint,
    Complex.conj_ofReal]

/-- Reindexing identifies P* with the Markov operator for μ̌(g)=μ(g⁻¹).
@isnad1 id=eq.0h3v.s16.1ea4011f8dcf from=translated src=- shape=f90da763 vocab=72e9f9c9
-/
theorem rightMarkov_adjoint_eq_reflected (s : Finset Γ) (μ : Γ → ℝ) :
    (rightMarkov s μ).adjoint =
      rightMarkov (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) := by
  rw [rightMarkov_adjoint, rightMarkov, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, inv_inv]

/-- Pointwise form of the adjoint on counting-measure L².
@isnad1 id=eventual.0h4v.s16.0fd73a6b3948 from=translated src=- shape=b27dccac vocab=7545654f
-/
theorem rightMarkov_adjoint_apply_ae (s : Finset Γ) (μ : Γ → ℝ) (f : GroupL2 Γ) :
    ((rightMarkov s μ).adjoint f : Γ → ℂ) =ᵐ[Measure.count]
      fun x => ∑ g ∈ s, (μ g : ℂ) * f (x * g⁻¹) := by
  rw [rightMarkov_adjoint_eq_reflected]
  simpa only [Finset.sum_map, Function.Embedding.coeFn_mk, inv_inv] using
    rightMarkov_apply_ae (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) f

end Singularity

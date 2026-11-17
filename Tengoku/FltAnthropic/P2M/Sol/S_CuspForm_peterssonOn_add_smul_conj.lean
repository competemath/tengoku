import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CuspForm_PeterssonOn
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_FundamentalDomainVolume

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CuspForm_peterssonOn_add_smul_conj.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CuspForm_peterssonOn_add_smul_conj

set_option autoImplicit false

noncomputable section

open MeasureTheory UpperHalfPlane ModularForm Filter
open scoped MatrixGroups ModularForm ComplexConjugate Modular ENNReal Pointwise

namespace PetOnIP

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ}

local notation "Γᴳᴸ" => ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

/--
@isnad1 id=continuo.0h0v.s7.9213c1ba3a46 from=translated src=- shape=6cb9e56d vocab=434fe350
-/
scoped instance sl2zContinuousConstSMul : ContinuousConstSMul SL(2, ℤ) ℍ where
  continuous_const_smul γ := by
    have h : (fun z : ℍ => γ • z) =
        fun z : ℍ => (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) • z := by
      funext z
      exact MulAction.compHom_smul_def (Matrix.SpecialLinearGroup.mapGL ℝ) γ z
    rw [h]
    exact continuous_const_smul _

scoped instance fintypeQuot : Fintype (SL(2, ℤ) ⧸ Γ) :=
  haveI : Finite (SL(2, ℤ) ⧸ Γ) := Subgroup.finite_quotient_of_finiteIndex
  Fintype.ofFinite _

def cosum (Φ : ℍ → ℂ) (x : ℍ) : ℂ := ∑ q : SL(2, ℤ) ⧸ Γ, Φ ((q.out⁻¹ : SL(2, ℤ)) • x)

/--
@isnad1 id=eq.0h4v.s6.6033567886f0 from=translated src=- shape=cf9b44ef vocab=7dd257cc
-/
theorem integrand_eq (F G : ℍ → ℂ) :
    CuspForm.peterssonOnIntegrand Γ k F G = cosum (Γ := Γ) (UpperHalfPlane.petersson k F G) := by
  funext x
  unfold CuspForm.peterssonOnIntegrand cosum
  rw [finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun q _ => UpperHalfPlane.petersson_slash_SL k F G _ x

/--
@isnad1 id=eq.0h5v.s5.433e4ee6db0f from=translated src=- shape=c5c8e72b vocab=3544ec99
-/
theorem petersson_add_right (F G H : ℍ → ℂ) (x : ℍ) :
    UpperHalfPlane.petersson k F (G + H) x
      = UpperHalfPlane.petersson k F G x + UpperHalfPlane.petersson k F H x := by
  simp only [UpperHalfPlane.petersson, Pi.add_apply]; ring

/--
@isnad1 id=eq.0h5v.s5.9e2b17f9da80 from=translated src=- shape=8f4f15fc vocab=7a526d65
-/
theorem petersson_smul_right (F G : ℍ → ℂ) (c : ℂ) (x : ℍ) :
    UpperHalfPlane.petersson k F (c • G) x = c * UpperHalfPlane.petersson k F G x := by
  simp only [UpperHalfPlane.petersson, Pi.smul_apply, smul_eq_mul]; ring

/--
@isnad1 id=eq.0h3v.s7.8584570dccf9 from=translated src=- shape=9f00758e vocab=1047f938
-/
theorem cosum_add (Φ Ψ : ℍ → ℂ) : cosum (Γ := Γ) (Φ + Ψ) = cosum (Γ := Γ) Φ + cosum (Γ := Γ) Ψ := by
  funext x; simp [cosum, Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h3v.s7.20063e2d506a from=translated src=- shape=ef635317 vocab=a10f4435
-/
theorem cosum_const_mul (c : ℂ) (Φ : ℍ → ℂ) :
    cosum (Γ := Γ) (fun x => c * Φ x) = fun x => c * cosum (Γ := Γ) Φ x := by
  funext x; simp [cosum, Finset.mul_sum]

/--
@isnad1 id=continuo.1h2v.s7.21b160625fa7 from=translated src=- shape=4da3375c vocab=393f947f
-/
theorem continuous_cosum {Φ : ℍ → ℂ} (hΦ : Continuous Φ) : Continuous (cosum (Γ := Γ) Φ) :=
  continuous_finsetSum _ fun _ _ => hΦ.comp (continuous_const_smul _)

/--
@isnad1 id=integrab.2h2v.s7.f82a57aecca6 from=translated src=- shape=fe0b9fe9 vocab=c789f174
-/
theorem integrable_cosum {Φ : ℍ → ℂ} (hΦ : Continuous Φ) (hbd : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    Integrable (cosum (Γ := Γ) Φ) (volume.restrict (𝒟 : Set ℍ)) := by
  obtain ⟨C, hC⟩ := hbd
  refine Measure.integrableOn_of_bounded (M := ∑ _q : SL(2, ℤ) ⧸ Γ, C)
    FLT.FundamentalDomainVolume.volume_fd_lt_top.ne (continuous_cosum hΦ).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => hC _)

/--
@isnad1 id=ex.0h4v.s9.2f65463a0061 from=translated src=- shape=e3bfd1fd vocab=10b6c998
-/
theorem petersson_bounded (f g : CuspForm Γᴳᴸ k) :
    ∃ C, ∀ x, ‖UpperHalfPlane.petersson k ⇑f ⇑g x‖ ≤ C :=
  CuspFormClass.petersson_bounded_left k Γᴳᴸ f g

omit [Γ.FiniteIndex] in
/--
@isnad1 id=continuo.0h4v.s9.20cf1e7edc30 from=translated src=- shape=5073bece vocab=60e83cbf
-/
theorem petersson_continuous' (f g : CuspForm Γᴳᴸ k) : Continuous (UpperHalfPlane.petersson k ⇑f ⇑g) :=
  UpperHalfPlane.petersson_continuous k (CuspFormClass.holo f).continuous (CuspFormClass.holo g).continuous

/--
@isnad1 id=integrab.0h4v.s9.343de8ce6ac3 from=translated src=- shape=e3aeabd6 vocab=d47b4991
-/
theorem integrable_integrand (f g : CuspForm Γᴳᴸ k) :
    Integrable (CuspForm.peterssonOnIntegrand Γ k ⇑f ⇑g) (volume.restrict (𝒟 : Set ℍ)) := by
  rw [integrand_eq]
  exact integrable_cosum (petersson_continuous' f g) (petersson_bounded f g)

/--
@isnad1 id=eq.0h5v.s11.1a584a1fa140 from=translated src=- shape=337a8570 vocab=789462c5
-/
theorem peterssonOn_add_right (f g h : CuspForm Γᴳᴸ k) :
    CuspForm.peterssonOn Γ k f (g + h) = CuspForm.peterssonOn Γ k f g + CuspForm.peterssonOn Γ k f h := by
  rw [CuspForm.peterssonOn_def, CuspForm.peterssonOn_def, CuspForm.peterssonOn_def,
    ← integral_add (integrable_integrand f g) (integrable_integrand f h)]
  congr 1
  rw [integrand_eq, integrand_eq, integrand_eq]
  change _ = cosum (Γ := Γ) (UpperHalfPlane.petersson k ⇑f ⇑g) + cosum (Γ := Γ) (UpperHalfPlane.petersson k ⇑f ⇑h)
  rw [← cosum_add]
  congr 1
  funext x
  exact petersson_add_right _ _ _ x

/--
@isnad1 id=eq.0h5v.s10.3199c0059f44 from=translated src=- shape=2f74b7ad vocab=8c8f63a9
-/
theorem peterssonOn_smul_right (c : ℂ) (f g : CuspForm Γᴳᴸ k) :
    CuspForm.peterssonOn Γ k f (c • g) = c * CuspForm.peterssonOn Γ k f g := by
  rw [CuspForm.peterssonOn_def, CuspForm.peterssonOn_def, ← integral_const_mul]
  congr 1
  rw [integrand_eq, integrand_eq]
  change _ = fun x => c * cosum (Γ := Γ) (UpperHalfPlane.petersson k ⇑f ⇑g) x
  rw [← cosum_const_mul]
  congr 1
  funext x
  exact petersson_smul_right _ _ c x

/--
@isnad1 id=eq.0h5v.s7.72b9e26adac5 from=translated src=- shape=0deb3277 vocab=330cd884
-/
theorem cosum_conj (F G : ℍ → ℂ) (x : ℍ) :
    conj (cosum (Γ := Γ) (UpperHalfPlane.petersson k G F) x)
      = cosum (Γ := Γ) (UpperHalfPlane.petersson k F G) x := by
  unfold cosum
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [UpperHalfPlane.petersson_symm k F G, Complex.conj_conj]

/--
@isnad1 id=eq.0h5v.s10.9a082e4e6bb3 from=translated src=- shape=7061807e vocab=8f49bd79
-/
theorem integrand_conj (f g : CuspForm Γᴳᴸ k) (x : ℍ) :
    conj (CuspForm.peterssonOnIntegrand Γ k ⇑g ⇑f x) = CuspForm.peterssonOnIntegrand Γ k ⇑f ⇑g x := by
  rw [integrand_eq, integrand_eq]
  exact cosum_conj ⇑f ⇑g x

/--
@isnad1 id=eq.0h4v.s10.a930d13d5d4f from=translated src=- shape=ca398e2f vocab=5def7287
-/
theorem peterssonOn_conj_symm (f g : CuspForm Γᴳᴸ k) :
    conj (CuspForm.peterssonOn Γ k g f) = CuspForm.peterssonOn Γ k f g := by
  rw [CuspForm.peterssonOn_def, CuspForm.peterssonOn_def]
  have h := integral_conj (μ := volume.restrict (𝒟 : Set ℍ)) (𝕜 := ℂ)
    (f := CuspForm.peterssonOnIntegrand Γ k ⇑g ⇑f)
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => integrand_conj f g x)

end PetOnIP
open scoped _root_.P2MW.S_CuspForm_peterssonOn_add_smul_conj.PetOnIP

end
open scoped _root_.P2MW.S_CuspForm_peterssonOn_add_smul_conj.PetOnIP

open scoped MatrixGroups in
/--
@isnad1 id=and.0h6v.s12.62d756228290 from=translated src=- shape=fcfa8a34 vocab=df88a663
-/
theorem solution (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ)
    (f g h : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (c : ℂ) :
    CuspForm.peterssonOn Γ k f (g + h) = CuspForm.peterssonOn Γ k f g + CuspForm.peterssonOn Γ k f h ∧
    CuspForm.peterssonOn Γ k f (c • g) = c * CuspForm.peterssonOn Γ k f g ∧
    starRingEnd ℂ (CuspForm.peterssonOn Γ k g f) = CuspForm.peterssonOn Γ k f g :=
  ⟨PetOnIP.peterssonOn_add_right f g h, PetOnIP.peterssonOn_smul_right c f g,
    PetOnIP.peterssonOn_conj_symm f g⟩

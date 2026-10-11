import Tengoku.OpenaiMath.OAI.Analysis.TracialSplitting.GNSRepresentations

namespace OAI

noncomputable section

universe uA uB uE

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

namespace CurrentMain

open scoped ComplexOrder ComplexStarModule

variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

def selfAdjointFunctionalComplex (f : selfAdjoint A →ₗ[ℝ] ℝ) : A →ₗ[ℂ] ℂ where
  toFun a := (f (ℜ a) : ℂ) + Complex.I * (f (ℑ a) : ℂ)
  map_add' a b := by simp only [map_add, Complex.ofReal_add]; ring
  map_smul' z a := by
    simp only [realPart_smul, imaginaryPart_smul, map_sub, map_add, map_smul,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, smul_eq_mul]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

omit [PartialOrder A] [StarOrderedRing A] in
lemma selfAdjointFunctionalComplex_apply (f : selfAdjoint A →ₗ[ℝ] ℝ)
    (a : selfAdjoint A) : selfAdjointFunctionalComplex f a = (f a : ℂ) := by
  have hr : ℜ (a : A) = a := Subtype.ext a.property.coe_realPart
  simp [selfAdjointFunctionalComplex, hr, a.property.imaginaryPart]

lemma selfAdjointFunctional_nonneg (f : selfAdjoint A →L[ℝ] ℝ)
    (hn : ‖f‖ ≤ 1) (h1 : f 1 = 1) (a : selfAdjoint A) (ha : 0 ≤ (a : A)) :
    0 ≤ f a := by
  by_cases hz : a = 0
  · simp [hz]
  have hp : 0 < ‖(a : A)‖ := norm_pos_iff.mpr (fun h => hz (Subtype.ext h))
  let b : selfAdjoint A := ‖(a : A)‖⁻¹ • a
  have hb0 : 0 ≤ (b : A) := smul_nonneg (by positivity) ha
  have hbn : ‖(b : A)‖ ≤ 1 := by
    change ‖‖(a : A)‖⁻¹ • (a : A)‖ ≤ 1
    simp [norm_smul, inv_mul_cancel₀ hp.ne']
  have hb1 : (b : A) ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hb0).mp hbn
  have hsub : ‖(1 : selfAdjoint A) - b‖ ≤ 1 := by
    change ‖(1 : A) - (b : A)‖ ≤ 1
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (sub_nonneg.mpr hb1)).mpr
      (sub_le_self _ hb0)
  have hf : ‖f (1 - b)‖ ≤ 1 :=
    (f.le_opNorm _).trans ((mul_le_mul hn hsub (norm_nonneg _) zero_le_one).trans_eq (mul_one 1))
  have hfb : 0 ≤ f b := by
    have := le_abs_self (f (1 - b))
    rw [map_sub, h1] at hf this
    change |1 - f b| ≤ 1 at hf
    linarith
  change 0 ≤ f (‖(a : A)‖⁻¹ • a) at hfb
  rw [map_smul, smul_eq_mul] at hfb
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hp)).mp hfb

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
def selfAdjointEmbedding (ι : A →⋆ₐ[ℂ] B) (hi : Function.Injective ι) :
    selfAdjoint A →ₗᵢ[ℝ] selfAdjoint B where
  toFun a := ⟨ι a,by change star (ι a) = ι a; rw [← map_star,a.property.star_eq]⟩
  map_add' a b := Subtype.ext (map_add ι (a : A) (b : A))
  map_smul' c a := Subtype.ext (by
    change ι (c • (a : A)) = c • ι a
    rw [← Complex.coe_smul, map_smul, Complex.coe_smul])
  norm_map' a := (NonUnitalStarAlgHom.isometry ι hi).norm_map_of_map_zero (map_zero ι) (a : A)

omit [PartialOrder B] [StarOrderedRing B] in
lemma state_realPart_bound (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) (a : selfAdjoint A) :
    |(f a).re| ≤ ‖a‖ := by
  have hu (b : selfAdjoint A) : (f b).re ≤ ‖b‖ := by
    have h := f.apply_le_of_isSelfAdjoint b b.property
    have he : f (algebraMap ℝ A ‖(b : A)‖) = (‖b‖ : ℂ) := by
      rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, map_smul, hf]
      simp
    rw [he] at h
    exact h.1
  refine abs_le.mpr ⟨?_,hu a⟩
  have h := hu (-a)
  change (f (-(a : A))).re ≤ ‖-a‖ at h
  simp only [map_neg,Complex.neg_re,norm_neg] at h
  linarith

omit [PartialOrder B] [StarOrderedRing B] in
def stateRealLinear (f : A →ₚ[ℂ] ℂ) : selfAdjoint A →ₗ[ℝ] ℝ :=
  Complex.reCLM.toLinearMap.comp
    (((f : A →ₗ[ℂ] ℂ).restrictScalars ℝ).comp (selfAdjoint.submodule ℝ A).subtype)

omit [PartialOrder B] [StarOrderedRing B] in
def stateRealContinuous (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) : selfAdjoint A →L[ℝ] ℝ :=
  (stateRealLinear f).mkContinuous 1 (fun a => by
    change |(f a).re| ≤ 1 * ‖a‖
    simpa only [one_mul] using state_realPart_bound f hf a)

theorem state_extension (ι : A →⋆ₐ[ℂ] B) (hi : Function.Injective ι)
    (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) :
    ∃ g : B →ₚ[ℂ] ℂ, g 1 = 1 ∧ ∀ a, g (ι a) = f a := by
  let L := selfAdjointEmbedding ι hi
  let F := stateRealContinuous f hf
  let E := L.equivRange
  let S : Submodule ℝ (selfAdjoint B) := L.range
  let _ : NormedAddCommGroup S := inferInstance
  let _ : NormedSpace ℝ S :=
    { norm_smul_le := fun r a => norm_smul_le r ((a : selfAdjoint B) : B) }
  let Fr : S →L[ℝ] ℝ := F.comp E.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hFr : ‖Fr‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro a
    change |(f (E.symm a)).re| ≤ 1 * ‖a‖
    simpa only [one_mul,E.symm.norm_map] using state_realPart_bound f hf (E.symm a)
  obtain ⟨G,hG,hGn⟩ := exists_extension_norm_eq S Fr
  have hGa (a : selfAdjoint A) : G (L a) = (f a).re := by
    have h := hG (E a)
    change G (L a) = F (E.symm (E a)) at h
    rw [E.symm_apply_apply] at h
    exact h
  have hG1 : G 1 = 1 := by
    have h := hGa 1
    have he : L 1 = 1 := Subtype.ext (map_one ι)
    rw [he] at h
    simpa [hf] using h
  let gL := selfAdjointFunctionalComplex G.toLinearMap
  have hgpos (b : B) (hb : 0 ≤ b) : 0 ≤ gL b := by
    have h := selfAdjointFunctional_nonneg G (hGn.le.trans hFr) hG1
      ⟨b,.of_nonneg hb⟩ hb
    change 0 ≤ selfAdjointFunctionalComplex G.toLinearMap
      ((⟨b,.of_nonneg hb⟩ : selfAdjoint B) : B)
    rw [selfAdjointFunctionalComplex_apply]
    exact_mod_cast h
  let g : B →ₚ[ℂ] ℂ :=
    { toLinearMap := gL
      monotone' := by
        intro a b hab
        have h := hgpos (b-a) (sub_nonneg.mpr hab)
        rw [map_sub] at h
        exact sub_nonneg.mp h }
  have hga (a : selfAdjoint A) : g (ι a) = f a := by
    change selfAdjointFunctionalComplex G.toLinearMap ((L a : selfAdjoint B) : B) = f a
    rw [selfAdjointFunctionalComplex_apply]
    change (G (L a) : ℂ) = f a
    rw [hGa]
    exact (Complex.ext rfl (by
      have hsa : IsSelfAdjoint (f a) := a.property.map f
      have he := congrArg Complex.im hsa
      simp only [Complex.star_def,Complex.conj_im] at he
      change 0 = (f a).im
      linarith))
  refine ⟨g, ?_, ?_⟩
  · have h := hga 1
    change g (ι 1) = f 1 at h
    simpa only [map_one,hf] using h
  · intro a
    have ha : a = (ℜ a : A) + Complex.I • (ℑ a : A) := by
      exact (realPart_add_I_smul_imaginaryPart a).symm
    conv_lhs => rw [ha]
    rw [map_add,map_smul,map_add,map_smul,hga,hga]
    rw [← map_smul,← map_add,← ha]

end CurrentMain

open scoped ComplexOrder InnerProductSpace

namespace NuclearTrace

section NullVectors

variable {E : Type uE} [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]

variable (σ : E →ₚ[ℂ] ℂ)

end NullVectors
section

variable {A : Type uA} {E : Type uE} [CStarAlgebra A] [CStarAlgebra E]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder E] [StarOrderedRing E]

variable (α : A →⋆ₐ[ℂ] E) (β : Aᵐᵒᵖ →⋆ₐ[ℂ] E)

variable (hc : ∀ a b, Commute (α a) (β b))

variable (f : A →ₚ[ℂ] ℂ) (σ : E →ₚ[ℂ] ℂ)

variable (hd : ∀ a b, σ (α a*β (MulOpposite.op b)) = f (a*b))

omit [StarOrderedRing A] [StarOrderedRing E] in
include hd in
lemma diagonal_left (a : A) : σ (α a) = f a := by
  simpa only [MulOpposite.op_one,map_one,mul_one] using hd a 1

omit [StarOrderedRing A] [StarOrderedRing E] in
include hd in
lemma diagonal_right (a : A) : σ (β (MulOpposite.op a)) = f a := by
  simpa only [map_one,one_mul] using hd 1 a

end

open scoped TensorProduct ComplexOrder

variable {A N : Type} [CStarAlgebra A] [CStarAlgebra N]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder N] [StarOrderedRing N]

variable (f : A →ₚ[ℂ] ℂ) (ht : ∀ a b, f (a*b) = f (b*a))

end NuclearTrace

end

end OAI

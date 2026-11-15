import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open MonoidWithZeroHom WithZeroTopology UniformSpace

namespace ValuationSubring

variable {K : Type*} [Field K] (A : ValuationSubring K) (F : Type*) [Field F] [Algebra F K]

def DecompositionIsometric : Prop :=
  ∀ (σ : A.decompositionSubgroup F) (x : K),
    A.valuation ((σ : K ≃ₐ[F] K) x) = A.valuation x

variable {A F}

/--
@isnad1 id=charzero.0h2v.s7.f91c91e1097a from=translated src=- shape=048aa98d vocab=b089b0c4
-/
instance charZero_completion [CharZero K] : CharZero A.valuation.Completion :=
  charZero_of_injective_ringHom
    (UniformSpace.Completion.coeRingHom (α := WithVal A.valuation)).injective

/--
@isnad1 id=eq.0h5v.s11.80c82b426542 from=translated src=- shape=4734f74a vocab=1b438c76
-/
theorem smul_withVal_def (σ : A.decompositionSubgroup F) (x : WithVal A.valuation) :
    σ • x = WithVal.toVal A.valuation ((σ : K ≃ₐ[F] K) x.ofVal) := rfl

instance mulSemiringActionWithVal :
    MulSemiringAction (A.decompositionSubgroup F) (WithVal A.valuation) where
  one_smul x := by rw [smul_withVal_def]; rfl
  mul_smul σ τ x := by simp only [smul_withVal_def]; rfl
  smul_zero σ := by rw [smul_withVal_def, WithVal.ofVal_zero, map_zero]; rfl
  smul_add σ x y := by simp only [smul_withVal_def, WithVal.ofVal_add, map_add]; rfl
  smul_one σ := by rw [smul_withVal_def, WithVal.ofVal_one, map_one]; rfl
  smul_mul σ x y := by simp only [smul_withVal_def, WithVal.ofVal_mul, map_mul]; rfl

/--
@isnad1 id=eq.1h5v.s11.fc8cd8f13603 from=translated src=- shape=8a7b67a1 vocab=748ad1f2
-/
theorem valued_smul_withVal (h : A.DecompositionIsometric F) (σ : A.decompositionSubgroup F)
    (x : WithVal A.valuation) : Valued.v (σ • x) = Valued.v x := by
  rw [smul_withVal_def]
  change A.valuation ((σ : K ≃ₐ[F] K) x.ofVal) = A.valuation x.ofVal
  exact h σ _

/--
@isnad1 id=continuo.1h4v.s10.5a5ffe069e81 from=translated src=- shape=8ed33fed vocab=7a81b0e2
-/
theorem continuous_smul_withVal (h : A.DecompositionIsometric F) (σ : A.decompositionSubgroup F) :
    Continuous (fun x : WithVal A.valuation => σ • x) := by
  let f : WithVal A.valuation →+* WithVal A.valuation :=
    MulSemiringAction.toRingHom (A.decompositionSubgroup F) (WithVal A.valuation) σ
  change Continuous f
  apply continuous_of_continuousAt_zero f
  rw [ContinuousAt, map_zero]
  refine ((Valued.hasBasis_nhds_zero (WithVal A.valuation) A.ValueGroup).tendsto_iff
    (Valued.hasBasis_nhds_zero (WithVal A.valuation) A.ValueGroup)).mpr
    fun γ _ => ⟨γ, trivial, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq] at hx ⊢
  have hres : Valued.v.restrict (f x) = Valued.v.restrict x :=
    (Valuation.restrict_inj _).mpr (valued_smul_withVal h σ x)
  rw [hres]
  exact hx

/--
@isnad1 id=uniformc.0h3v.s10.49e5361a3296 from=translated src=- shape=bc227975 vocab=feec7702
-/
instance uniformContinuousConstSMul_withVal [h : Fact (A.DecompositionIsometric F)] :
    UniformContinuousConstSMul (A.decompositionSubgroup F) (WithVal A.valuation) :=
  ⟨fun σ => uniformContinuous_addMonoidHom_of_continuous
    (f := (MulSemiringAction.toRingHom (A.decompositionSubgroup F) (WithVal A.valuation) σ :
      WithVal A.valuation →+ WithVal A.valuation)) (continuous_smul_withVal h.out σ)⟩

section Completion

variable [h : Fact (A.DecompositionIsometric F)]

/--
@isnad1 id=eq.0h5v.s11.8e822fc016a7 from=translated src=- shape=f809f5f7 vocab=cec8d30e
-/
theorem smul_completion_coe (σ : A.decompositionSubgroup F) (a : K) :
    σ • ((a : K) : A.valuation.Completion) =
      (((σ : K ≃ₐ[F] K) a : K) : A.valuation.Completion) :=
  (Completion.coe_smul σ (WithVal.toVal A.valuation a)).symm

omit h in

/--
@isnad1 id=continuo.0h4v.s11.fe2a4123b6f7 from=translated src=- shape=c15f3db6 vocab=76c3123a
-/
theorem continuous_smul_completion (σ : A.decompositionSubgroup F) :
    Continuous (fun x : A.valuation.Completion => σ • x) :=
  continuous_const_smul σ

instance mulSemiringActionCompletion :
    MulSemiringAction (A.decompositionSubgroup F) A.valuation.Completion :=
  { (inferInstance : DistribMulAction (A.decompositionSubgroup F) A.valuation.Completion) with
    smul_one := fun σ => by
      rw [← Completion.coe_one, ← Completion.coe_smul, smul_one]
    smul_mul := fun σ x y =>
      Completion.induction_on₂ x y
        (isClosed_eq ((continuous_fst.fun_mul continuous_snd).fun_const_smul (σ : A.decompositionSubgroup F))
          ((continuous_fst.fun_const_smul (σ : A.decompositionSubgroup F)).fun_mul
            (continuous_snd.fun_const_smul (σ : A.decompositionSubgroup F))))
        fun a b => by simp only [← Completion.coe_mul, ← Completion.coe_smul, smul_mul'] }

/--
@isnad1 id=eq.0h5v.s11.bb0946bfd882 from=translated src=- shape=93113803 vocab=03c7a961
-/
theorem valuation_smul_completion (σ : A.decompositionSubgroup F) (x : A.valuation.Completion) :
    Valued.v (σ • x) = Valued.v x := by
  rw [← Valuation.restrict_inj]
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq ((Valued.continuous_valuation (K := A.valuation.Completion)).comp
      (continuous_smul_completion σ)) (Valued.continuous_valuation (K := A.valuation.Completion))
  | ih a =>
    rw [Valuation.restrict_inj, ← Completion.coe_smul, Valued.valuedCompletion_apply,
      Valued.valuedCompletion_apply]
    exact valued_smul_withVal h.out σ a

theorem eq_smul_completion_of_continuous (σ : A.decompositionSubgroup F)
    (g : A.valuation.Completion →+* A.valuation.Completion) (hg : Continuous g)
    (hext : ∀ a : K, g ((a : K) : A.valuation.Completion) =
      (((σ : K ≃ₐ[F] K) a : K) : A.valuation.Completion)) (x : A.valuation.Completion) :
    g x = σ • x := by
  refine congrFun (Completion.ext hg (continuous_smul_completion σ) fun a => ?_) x
  refine (hext (WithVal.equiv A.valuation a)).trans ?_
  exact (smul_completion_coe σ _).symm

def completionRingAut :
    A.decompositionSubgroup F →* (A.valuation.Completion ≃+* A.valuation.Completion) :=
  MulSemiringAction.toRingAut (A.decompositionSubgroup F) A.valuation.Completion

/--
@isnad1 id=eq.0h5v.s13.14046fa8bda9 from=translated src=- shape=ba25da93 vocab=1cfd15b5
-/
theorem completionRingAut_apply (σ : A.decompositionSubgroup F) (x : A.valuation.Completion) :
    completionRingAut σ x = σ • x := by
  simp only [completionRingAut, MulSemiringAction.toRingAut_apply,
    MulSemiringAction.toRingEquiv_apply_apply]

end Completion

end ValuationSubring

end

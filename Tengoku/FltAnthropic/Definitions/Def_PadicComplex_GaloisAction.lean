import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_CompletionBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open UniformSpace

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]

abbrev Gal : Type := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p

/--
@isnad1 id=isometry.0h2v.s7.7c53bf3799b2 from=translated src=- shape=4548bfae vocab=f7eb1f2e
-/
theorem isometry_algEquiv (σ : Gal p) : Isometry σ := by
  refine AddMonoidHomClass.isometry_of_norm σ fun x => ?_
  exact (spectralNorm_eq_of_equiv σ x).symm

/--
@isnad1 id=uniformc.0h1v.s8.11dc577de938 from=translated src=- shape=7e6de1f7 vocab=9b889e8f
-/
instance uniformContinuousConstSMul_gal :
    UniformContinuousConstSMul (Gal p) (PadicAlgCl p) :=
  ⟨fun σ => (isometry_algEquiv p σ).uniformContinuous⟩

/--
@isnad1 id=eq.0h3v.s9.2216067a42d7 from=translated src=- shape=808609bf vocab=5968f306
-/
@[simp]
theorem smul_coe (σ : Gal p) (x : PadicAlgCl p) :
    σ • ((x : ℂ_[p])) = ((σ x : PadicAlgCl p) : ℂ_[p]) :=
  (Completion.coe_smul σ x).symm

/--
@isnad1 id=continuo.0h2v.s8.ec1b1280f7fb from=translated src=- shape=56da85e8 vocab=a1b7bfc5
-/
theorem continuous_smul_left (σ : Gal p) : Continuous fun x : ℂ_[p] => σ • x :=
  continuous_const_smul σ

/--
@isnad1 id=uniformc.0h2v.s8.62488cbe18d8 from=translated src=- shape=56da85e8 vocab=e6e0802a
-/
theorem uniformContinuous_smul_left (σ : Gal p) : UniformContinuous fun x : ℂ_[p] => σ • x :=
  uniformContinuous_const_smul σ

instance mulSemiringAction : MulSemiringAction (Gal p) ℂ_[p] :=
  { (inferInstance : DistribMulAction (Gal p) ℂ_[p]) with
    smul_one := fun σ => by
      rw [← Completion.coe_one, smul_coe, map_one]
    smul_mul := fun σ x y => by
      refine Completion.induction_on₂ x y ?_ ?_
      · exact isClosed_eq ((continuous_fst.mul continuous_snd).const_smul σ)
          ((continuous_fst.const_smul σ).mul (continuous_snd.const_smul σ))
      · intro a b
        rw [← Completion.coe_mul, smul_coe, smul_coe, smul_coe, map_mul, Completion.coe_mul] }

/--
@isnad1 id=eq.0h3v.s8.4db9dea5112c from=translated src=- shape=c0a9518f vocab=9d1d04dc
-/
@[simp]
theorem norm_smul_eq (σ : Gal p) (x : ℂ_[p]) : ‖σ • x‖ = ‖x‖ := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq ((continuous_norm).comp (continuous_const_smul σ)) continuous_norm
  · intro a
    rw [smul_coe, norm_extends, norm_extends]
    exact (spectralNorm_eq_of_equiv σ a).symm

/--
@isnad1 id=eq.0h3v.s8.ff84a5e51e35 from=translated src=- shape=c0a9518f vocab=9cdc23f8
-/
@[simp]
theorem nnnorm_smul_eq (σ : Gal p) (x : ℂ_[p]) : ‖σ • x‖₊ = ‖x‖₊ :=
  NNReal.eq (norm_smul_eq p σ x)

/--
@isnad1 id=isometry.0h2v.s8.f1570011b696 from=translated src=- shape=56da85e8 vocab=ddd6052c
-/
theorem isometry_smul (σ : Gal p) : Isometry fun x : ℂ_[p] => σ • x :=
  AddMonoidHomClass.isometry_of_norm (MulSemiringAction.toRingHom (Gal p) ℂ_[p] σ)
    (norm_smul_eq p σ)

/--
@isnad1 id=smulcomm.0h1v.s8.44d8c3ba2dca from=translated src=- shape=505a8ccf vocab=4d2859d0
-/
instance smulCommClass_gal_padic : SMulCommClass (Gal p) ℚ_[p] ℂ_[p] :=
  inferInstance

/--
@isnad1 id=smulcomm.0h1v.s8.54ab99ecfcda from=translated src=- shape=505a8ccf vocab=4d2859d0
-/
instance smulCommClass_padic_gal : SMulCommClass ℚ_[p] (Gal p) ℂ_[p] :=
  SMulCommClass.symm _ _ _

/--
@isnad1 id=eq.0h3v.s10.952c04457eaf from=translated src=- shape=155a46df vocab=78bb6319
-/
@[simp]
theorem smul_algebraMap (σ : Gal p) (q : ℚ_[p]) :
    σ • (algebraMap ℚ_[p] ℂ_[p] q) = algebraMap ℚ_[p] ℂ_[p] q := by
  rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

abbrev galAlgHom (σ : Gal p) : ℂ_[p] →ₐ[ℚ_[p]] ℂ_[p] :=
  MulSemiringAction.toAlgHom ℚ_[p] ℂ_[p] σ

/--
@isnad1 id=eq.0h3v.s9.7e7630764fdd from=translated src=- shape=fdb89dfc vocab=823cfc07
-/
@[simp]
theorem galAlgHom_apply (σ : Gal p) (x : ℂ_[p]) : galAlgHom p σ x = σ • x := rfl

/--
@isnad1 id=eq.0h3v.s11.2f917bf2a231 from=translated src=- shape=470440b0 vocab=11ba1526
-/
theorem smul_coe_padicEmbedding (σ : Gal p) (a : AlgebraicClosure ℚ) :
    σ • ((padicEmbedding p a : PadicAlgCl p) : ℂ_[p]) =
      ((padicEmbedding p (localGaloisToGlobal p σ a) : PadicAlgCl p) : ℂ_[p]) := by
  rw [smul_coe, padicEmbedding_localGaloisToGlobal]

end PadicComplex

end

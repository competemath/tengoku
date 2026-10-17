import Tengoku.OpenaiMath.OAI.Analysis.C0Absorption.Shift

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

def baseRepresentation (γ : Label) : GeneratedRepresentation concreteBases γ where
  operations := []
  ordered := by simp
  budget := by simpa only [List.map_nil,List.sum_nil] using half_pos (concreteBases.ell_pos (concreteBases.band γ))

/--
@isnad1 id=eq.0h1v.s4.eb1292888efd from=translated src=- shape=3da77df5 vocab=3bcaeae6
-/
theorem baseRepresentation_value (γ : Label) : (baseRepresentation γ).value=correction γ := by
  funext s
  change correctionBase γ (cubeRestrict (correctionCoordinates γ.level) s)=correction γ s
  exact correctionBase_restrict γ s

/--
@isnad1 id=mem.0h1v.s4.ffd9041e3267 from=translated src=- shape=cb271819 vocab=bb72eb17
-/
theorem correction_mem_TClass (γ : Label) : correction γ∈TClass concreteBases 0 :=
  ⟨γ,baseRepresentation γ,Nat.zero_le _,(baseRepresentation_value γ).symm⟩

def correctionDualBound : ℝ≥0 := Classical.choose (TClass_pairing_bound concreteBases 0)

/--
@isnad1 id=le.0h2v.s9.8cf40f5c33c1 from=translated src=- shape=dc35e930 vocab=c70d0619
-/
theorem correction_pairing_bound (γ : Label) (m : PreSpace (sourceClasses concreteBases) c0Origin) :
    |pairing C0Ball (correction γ) m|≤correctionDualBound*‖m‖ :=
  Classical.choose_spec (TClass_pairing_bound concreteBases 0) (correction γ) (correction_mem_TClass γ) m

def moleculeCorrection : Molecule C0Ball →ₗ[ℝ] BlockC0 :=
  (Finsupp.linearCombination ℝ correctionC0).comp (MoleculeSpace C0Ball).subtype

/--
@isnad1 id=eq.0h2v.s10.9193bab217ce from=translated src=- shape=d7753845 vocab=47f2ed9b
-/
theorem moleculeCorrection_apply (m : Molecule C0Ball) (γ : Label) :
    moleculeCorrection m γ=pairing C0Ball (correction γ) m := by
  classical
  simp only [moleculeCorrection,pairing,LinearMap.comp_apply,Submodule.subtype_apply,
    Finsupp.linearCombination_apply,Finsupp.sum]
  induction (m.val.support) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha,ZeroAtInftyContinuousMap.add_apply,
      ZeroAtInftyContinuousMap.smul_apply,smul_eq_mul,ih,correctionC0_apply]

def initialCorrection : PreSpace (sourceClasses concreteBases) c0Origin →L[ℝ] BlockC0 :=
  (show PreSpace (sourceClasses concreteBases) c0Origin →ₗ[ℝ] BlockC0 from by unfold PreSpace; exact moleculeCorrection).mkContinuous
    correctionDualBound (fun m => by
      apply cfun_norm_le _ (mul_nonneg correctionDualBound.coe_nonneg (norm_nonneg m))
      intro γ
      change |moleculeCorrection m γ|≤_
      exact (congrArg abs (moleculeCorrection_apply (show Molecule C0Ball from m) γ)).le.trans
        (correction_pairing_bound γ m))

def correctionQ : ConcreteSpace →L[ℝ] BlockC0 :=
  initialCorrection.extend (toTestSpace (sourceClasses concreteBases) c0Origin)

/--
@isnad1 id=eq.0h1v.s11.ee3046e00926 from=translated src=- shape=b0fe7fec vocab=0b8957b7
-/
theorem correctionQ_coe (m : PreSpace (sourceClasses concreteBases) c0Origin) :
    correctionQ (toTestSpace (sourceClasses concreteBases) c0Origin m)=moleculeCorrection m :=
  ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) m

/--
@isnad1 id=eq.0h0v.s4.409df6ce6ce6 from=translated src=- shape=b0ae1d2b vocab=b475d826
-/
theorem correctionC0_zero : correctionC0 c0Origin=0 := by
  ext γ
  exact correction_zero γ

/--
@isnad1 id=eq.0h1v.s8.20a7ff2fcad9 from=translated src=- shape=dab1dbc7 vocab=1c0372b4
-/
theorem correctionQ_zeta (s : C0Ball) :
    correctionQ (zeta (sourceClasses concreteBases) c0Origin s)=correctionC0 s := by
  rw [zeta,correctionQ_coe]
  change moleculeCorrection (molecule s c0Origin)=correctionC0 s
  simp only [moleculeCorrection,molecule,LinearMap.comp_apply,Submodule.subtype_apply,map_sub,
    Finsupp.linearCombination_single,one_smul,correctionC0_zero,sub_zero]

def concreteLift : C0 → ConcreteSpace := radialLift (zeta (sourceClasses concreteBases) c0Origin)

/--
@isnad1 id=lipschit.0h0v.s5.e3d1850d2766 from=translated src=- shape=c80f5d6d vocab=0ee6a895
-/
theorem concreteLift_lipschitz : LipschitzWith 3 concreteLift :=
  radialLift_lipschitz _ (zeta_lipschitz _ _) (zeta_base _ _)

/--
@isnad1 id=eq.0h1v.s9.e09c8ca948d6 from=translated src=- shape=9af5fef0 vocab=b4e0cd55
-/
theorem correctionQ_concreteLift (x : C0) : correctionQ (concreteLift x)=recomputedShift x-inputBlocks x := by
  rw [concreteLift,radialLift,map_smul,correctionQ_zeta]
  change ‖x‖ • (frozenCorrectionL (stateWeights (normalizedBall x)) (normalize x))=_
  rw [← map_smul,norm_smul_normalize]
  change frozenCorrectionL (stateWeights (normalizedBall x)) x=
    (inputBlocks x+frozenCorrectionL (stateWeights (normalizedBall x)) x)-inputBlocks x
  abel

end
end C0Absorption

end OAI

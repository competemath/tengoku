module
public import Tengoku.Seed.RingTheory.AdicCompletion.Completeness
public import Tengoku.Seed.RingTheory.AdicCompletion.RingHom
public import Tengoku.Seed.RingTheory.Smooth.AdicCompletion
public import Tengoku.Seed.RingTheory.Etale.Basic
public import Tengoku.Stafford38Formal.Stafford38.Geometry.AdicCompletionMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Stafford38.Geometry.FormallyEtaleCompletion

noncomputable section

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  (I : Ideal A) (J : Ideal B)

/-- Formal smoothness lifts a residue map from an algebra to the completion of its base.
@isnad1 id=ex.0h4v.s9.834203b4e342 from=translated src=- shape=c8628555 vocab=b9ed8a4f
-/
theorem exists_formalSmooth_lift_to_baseCompletion [Algebra.FormallySmooth A B]
    (r : B →ₐ[A] A ⧸ I) :
    ∃ ψ : B →ₐ[A] AdicCompletion I A,
      ((AdicCompletion.evalOneₐ I).restrictScalars A).comp ψ = r := by
  exact Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq r

/-- The ideal extension identity forced by an `A`-algebra map into `Â`.
@isnad1 id=eq.1h5v.s10.b1d20724429e from=translated src=- shape=ae095d86 vocab=7fb53e2b
-/
theorem extendedIdeal_eq_map_of_lift (hJ : J = I.map (algebraMap A B))
    (ψ : B →ₐ[A] AdicCompletion I A) :
    I.map (algebraMap A (AdicCompletion I A)) = J.map (ψ : B →+* AdicCompletion I A) := by
  have hcomp : (ψ : B →+* AdicCompletion I A).comp (algebraMap A B) =
      algebraMap A (AdicCompletion I A) := by
    exact RingHom.ext fun a => ψ.commutes a
  calc
    I.map (algebraMap A (AdicCompletion I A)) =
        I.map ((ψ : B →+* AdicCompletion I A).comp (algebraMap A B)) := by
      rw [hcomp]
    _ = (I.map (algebraMap A B)).map (ψ : B →+* AdicCompletion I A) := by
      rw [Ideal.map_map]
    _ = J.map (ψ : B →+* AdicCompletion I A) := by rw [← hJ]

/-- A formal-smooth lift to `Â` extends continuously to the completion at an ideal
which is the extension of the base ideal.-/
def extendFormalSmoothLift (hJ : J = I.map (algebraMap A B))
    (hfg : I.FG) (ψ : B →ₐ[A] AdicCompletion I A) :
    AdicCompletion J B →+* AdicCompletion I A := by
  let IC : Ideal (AdicCompletion I A) := I.map (algebraMap A (AdicCompletion I A))
  have hIC : IC = J.map (ψ : B →+* AdicCompletion I A) := by
    simpa [IC] using extendedIdeal_eq_map_of_lift I J hJ ψ
  letI : IsAdicComplete IC (AdicCompletion I A) := by
    rw [IsAdicComplete.map_algebraMap_iff]
    exact AdicCompletion.isAdicComplete hfg
  let e : AdicCompletion I A ≃ₐ[AdicCompletion I A]
      AdicCompletion IC (AdicCompletion I A) := AdicCompletion.ofAlgEquiv IC
  exact (e.symm : AdicCompletion IC (AdicCompletion I A) →+* AdicCompletion I A).comp
      (Stafford38.Geometry.AdicCompletionMap.mapOfRingHom
        (ψ : B →+* AdicCompletion I A) J IC hIC)

/-- The extension agrees with the chosen formal-smooth lift on the dense base ring.
@isnad1 id=eq.2h6v.s10.1a8194727e13 from=translated src=- shape=bd290e65 vocab=a7496d94
-/
theorem extendFormalSmoothLift_apply_of (hJ : J = I.map (algebraMap A B))
    (hfg : I.FG) (ψ : B →ₐ[A] AdicCompletion I A) (b : B) :
    extendFormalSmoothLift I J hJ hfg ψ (AdicCompletion.of J B b) = ψ b := by
  let IC : Ideal (AdicCompletion I A) := I.map (algebraMap A (AdicCompletion I A))
  have hIC : IC = J.map (ψ : B →+* AdicCompletion I A) := by
    simpa [IC] using extendedIdeal_eq_map_of_lift I J hJ ψ
  letI : IsAdicComplete IC (AdicCompletion I A) := by
    rw [IsAdicComplete.map_algebraMap_iff]
    exact AdicCompletion.isAdicComplete hfg
  let e : AdicCompletion I A ≃ₐ[AdicCompletion I A]
      AdicCompletion IC (AdicCompletion I A) := AdicCompletion.ofAlgEquiv IC
  apply e.injective
  simp [extendFormalSmoothLift, IC, hIC,
    Stafford38.Geometry.AdicCompletionMap.mapOfRingHom_apply_of]

end
end Stafford38.Geometry.FormallyEtaleCompletion

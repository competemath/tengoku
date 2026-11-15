import Tengoku.Seed.FieldTheory.IsAlgClosed.AlgebraicClosure
import Tengoku.Seed.RingTheory.Localization.FractionRing
import Tengoku.Seed.Algebra.Polynomial.AlgebraMap
import Tengoku.Seed.Algebra.Algebra.Rat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace RatFuncTower

abbrev K0 : Type := FractionRing (Polynomial (AlgebraicClosure ℚ))

scoped instance algebraRatPoly : Algebra (Polynomial ℚ) K0 :=
  ((algebraMap (Polynomial (AlgebraicClosure ℚ)) K0).comp
    (Polynomial.mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))).toAlgebra

/--
@isnad1 id=eq.0h1v.s11.555628c0b012 from=translated src=- shape=74c2882c vocab=18952cf8
-/
theorem algebraMap_ratPoly_apply (p : Polynomial ℚ) :
    algebraMap (Polynomial ℚ) K0 p =
      algebraMap (Polynomial (AlgebraicClosure ℚ)) K0
        (p.map (algebraMap ℚ (AlgebraicClosure ℚ))) := rfl

def galLift (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : K0 ≃ₐ[Polynomial ℚ] K0 :=
  AlgEquiv.ofRingEquiv
    (f := IsFractionRing.ringEquivOfRingEquiv
      (A := Polynomial (AlgebraicClosure ℚ)) (B := Polynomial (AlgebraicClosure ℚ))
      (K := K0) (L := K0) (Polynomial.mapAlgEquiv σ).toRingEquiv)
    (by
      intro p
      have hq : ∀ q : Polynomial (AlgebraicClosure ℚ),
          (Polynomial.mapAlgEquiv σ).toRingEquiv q =
            q.map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) := fun q => rfl
      rw [algebraMap_ratPoly_apply, IsFractionRing.ringEquivOfRingEquiv_algebraMap, hq,
        Polynomial.map_map]
      congr 2
      ext x
      simp)

/--
@isnad1 id=eq.0h2v.s11.80911fab4300 from=translated src=- shape=d8e8081f vocab=e57f6296
-/
theorem galLift_algebraMap (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (p : Polynomial (AlgebraicClosure ℚ)) :
    galLift σ (algebraMap (Polynomial (AlgebraicClosure ℚ)) K0 p) =
      algebraMap (Polynomial (AlgebraicClosure ℚ)) K0
        (p.map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) := by
  simp [galLift]

end RatFuncTower

end

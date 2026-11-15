import Tengoku.Seed.AlgebraicGeometry.Pullbacks
import Tengoku.Seed.AlgebraicGeometry.Morphisms.ClosedImmersion
import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (I : Ideal R)

abbrev adicThickeningBase (n : ℕ) : Spec (.of (R ⧸ I ^ (n + 1))) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))

def adicThickening (n : ℕ) : Scheme.{u} := pullback f (adicThickeningBase I n)

def adicThickeningι (n : ℕ) : adicThickening f I n ⟶ X := pullback.fst f (adicThickeningBase I n)

def adicThickeningToBase (n : ℕ) : adicThickening f I n ⟶ Spec (.of (R ⧸ I ^ (n + 1))) :=
  pullback.snd f (adicThickeningBase I n)

/--
@isnad1 id=eq.0h5v.s7.aef317d69f3b from=translated src=- shape=cc7117a5 vocab=89a2a26b
-/
theorem adicThickeningι_comp (n : ℕ) :
    adicThickeningι f I n ≫ f = adicThickeningToBase f I n ≫ adicThickeningBase I n :=
  pullback.condition

/--
@isnad1 id=eq.0h3v.s10.8595b817e844 from=translated src=- shape=d0f97f71 vocab=67efae69
-/
theorem adicThickeningBase_succ_comp (n : ℕ) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))) ≫
      adicThickeningBase I (n + 1) = adicThickeningBase I n := by
  rw [adicThickeningBase, adicThickeningBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Ideal.Quotient.factor_comp_mk]

def adicThickeningTransition (n : ℕ) : adicThickening f I n ⟶ adicThickening f I (n + 1) :=
  pullback.lift (adicThickeningι f I n)
    (adicThickeningToBase f I n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))))
    (by rw [adicThickeningι_comp, Category.assoc, adicThickeningBase_succ_comp])

/--
@isnad1 id=eq.0h5v.s6.10899b54ad8d from=translated src=- shape=a81fc2bf vocab=45fec5f4
-/
@[simp] theorem adicThickeningTransition_ι (n : ℕ) :
    adicThickeningTransition f I n ≫ adicThickeningι f I (n + 1) = adicThickeningι f I n := by
  rw [adicThickeningTransition]; exact pullback.lift_fst _ _ _

/--
@isnad1 id=eq.0h5v.s10.815c90730b02 from=translated src=- shape=0b16c544 vocab=94007264
-/
theorem adicThickeningTransition_toBase (n : ℕ) :
    adicThickeningTransition f I n ≫ adicThickeningToBase f I (n + 1) =
      adicThickeningToBase f I n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))) := by
  rw [adicThickeningTransition]; exact pullback.lift_snd _ _ _

/--
@isnad1 id=eq.0h5v.s7.a047fa149af2 from=translated src=- shape=0d5c33e7 vocab=eddff4de
-/
theorem adicThickening_def (n : ℕ) : adicThickening f I n = pullback f (adicThickeningBase I n) := rfl
/--
@isnad1 id=eq.0h5v.s8.e5f35bbbfad6 from=translated src=- shape=3acca2da vocab=1b9800d7
-/
theorem adicThickeningToBase_def (n : ℕ) :
    adicThickeningToBase f I n = pullback.snd f (adicThickeningBase I n) := rfl

end AlgebraicGeometry

end

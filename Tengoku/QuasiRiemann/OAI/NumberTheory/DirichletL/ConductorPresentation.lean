import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.ConductorBounds
import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.CharacterTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

namespace SevenEighths

namespace FiniteConductor

variable {R : Type*} [CommRing R] [Finite R]

/--
@isnad1 id=factorst.0h2v.s5.a9328135a5a5 from=translated src=- shape=f3c77f23 vocab=bc7baf76
-/
theorem FactorsThroughIdeal.bot (χ : MulChar R ℂ) : FactorsThroughIdeal χ ⊥ := by
  rw [factorsThroughIdeal_iff]
  intro u hu
  have hu1 : (u : R) = 1 := sub_eq_zero.mp hu
  rw [hu1, map_one]

/--
@isnad1 id=factorst.1h4v.s7.f47f5fbd5b2f from=translated src=- shape=ad902cef vocab=384b2c14
-/
theorem FactorsThroughIdeal.pow {χ : MulChar R ℂ} {I : Ideal R}
    (hχ : FactorsThroughIdeal χ I) (n : ℕ) : FactorsThroughIdeal (χ ^ n) I := by
  rw [factorsThroughIdeal_iff] at hχ ⊢
  intro u hu
  rw [MulChar.pow_apply_coe, hχ u hu, one_pow]

end FiniteConductor

namespace ConductorPresentation

open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open scoped Classical

noncomputable section

section Transport

variable {A : Type*} [CommRing A]

def quotientCharacter (M : Ideal A) (I : Ideal (A ⧸ M))
    (φ : MulChar ((A ⧸ M) ⧸ I) ℂ) : MulChar (A ⧸ I.comap (Ideal.Quotient.mk M)) ℂ :=
  CharacterTransport.pullback (quotientComapEquiv M I) φ

/--
@isnad1 id=eq.0h5v.s12.f3b669f45325 from=translated src=- shape=a2291996 vocab=aa8fe931
-/
@[simp] theorem quotientCharacter_mk (M : Ideal A) (I : Ideal (A ⧸ M))
    (φ : MulChar ((A ⧸ M) ⧸ I) ℂ) (a : A) :
    quotientCharacter M I φ (Ideal.Quotient.mk _ a) =
      φ (Ideal.Quotient.mk I (Ideal.Quotient.mk M a)) := rfl

/--
@isnad1 id=isprimit.1h4v.s9.5bec43a7ba74 from=translated src=- shape=800894c0 vocab=66b8fca8
-/
theorem primitive_quotientCharacter (M : Ideal A) (I : Ideal (A ⧸ M))
    (φ : MulChar ((A ⧸ M) ⧸ I) ℂ) (hφ : IsPrimitiveOnIdeals φ) :
    IsPrimitiveOnIdeals (quotientCharacter M I φ) :=
  CharacterTransport.primitive_pullback _ _ hφ

/--
@isnad1 id=le.0h3v.s7.f564c3147eed from=translated src=- shape=a8bcb65f vocab=d8fbdf60
-/
theorem source_le_comap (M : Ideal A) (I : Ideal (A ⧸ M)) :
    M ≤ I.comap (Ideal.Quotient.mk M) := by
  intro a ha
  change Ideal.Quotient.mk M a ∈ I
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact I.zero_mem

/--
@isnad1 id=eq.2h5v.s11.d16e714f9aac from=translated src=- shape=64d2ac0c vocab=e9d0eb3e
-/
theorem unit_factorization_of_mask (M K : Ideal A) (hMK : M ≤ K)
    (χ : MulChar (A ⧸ M) ℂ) (φ : MulChar (A ⧸ K) ℂ)
    (hmask : ∀ a : A, χ (Ideal.Quotient.mk M a) =
      if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0) :
    φ.toUnitHom.comp (Units.map (Ideal.Quotient.factor hMK).toMonoidHom) =
      χ.toUnitHom := by
  apply MonoidHom.ext
  intro u
  apply Units.ext
  change φ (Ideal.Quotient.factor hMK (u : A ⧸ M)) = χ (u : A ⧸ M)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : A ⧸ M)
  have h := hmask a
  simp only [ha, u.isUnit, ite_true] at h
  simpa only [← ha, Ideal.Quotient.factor_mk] using h.symm

end Transport

variable {A : Type*} [CommRing A] [IsDedekindDomain A] [Infinite A]

end

end ConductorPresentation

end SevenEighths

end OAI

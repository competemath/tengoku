import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi

set_option autoImplicit false

open scoped TensorProduct

universe u

/--
@isnad1 id=ex.0h2v.s8.eb98aec54cc9 from=translated src=- shape=51e5cd06 vocab=c93ce0f2
-/
theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B] [Algebra.Etale R B] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Module.Finite R R')
      (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R') (_ : IsNoetherianRing R'),
      Nonempty ((R' ⊗[R] B) ≃ₐ[R'] (Fin (Module.finrank R B) → R')) := by
  haveI : Module.Free R B := Module.free_of_flat_of_isLocalRing
  obtain ⟨R', _, _, _, _, _, ⟨e⟩⟩ :=
    Algebra.Etale.exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq R B
      (Module.finrank R B) (fun p => by rw [Module.rankAtStalk_eq_finrank_of_free]; rfl)
  exact ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Algebra.FiniteType.isNoetherianRing R R', ⟨e⟩⟩

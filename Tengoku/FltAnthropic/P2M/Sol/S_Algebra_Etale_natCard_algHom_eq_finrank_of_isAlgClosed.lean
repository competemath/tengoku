import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed

set_option autoImplicit false

/--
@isnad1 id=eq.0h2v.s6.63eb8cd87179 from=translated src=- shape=31007b4a vocab=1bea3fe5
-/
theorem solution
    (k : Type*) [Field k] [IsAlgClosed k] (R : Type*) [CommRing R] [Algebra k R] [Algebra.Etale k R] :
    Nat.card (R →ₐ[k] k) = Module.finrank k R := by
  classical
  obtain ⟨ι, _, L, _, _, e, hL⟩ := (Algebra.Etale.iff_exists_algEquiv_prod k R).mp ‹_›
  haveI : Fintype ι := Fintype.ofFinite ι

  have hLk : ∀ i, Nonempty (L i ≃ₐ[k] k) := fun i => by
    haveI := (hL i).1
    haveI : Algebra.IsIntegral k (L i) := Algebra.IsIntegral.of_finite k (L i)
    exact ⟨(AlgEquiv.ofBijective (Algebra.ofId k (L i))
      IsAlgClosed.algebraMap_bijective_of_isIntegral).symm⟩

  let f : R ≃ₐ[k] (ι → k) := e.trans (AlgEquiv.piCongrRight fun i => (hLk i).some)
  have hrk : Module.finrank k R = Fintype.card ι := by
    rw [LinearEquiv.finrank_eq f.toLinearEquiv, Module.finrank_pi]

  have heval : Function.Bijective (fun i : ι => Pi.evalAlgHom k (fun _ => k) i) := by
    refine ⟨fun i j hij => ?_, fun φ => (AlgHom.eq_piEvalAlgHom φ).imp fun _ h => h.symm⟩
    have := DFunLike.congr_fun hij (Pi.single i 1)
    simp only [Pi.evalAlgHom_apply, Pi.single_apply] at this
    by_contra hne; simp [ite_eq_right (Ne.symm hne)] at this
  have hcard : Nat.card (R →ₐ[k] k) = Fintype.card ι := by
    rw [Nat.card_congr (AlgEquiv.arrowCongr f AlgEquiv.refl),
      ← Nat.card_eq_fintype_card (α := ι),
      Nat.card_eq_of_bijective _ heval]
  rw [hrk, hcard]

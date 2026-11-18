import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_Module_Invertible_of_projective_of_forall_finrank_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_Invertible_of_localization_maximal.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_Invertible_of_localization_maximal

set_option autoImplicit false

open scoped TensorProduct

namespace P2mKcLocalInvertible

/--
@isnad1 id=eq.0h2v.s5.e43bc62d8e65 from=translated src=- shape=ac87a97b vocab=86ff3db6
-/
theorem finrank_eq_one_of_invertible (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V] [Module.Invertible K V] :
    Module.finrank K V = 1 :=
  Module.finrank_eq_of_rank_eq (Module.Invertible.rank_eq_one K V)

/--
@isnad1 id=invertib.1h2v.s7.62d31110a0d4 from=translated src=- shape=64267fb0 vocab=cfcdb271
-/
theorem main {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    (H : ∀ (P : Ideal R) [P.IsMaximal], Module.Invertible (Localization.AtPrime P) (LocalizedModule P.primeCompl M)) :
    Module.Invertible R M := by
  haveI : Module.Projective R M :=
    Module.projective_of_localization_maximal (fun I hI => by haveI := hI; haveI := H I; infer_instance)
  apply Module.Invertible.of_projective_of_forall_finrank_eq_one (A := R) M
  intro K _ _

  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal (RingHom.ker (algebraMap R K)) (RingHom.ker_ne_top _)

  have hunit : ∀ s : 𝔪.primeCompl, IsUnit (algebraMap R K s) := by
    intro s
    apply isUnit_iff_ne_zero.mpr
    intro h0
    exact s.2 (hle ((RingHom.mem_ker).mpr h0))
  letI : Algebra (Localization.AtPrime 𝔪) K := (IsLocalization.lift (M := 𝔪.primeCompl) hunit).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime 𝔪) K :=
    IsScalarTower.of_algebraMap_eq fun r => (IsLocalization.lift_eq (M := 𝔪.primeCompl) hunit r).symm
  haveI := H 𝔪
  haveI : Module.Invertible (Localization.AtPrime 𝔪) (Localization.AtPrime 𝔪 ⊗[R] M) :=
    Module.Invertible.congr (LocalizedModule.equivTensorProduct 𝔪.primeCompl M)
  haveI : Module.Invertible K (K ⊗[R] M) :=
    Module.Invertible.congr (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime 𝔪) K K M)
  exact finrank_eq_one_of_invertible K (K ⊗[R] M)

end P2mKcLocalInvertible

/--
@isnad1 id=invertib.1h2v.s7.62d31110a0d4 from=translated src=- shape=64267fb0 vocab=cfcdb271
-/
theorem solution
    {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    (H : ∀ (P : Ideal R) [P.IsMaximal], Module.Invertible (Localization.AtPrime P) (LocalizedModule P.primeCompl M)) :
    Module.Invertible R M :=
  P2mKcLocalInvertible.main H

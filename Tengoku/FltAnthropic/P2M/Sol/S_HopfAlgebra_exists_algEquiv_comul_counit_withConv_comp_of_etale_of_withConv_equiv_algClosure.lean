import Tengoku
import Tengoku.Seed.RingTheory.Etale.Field
import Tengoku.Seed.RingTheory.Bialgebra.Convolution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_exists_algEquiv_comul_counit_withConv_comp_of_etale_of_withConv_equiv_algClosure.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_exists_algEquiv_comul_counit_withConv_comp_of_etale_of_withConv_equiv_algClosure

set_option autoImplicit false

open scoped TensorProduct

namespace EtalePointsDescent

section Separation

universe u

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]

end Separation

section Points

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
variable {A : Type*} [CommRing A] [Algebra K A]

/--
@isnad1 id=le.0h3v.s7.5f54b71bae4b from=translated src=- shape=ed35a4a3 vocab=a70dcad0
-/
theorem card_algHom_le_finrank [Module.Finite K A] [Fintype (A →ₐ[K] Ω)] :
    Fintype.card (A →ₐ[K] Ω) ≤ Module.finrank K A := by
  have h := (linearIndependent_toLinearMap K A Ω).fintype_card_le_finrank
  rwa [Module.finrank_linearMap_self] at h

variable [IsAlgClosed Ω]

end Points

section Descent

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [IsGalois K Ω]
variable {A : Type*} [CommRing A] [Algebra K A] [Algebra.Etale K A]

end Descent

section Iso

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [IsGalois K Ω]
variable {A : Type*} [CommRing A] [Algebra K A] [Algebra.Etale K A]
variable {B : Type*} [CommRing B] [Algebra K B] [Algebra.Etale K B]

end Iso

section Additive

variable {K : Type*} [CommRing K] {Ω : Type*} [CommRing Ω] [Algebra K Ω]
variable {A : Type*} [CommRing A] [HopfAlgebra K A] {M : Type*} [AddCommGroup M]

end Additive

section Conv

variable {K : Type*} [CommRing K] {Ω : Type*} [CommRing Ω] [Algebra K Ω]
variable {A : Type*} [CommRing A] [HopfAlgebra K A]
variable {B : Type*} [CommRing B] [HopfAlgebra K B]

end Conv

section Main

variable (K : Type*) [Field K] (Ω : Type*) [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]
    {M : Type*} [AddCommGroup M] [DistribMulAction (Ω ≃ₐ[K] Ω) M]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.Etale K A]
    (eA : WithConv (A →ₐ[K] Ω) ≃ M)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : Ω ≃ₐ[K] Ω) (f g : WithConv (A →ₐ[K] Ω)),
      (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f))
    (B : Type*) [CommRing B] [HopfAlgebra K B] [Algebra.Etale K B]
    (eB : WithConv (B →ₐ[K] Ω) ≃ M)
    (heB_add : ∀ f g, eB (f * g) = eB f + eB g)
    (heB_act : ∀ (σ : Ω ≃ₐ[K] Ω) (f g : WithConv (B →ₐ[K] Ω)),
      (∀ b : B, g b = σ (f b)) → eB g = σ • (eB f))

end Main

end EtalePointsDescent
open scoped _root_.P2MW.S_HopfAlgebra_exists_algEquiv_comul_counit_withConv_comp_of_etale_of_withConv_equiv_algClosure.EtalePointsDescent

import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_CompletionBridge
import Tengoku.FltAnthropic.Theorems.Thm_HopfAlgebra_bijective_withConv_algHomComp_of_finite_of_isAlgClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_exists_withConv_equiv_padic_of_withConv_equiv_algebraicClosure.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_exists_withConv_equiv_padic_of_withConv_equiv_algebraicClosure

set_option autoImplicit false

theorem solution
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A] (hAfin : Module.Finite ℚ A)
    {N : Type} [AddCommGroup N] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (eA : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ) ≃ N)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ)),
      (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f)) :
    ∃ eAp : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p]) ≃ N,
      (∀ f g, eAp (f * g) = eAp f + eAp g) ∧
      ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p])),
        (∀ a : A, g a = σ (f a)) → eAp g = (localGaloisToGlobal p σ) • (eAp f) := by
  classical

  let ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p] := (padicEmbedding p).toRingHom.toRatAlgHom
  have hι : ∀ x, ι x = padicEmbedding p x := fun _ => rfl
  have hιinj : Function.Injective ι := fun x y h => (padicEmbedding p).toRingHom.injective h

  obtain ⟨hθbij, hθmul⟩ :=
    HopfAlgebra.bijective_withConv_algHomComp_of_finite_of_isAlgClosed
      ℚ (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[p]) ι A hAfin
  let θ : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ) ≃ WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p]) :=
    Equiv.ofBijective _ hθbij
  have hθmul' : ∀ f g, θ (f * g) = θ f * θ g := hθmul
  have hθsymm : ∀ (g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p])) (a : A),
      ι ((θ.symm g).ofConv a) = g.ofConv a := by
    intro g a
    have := congrArg (fun φ : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p]) => φ.ofConv a)
      (θ.apply_symm_apply g)
    simpa only [θ, Equiv.ofBijective_apply, AlgHom.comp_apply, WithConv.ofConv_toConv] using this
  refine ⟨θ.symm.trans eA, fun f g => ?_, fun σ f g hfg => ?_⟩
  ·
    show eA (θ.symm (f * g)) = eA (θ.symm f) + eA (θ.symm g)
    have hs : θ.symm (f * g) = θ.symm f * θ.symm g := by
      apply θ.injective
      rw [θ.apply_symm_apply, hθmul', θ.apply_symm_apply, θ.apply_symm_apply]
    rw [hs, heA_add]
  ·
    show eA (θ.symm g) = (localGaloisToGlobal p σ) • eA (θ.symm f)
    refine heA_act (localGaloisToGlobal p σ) (θ.symm f) (θ.symm g) fun a => hιinj ?_
    calc ι ((θ.symm g).ofConv a) = g.ofConv a := hθsymm g a
      _ = σ (f.ofConv a) := hfg a
      _ = σ (ι ((θ.symm f).ofConv a)) := congrArg (fun y => σ y) (hθsymm f a).symm
      _ = ι (localGaloisToGlobal p σ ((θ.symm f).ofConv a)) :=
          (padicEmbedding_localGaloisToGlobal (q := p) σ _).symm
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)

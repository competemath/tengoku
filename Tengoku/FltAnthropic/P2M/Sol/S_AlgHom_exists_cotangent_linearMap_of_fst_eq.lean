import Tengoku.Seed.RingTheory.Ideal.Cotangent
import Tengoku.Seed.Algebra.TrivSqZeroExt.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgHom_exists_cotangent_linearMap_of_fst_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgHom_exists_cotangent_linearMap_of_fst_eq

universe u v x

/--
@isnad1 id=ex.1h5v.s11.29afa1e5dffb from=translated src=- shape=1bd9c6ae vocab=93e0bf82
-/
theorem solution
    {𝒪 : Type u} [CommRing 𝒪] {R : Type v} [CommRing R] [Algebra 𝒪 R] (πR : R →ₐ[𝒪] 𝒪)
    {N : Type x} [AddCommGroup N] [Module 𝒪 N] [Module 𝒪ᵐᵒᵖ N] [IsCentralScalar 𝒪 N]
    (ψ : R →ₐ[𝒪] TrivSqZeroExt 𝒪 N) (hψ : ∀ r : R, (ψ r).fst = πR r) :
    ∃ f : (RingHom.ker πR).Cotangent →ₗ[𝒪] N,
      ∀ a : RingHom.ker πR, (ψ (a : R)).snd = f ((RingHom.ker πR).toCotangent a) := by

  let g : RingHom.ker πR →ₗ[𝒪] N :=
    { toFun := fun a => (ψ (a : R)).snd
      map_add' := fun a b => by
        simp only [Submodule.coe_add, map_add, TrivSqZeroExt.snd_add]
      map_smul' := fun c a => by
        simp only [Submodule.coe_smul_of_tower, map_smul, TrivSqZeroExt.snd_smul, RingHom.id_apply] }

  have hg : ∀ x y : RingHom.ker πR, g (x * y) = 0 := fun x y => by
    show (ψ ((x * y : RingHom.ker πR) : R)).snd = 0
    have hxy : ((x * y : RingHom.ker πR) : R) = (x : R) * (y : R) := rfl
    rw [hxy, map_mul, TrivSqZeroExt.snd_mul, hψ, hψ, RingHom.mem_ker.mp x.2, RingHom.mem_ker.mp y.2,
      MulOpposite.op_zero, zero_smul, zero_smul, add_zero]
  exact ⟨Ideal.Cotangent.lift g hg, fun a => (Ideal.Cotangent.lift_toCotangent g hg a).symm⟩

import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_FaithfullyFlat_exists_ringHom_isAlgClosed_comp_algebraMap_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_FaithfullyFlat_exists_ringHom_isAlgClosed_comp_algebraMap_eq

set_option autoImplicit false

universe u

open scoped TensorProduct

/--
@isnad1 id=ex.0h4v.s8.4c6d1ef282b3 from=translated src=- shape=945fb18d vocab=6f21852e
-/
theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (k : Type u) [Field k] (sk : S →+* k) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (j : k →+* K) (sK : S' →+* K),
      sK.comp (algebraMap S S') = j.comp sk := by
  classical
  letI : Algebra S k := sk.toAlgebra

  let R : Type u := k ⊗[S] S'
  haveI : Nontrivial R := Module.FaithfullyFlat.rTensor_nontrivial S S' k
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  let K : Type u := AlgebraicClosure (R ⧸ m)
  let π : R →+* K := (algebraMap (R ⧸ m) K).comp (Ideal.Quotient.mk m)
  refine ⟨K, inferInstance, inferInstance, π.comp (algebraMap k R),
    π.comp (Algebra.TensorProduct.includeRight : S' →ₐ[S] R).toRingHom, ?_⟩
  ext s
  change π (Algebra.TensorProduct.includeRight (R := S) (A := k) (B := S') (algebraMap S S' s)) =
    π (algebraMap k R (sk s))
  congr 1
  rw [AlgHom.commutes]
  change algebraMap S R s = algebraMap k R (algebraMap S k s)
  exact (IsScalarTower.algebraMap_apply S k R s)

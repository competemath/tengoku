import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_finrank_baseChange_eq_one_of_rankAtStalk_eq_one.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_finrank_baseChange_eq_one_of_rankAtStalk_eq_one

universe u

open TensorProduct

set_option autoImplicit false

/--
@isnad1 id=eq.1h3v.s7.fba7e3fa272d from=translated src=- shape=ff8d18c4 vocab=0ddfffe0
-/
theorem solution
    {R : Type u} [CommRing R] (P : Type u) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Flat R P]
    (h : ∀ 𝔭, Module.rankAtStalk (R := R) P 𝔭 = 1)
    (K : Type u) [Field K] [Algebra R K] :
    Module.finrank K (K ⊗[R] P) = 1 := by
  have hq : Module.rankAtStalk (R := K) (K ⊗[R] P) ⟨⊥, Ideal.isPrime_bot⟩ = 1 := by
    rw [Module.rankAtStalk_baseChange]; exact h _
  rw [Module.rankAtStalk_eq_finrank_tensorProduct] at hq
  haveI : Nontrivial (Localization.AtPrime (⊥ : Ideal K)) := by infer_instance
  rwa [Module.finrank_baseChange] at hq

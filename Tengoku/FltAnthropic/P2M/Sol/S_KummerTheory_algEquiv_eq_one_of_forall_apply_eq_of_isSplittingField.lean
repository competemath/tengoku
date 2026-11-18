import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_KummerTheory_algEquiv_eq_one_of_forall_apply_eq_of_isSplittingField.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_KummerTheory_algEquiv_eq_one_of_forall_apply_eq_of_isSplittingField

set_option autoImplicit false

theorem solution (K L : Type*) [Field K] [Field L]
    [Algebra K L] {n : ℕ} (S : Finset Kˣ)
    [Polynomial.IsSplittingField K L (∏ u ∈ S, (Polynomial.X ^ n - Polynomial.C ((u : Kˣ) : K)))]
    (σ : L ≃ₐ[K] L) (hσ : ∀ α : L, ∀ u ∈ S, α ^ n = algebraMap K L (u : K) → σ α = α) : σ = 1 := by
  classical
  set f : Polynomial K := ∏ u ∈ S, (Polynomial.X ^ n - Polynomial.C ((u : Kˣ) : K)) with hf
  have hadj := Polynomial.IsSplittingField.adjoin_rootSet L f
  have key : (σ : L →ₐ[K] L) = AlgHom.id K L := by
    apply AlgHom.ext_of_adjoin_eq_top hadj
    intro α hα
    rw [Polynomial.mem_rootSet] at hα
    obtain ⟨-, hα⟩ := hα
    rw [hf, map_prod, Finset.prod_eq_zero_iff] at hα
    obtain ⟨u, hu, hαu⟩ := hα
    have hαn : α ^ n = algebraMap K L (u : K) := by
      rw [← sub_eq_zero]
      simpa using hαu
    change σ α = α
    exact hσ α u hu hαn
  ext x
  exact DFunLike.congr_fun key x

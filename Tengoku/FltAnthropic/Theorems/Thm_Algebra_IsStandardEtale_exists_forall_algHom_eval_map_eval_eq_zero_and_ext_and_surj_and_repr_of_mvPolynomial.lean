import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_IsStandardEtale_exists_forall_algHom_eval_map_eval_eq_zero_and_ext_and_surj_and_repr_of_mvPolynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_IsStandardEtale_exists_forall_algHom_eval_map_eval_eq_zero_and_ext_and_surj_and_repr_of_mvPolynomial.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Polynomial

/--
@isnad1 id=ex.0h3v.s12.e56a74cf31ca from=translated src=- shape=79c0040a vocab=001d58e2
-/
theorem Algebra.IsStandardEtale.exists_forall_algHom_eval_map_eval_eq_zero_and_ext_and_surj_and_repr_of_mvPolynomial
    (k : Type) [Field k] {n : ℕ} (A : Type) [CommRing A] [Algebra k A] [Algebra (MvPolynomial (Fin n) k) A]
    [IsScalarTower k (MvPolynomial (Fin n) k) A] [Algebra.IsStandardEtale (MvPolynomial (Fin n) k) A] :
    ∃ (x : A) (F G : Polynomial (MvPolynomial (Fin n) k)),
      (∀ τ : A →ₐ[k] k,
        (F.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)))).eval (τ x) = 0 ∧
        (G.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)))).eval (τ x) ≠ 0 ∧
        ((Polynomial.derivative F).map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)))).eval (τ x) ≠ 0) ∧
      (∀ τ τ' : A →ₐ[k] k,
        (∀ i : Fin n, τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)) =
          τ' (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i))) → τ x = τ' x → τ = τ') ∧
      (∀ (z : Fin n → k) (w : k), (F.map (MvPolynomial.eval z)).eval w = 0 → (G.map (MvPolynomial.eval z)).eval w ≠ 0 →
        ∃ τ : A →ₐ[k] k, (∀ i : Fin n, τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)) = z i) ∧ τ x = w) ∧
      (∀ s : A, ∃ (h : Polynomial (MvPolynomial (Fin n) k)) (N : ℕ), ∀ τ : A →ₐ[k] k,
        τ s * ((G.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)))).eval (τ x)) ^ N =
          (h.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)))).eval (τ x)) := by exact @_root_.P2MW.S_Algebra_IsStandardEtale_exists_forall_algHom_eval_map_eval_eq_zero_and_ext_and_surj_and_repr_of_mvPolynomial.solution k _ n A _ _ _ _ _

import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.P2M.Sol.S_GaloisRep_exists_finiteFlat_of_subalgebra_pi_algebraicClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_GaloisRep_exists_finiteFlat_of_subalgebra_pi_algebraicClosure.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=ex.6h3v.s14.b669505f7c23 from=translated src=- shape=6d13abbe vocab=fb3605ab
-/
theorem GaloisRep.exists_finiteFlat_of_subalgebra_pi_algebraicClosure (p : ℕ) (hp : p.Prime)
    {X : Type} [AddCommGroup X] [Finite X]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) X]
    (B : Subalgebra (GaloisRep.ratLocalizedAt p) (X → AlgebraicClosure ℚ))
    (hfin : (Subalgebra.toSubmodule B).FG)
    (hequiv : ∀ F ∈ B, ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : X),
      F (σ • x) = σ (F x))
    (hcomul : ∀ F ∈ B, ∃ (n : ℕ) (F₁ F₂ : Fin n → X → AlgebraicClosure ℚ),
      (∀ i, F₁ i ∈ B) ∧ (∀ i, F₂ i ∈ B) ∧ ∀ x y : X, F (x + y) = ∑ i, F₁ i x * F₂ i y)
    (hneg : ∀ F ∈ B, (fun x => F (-x)) ∈ B)
    (hsep : ∀ x y : X, (∀ F ∈ B, F x = F y) → x = y) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧ Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ X,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ x : H, g x = σ (f x)) → e g = σ • (e f) := by exact @_root_.P2MW.S_GaloisRep_exists_finiteFlat_of_subalgebra_pi_algebraicClosure.solution p hp X _ _ _ B hfin hequiv hcomul hneg hsep

import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomologyEigen
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeEis_exists_addMonoidHom_coeffH1_of_equivariant_addMonoidHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeEis_exists_addMonoidHom_coeffH1_of_equivariant_addMonoidHom.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open CongruenceSubgroup

/--
@isnad1 id=ex.3h11v.s17.55f7f68e9467 from=translated src=- shape=6ea9aa58 vocab=9ac0ee77
-/
theorem HeckeEis.exists_addMonoidHom_coeffH1_of_equivariant_addMonoidHom
    (N : ℕ) {R : Type} [CommRing R] {κ : Type} [CommRing κ] (f : R →+* κ)
    {Λ : Type} [AddCommGroup Λ] [Module R Λ] {Λ' : Type} [AddCommGroup Λ'] [Module κ Λ']
    (ρR : Representation R (Gamma0 N) Λ) (ρ' : Representation κ (Gamma0 N) Λ')
    (red : Λ →+ Λ') (hreds : ∀ (c : R) (x : Λ), red (c • x) = f c • red x)
    (hredρ : ∀ (g : Gamma0 N) (x : Λ), red (ρR g x) = ρ' g (red x))
    (a : ℕ → (Λ →ₗ[R] Λ)) (a' : ℕ → (Λ' →ₗ[κ] Λ')) (hreda : ∀ (ℓ : ℕ) (x : Λ), red (a ℓ x) = a' ℓ (red x)) :
    ∃ Φ : HeckeEis.coeffH1 ρR →+ HeckeEis.coeffH1 ρ',
      (∀ z : ↥(HeckeEis.coeffCocycles ρR), ∃ w : ↥(HeckeEis.coeffCocycles ρ'),
        (∀ g : Gamma0 N, (w : Gamma0 N → Λ') g = red ((z : Gamma0 N → Λ) g)) ∧
          Φ (HeckeEis.coeffH1Mk ρR z) = HeckeEis.coeffH1Mk ρ' w) ∧
      (∀ (c : R) (x : HeckeEis.coeffH1 ρR), Φ (c • x) = f c • Φ x) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ] (T : HeckeEis.coeffH1 ρR →ₗ[R] HeckeEis.coeffH1 ρR)
          (T' : HeckeEis.coeffH1 ρ' →ₗ[κ] HeckeEis.coeffH1 ρ'),
        HeckeEis.IsCoeffHeckeOnH1 N ℓ ρR (a ℓ) T → HeckeEis.IsCoeffHeckeOnH1 N ℓ ρ' (a' ℓ) T' →
          ∀ x : HeckeEis.coeffH1 ρR, Φ (T x) = T' (Φ x)) ∧
      ∀ ϖ : R, Function.Surjective red → (∀ x : Λ, red x = 0 ↔ ∃ y : Λ, x = ϖ • y) → (∀ x : Λ, ϖ • x = 0 → x = 0) →
        ∀ x : HeckeEis.coeffH1 ρR, Φ x = 0 ↔ ∃ y : HeckeEis.coeffH1 ρR, x = ϖ • y := by exact @_root_.P2MW.S_HeckeEis_exists_addMonoidHom_coeffH1_of_equivariant_addMonoidHom.solution N R _ κ _ f Λ _ _ Λ' _ _ ρR ρ' red hreds hredρ a a' hreda

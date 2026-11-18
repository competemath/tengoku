import Tengoku.Seed.Algebra.Module.LocalizedModule.Basic
import Tengoku.Seed.LinearAlgebra.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IharaLemma_resInj_of_reduction.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IharaLemma_resInj_of_reduction

set_option autoImplicit false

/--
@isnad1 id=ex.5h12v.s10.915fb06b151e from=translated src=- shape=dd9df179 vocab=825d759f
-/
theorem solution {R : Type*} [CommRing R] {V L Vk Lk : Type*}
    [AddCommGroup V] [Module R V] [AddCommGroup L] [Module R L]
    [AddCommGroup Vk] [Module R Vk] [AddCommGroup Lk] [Module R Lk]
    (ϖ : R) (f : V →ₗ[R] L) (redV : V →ₗ[R] Vk) (redL : L →ₗ[R] Lk)
    (fk : Vk →ₗ[R] Lk) (hsq : ∀ v, redL (f v) = fk (redV v))
    (hker : ∀ v, redV v = 0 → ∃ v₁, v = ϖ • v₁) (hϖ : ∀ x : L, redL (ϖ • x) = 0)
    (hfk : Function.Injective fk) :
    ∀ (v : V) (x : L), f v = ϖ • x → ∃ v₁ : V, v = ϖ • v₁ := by
  intro v x h
  apply hker
  apply hfk
  rw [← hsq, h, hϖ, map_zero]
